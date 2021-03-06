module CVars = Vars

open Util
open Context
open Rel.Declaration
open Names
open Term
open EConstr
open Entries
open Declarations
open Globnames
open Pp

open EConstants

type effect = global_reference option

exception MissingGlobal of effect * global_reference
exception MissingPrimitive of global_reference
exception MatchEliminationNotSupportedOnTranslation
exception BadFormingCatchInduction

type 'a global_translation =
| GlobGen of 'a
  (** Implementation generic over the type of exceptions *)
| GlobImp of 'a Refmap.t
  (** For every type of exceptions, a specialized implementation. *)

type translator = {
  refs : global_reference global_translation Cmap.t;
  inds : MutInd.t global_translation Mindmap.t;
  prefs : global_reference global_translation Cmap.t;
  pinds : MutInd.t global_translation Mindmap.t;
  wrefs : global_reference global_translation Cmap.t;
  winds : MutInd.t global_translation Mindmap.t;
  paramrefs : global_reference global_translation Mindmap.t;
  paraminds : MutInd.t global_translation Mindmap.t;
}

let empty_translator =
  let refss = [
      (param_cst, param_cst_e);
      (param_correct_cst, param_correct_cst_e);
      (tm_exception, tm_exception_e);
      (tm_raise, tm_raise_e)
    ]
  in
  let map acc (s,t) =
    Cmap.add s (GlobGen (ConstRef t)) acc
  in
  let refss = List.fold_left map Cmap.empty refss in
  let inds =
    Mindmap.add
      param_mod
      (GlobGen param_mod_e)
      (Mindmap.add tm_False (GlobGen tm_False_e) Mindmap.empty)
  in
  let prefs = Cmap.empty in
  let pinds = Mindmap.empty in
  {
    refs = refss;
    inds = inds;
    prefs = prefs;
    pinds = pinds;
    wrefs = Cmap.empty;
    winds = Mindmap.empty;
    paramrefs = Mindmap.empty;
    paraminds = Mindmap.empty;
  }

type context = {
  error : global_reference option;
  (** Whether the translation is relativized to a specific error type *)
  translator : translator;
  env_src : Environ.env;
  env_tgt : Environ.env;
}

let push_assum na (t, te) env = { env with
  env_src = EConstr.push_rel (LocalAssum (na, t)) env.env_src;
  env_tgt = EConstr.push_rel (LocalAssum (na, te)) env.env_tgt;
}

let push_def na (c, ce) (t, te) env = { env with
  env_src = EConstr.push_rel (LocalDef (na, c, t)) env.env_src;
  env_tgt = EConstr.push_rel (LocalDef (na, ce, te)) env.env_tgt;
}

let lift_rel_context n ctx =
  let fold k d accu =
    let d = Context.Rel.Declaration.map_constr (fun c -> Vars.liftn n k c) d in
    d :: accu
  in
  List.fold_right_i fold 1 ctx []

(** Handling of globals *)

let get_instance err = function
| GlobGen x -> true, x
| GlobImp m ->
  match err with
  | None -> raise Not_found (** No generic implementation *)
  | Some gr -> false, Refmap.find gr m

let instantiate_error err env sigma gen c_ = match err with
| None -> (sigma, c_)
| Some err ->
  if gen then
    let (sigma, err) = Evd.fresh_global env sigma err in
    (sigma, mkApp (c_, [| EConstr.of_constr err |]))
  else (sigma, c_)

let get_cst env cst =
  try get_instance env.error (Cmap.find cst env.translator.refs)
  with Not_found -> raise (MissingGlobal (env.error, ConstRef cst))

let get_ind env (ind, n) =
  try
    let gen, ind = get_instance env.error (Mindmap.find ind env.translator.inds) in
    gen, (ind, n)
  with Not_found -> raise (MissingGlobal (env.error, IndRef (ind, n)))

let apply_global env sigma gr =
  let gen, gr = match gr with
  | ConstructRef (ind, n) ->
    let gen, ind = get_ind env ind in
    gen, ConstructRef (ind, n)
  | IndRef ind ->
    let gen, ind = get_ind env ind in
    gen, IndRef ind
  | ConstRef cst -> get_cst env cst
  | VarRef _ -> CErrors.user_err (str "Variables not handled")
  in
  let (sigma, c) = Evd.fresh_global env.env_tgt sigma gr in
  let c = EConstr.of_constr c in
  if gen then
    let e = mkRel (Environ.nb_rel env.env_tgt) in
    (sigma, mkApp (c, [|e|]))
  else
    (sigma, c)

let fresh_global env sigma gr =
  try
    let (sigma, c) = Evd.fresh_global env.env_tgt sigma gr in
    (sigma, EConstr.of_constr c)
  with Not_found -> raise (MissingPrimitive gr)

(** Effect translation core *)

let element env sigma is_prop c =
  let (sigma, value) =
    if is_prop then
      (sigma, c)
    else
      let (sigma, el) = fresh_global env sigma el_e in
      let e = mkRel (Environ.nb_rel env.env_tgt) in
      (sigma, mkApp (el, [|e; c|]))
  in
  (sigma, value)

let translate_case_info env sigma ci mip =
  let gen, ci_ind = get_ind env ci.ci_ind in
  let nrealdecls = mip.mind_nrealdecls in
  let nrealargs = mip.mind_nrealargs in
  let ci_npar = if gen then 1 + ci.ci_npar else ci.ci_npar in
  let ci_cstr_ndecls = Array.append ci.ci_cstr_ndecls [|1 + nrealdecls|] in
  let ci_cstr_nargs = Array.append ci.ci_cstr_nargs [|1 + nrealargs|] in
  let tags =
    false :: (** additional exception argument *)
    Context.Rel.to_tags (List.firstn nrealdecls mip.mind_arity_ctxt)
  in
  let ci_pp_info = { ci.ci_pp_info with
    ind_tags = (not gen) :: ci.ci_pp_info.ind_tags;
    cstr_tags = Array.append ci.ci_pp_info.cstr_tags [|tags|];
  } in
  { ci_ind; ci_npar; ci_cstr_ndecls; ci_cstr_nargs; ci_pp_info; }

let translate_prop_case_info env sigma ci mip =
  let gen, ci_ind = get_ind env ci.ci_ind in
  let ci_npar = if gen then 1 + ci.ci_npar else ci.ci_npar in
  { ci with ci_ind;  ci_npar; }

let mk_default_ind env sigma (ind, u) =
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let (_, mip) = Inductive.lookup_mind_specif env.env_src ind in
  let err = Array.length mip.mind_consnames + 1 in
  let gen, ind = get_ind env ind in
  let (sigma, (ind, u)) = Evd.fresh_inductive_instance env.env_tgt sigma ind in
  let r = mkConstructU ((ind, err), EInstance.make u) in
  let r = if gen then mkApp (r, [|e|]) else r in
  (sigma, r)

let mk_default_primitive_record env sigma (ind, u) =
  let (modd, dir, lab) = (MutInd.repr3 (fst ind)) in
  let cst = Constant.make3 modd dir lab in
  let (gen, default) = get_cst env cst in
  let (sigma, r) = fresh_global env sigma default in
  (sigma, gen, EInstance.kind sigma (snd (destConst sigma r)), r)

let ind_in_prop mip =
  match mip.mind_arity with
  | RegularArity ar -> Sorts.is_prop ar.mind_sort
  | TemplateArity _ -> false

(* From Γ ⊢ M : A produce [M] s.t. ⟦Γ⟧ ⊢ [M] : ⟦A⟧. *)
let rec otranslate env sigma c = match EConstr.kind sigma c with
| Rel n ->
  (sigma, mkRel n)
| Sort s ->
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let is_prop = Sorts.is_prop (EConstr.ESorts.kind sigma s) in
  let sort_e = if is_prop then prop_e else type_e in
  let (sigma, t) = fresh_global env sigma sort_e in
  sigma, mkApp (t, [|e|])
| Cast (c, k, t) ->
  let (sigma, ce) = otranslate env sigma c in
  let (sigma, te) = otranslate_type env sigma t in
  let r = mkCast (ce, k, te) in
  (sigma, r)
| Prod (na, t, u) ->
  let (sigma,ty) = Typing.type_of env.env_src sigma c in
  let is_prop = isSort sigma ty && Sorts.is_prop (ESorts.kind sigma (destSort sigma ty)) in
  if is_prop then
    let (sigma, ty) = otranslate_type env sigma c in
    (sigma, ty)
  else
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let (sigma, p) = fresh_global env sigma prod_e in
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_assum na (t, te) env in
  let (sigma, ue) = otranslate env sigma u in
  let ue = mkLambda (na, te, ue) in
  let r = mkApp (p, [|e; te; ue|]) in
  (sigma, r)
| Lambda (na, t, u) ->
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_assum na (t, te) env in
  let (sigma, ue) = otranslate env sigma u in
  let r = mkLambda (na, te, ue) in
  (sigma, r)
| LetIn (na, c, t, u) ->
  let (sigma, ce) = otranslate env sigma c in
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_def na (c, ce) (t, te) env in
  let (sigma, ue) = otranslate env sigma u in
  let r = mkLetIn (na, ce, te, ue) in
  (sigma, r)
| App (t, args) when isInd sigma t ->
  otranslate_ind env sigma (destInd sigma t) args
| App (t, args) ->
  let (sigma, te) = otranslate env sigma t in
  let fold (sigma, argse) arg =
    let (sigma, arge) = otranslate env sigma arg in
    (sigma, arge :: argse)
  in
  let (sigma, argse) = Array.fold_left fold (sigma, []) args in
  let r = mkApp (te, Array.rev_of_list argse) in
  (sigma, r)
| Var id ->
  let (sigma, c) = apply_global env sigma (VarRef id) in
  (sigma, c)
| Const (p, _) ->
  let (sigma, c) = apply_global env sigma (ConstRef p) in
  (sigma, c)
| Ind (ind, u) ->
  otranslate_ind env sigma (ind, u) [||]
| Construct (c, _) ->
  let (sigma, c) = apply_global env sigma (ConstructRef c) in
  (sigma, c)
| Case (ci, r, c, p) ->
  let (_, mip) = Inductive.lookup_mind_specif env.env_src ci.ci_ind in
  let r_ctx, r_end = decompose_lam_assum sigma r in
  let p_env_src = EConstr.push_rel_context r_ctx env.env_src in
  let match_on_prop = ind_in_prop mip in
  let () =
    let module S = ESorts in
    if isSort sigma r_end then
      let sort = S.kind sigma (destSort sigma r_end) in
      ( if Sorts.is_prop sort && not match_on_prop then
          raise MatchEliminationNotSupportedOnTranslation )
    else
      let r_sort = Typing.e_sort_of p_env_src (ref sigma) r_end in
      if Sorts.is_prop r_sort && not match_on_prop then
        raise MatchEliminationNotSupportedOnTranslation
  in
  let ci_translator = if match_on_prop then translate_prop_case_info else translate_case_info in
  let cie = ci_translator env sigma ci mip in
  let (ctx, r) = EConstr.decompose_lam_assum sigma r in
  let (sigma, env', ctxe) = otranslate_context env sigma ctx in
  let (sigma, ce) = otranslate env sigma c in
  let map sigma p = otranslate env sigma p in
  let (sigma, pe) = Array.fold_left_map map sigma p in
  let nE = Environ.nb_rel env'.env_tgt in
  (** The default constructor has as arguments the indices of the block plus an error *)
  let default_ctx = LocalAssum (Name name_err, mkRel (nE - 1)) :: List.tl ctxe in
  let default_case =
    (** Transform [Ind{I} params indices] into [Cstr{Iᴱ} params indices] *)
    let (ind, args) = Termops.decompose_app_vect sigma (get_type (List.hd ctxe)) in
    let (ind, u) = destInd sigma ind in
    let err = Array.length mip.mind_consnames + 1 in
    let args = Array.map (fun c -> Vars.lift 1 c) args in
    mkApp (mkConstructU ((ind, err), u), Array.append args [|mkRel 1|])
  in
  let (sigma, re, default) = otranslate_type_and_err env' sigma r in
  let re = it_mkLambda_or_LetIn re ctxe in
  let default = Vars.subst1 default_case (Vars.liftn 1 2 default) in
  let default = mkApp (default, [|mkRel 1|]) in
  let default = it_mkLambda_or_LetIn default default_ctx in
  let pe = if match_on_prop then pe else Array.append pe [| default |] in
  (*let pe = Array.append pe [|default|] in*)
  let r = mkCase (cie, re, ce, pe) in
  (sigma, r)
| Fix (fi, recdef) ->
  let (sigma, recdefe) = otranslate_recdef env sigma recdef in
  let r = mkFix (fi, recdefe) in
  (sigma, r)
| CoFix (fi, recdef) ->
  let (sigma, recdefe) = otranslate_recdef env sigma recdef in
  let r = mkCoFix (fi, recdefe) in
  (sigma, r)
| Proj (p, c) ->
  let constant = Names.Projection.constant p in
  let unfolded = Names.Projection.unfolded p in
  let _, glob_constante = get_cst env constant in
  let constante = Globnames.destConstRef glob_constante in
  let proje = Names.Projection.make constante unfolded in
  let (sigma, ce) = otranslate env sigma c in
  (sigma, mkProj (proje, ce))
| Meta _ -> assert false
| Evar _ -> assert false

and otranslate_recdef env sigma (nas, tys, bodies) =
  let fold i (env, sigma, ans) na t =
    let t = Vars.lift i t in
    let (sigma, te) = otranslate_type env sigma t in
    let env = push_assum na (t, te) env in
    (env, sigma, te :: ans)
  in
  let (env, sigma, tyse) = Array.fold_left2_i fold (env, sigma, []) nas tys in
  let tyse = Array.rev_of_list tyse in
  let (sigma, bodiese) = Array.fold_left_map (fun sigma c -> otranslate env sigma c) sigma bodies in
  (sigma, (nas, tyse, bodiese))

(* Special handling of types not to clutter the translation.
   From Γ ⊢ A : Type produce ⟦A⟧ s.t. ⟦Γ⟧ ⊢ ⟦A⟧ : Type. *)
and otranslate_type env sigma t = match EConstr.kind sigma t with
| App (c, args) when isInd sigma c ->
  let (ind, _) = destInd sigma c in
  let fold sigma c = otranslate env sigma c in
  let (sigma, args) = Array.fold_left_map fold sigma args in
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  (sigma, mkApp (c, args))
| Ind (ind, _) ->
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  (sigma, c)
| Prod (na, t, u) ->
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_assum na (t, te) env in
  let (sigma, ue) = otranslate_type env sigma u in
  (sigma, mkProd (na, te, ue))
| _ ->
  let is_prop = Sorts.is_prop (Typing.e_sort_of env.env_src (ref sigma) t) in
  let (sigma, t_) = otranslate env sigma t in
  let (sigma, t_) = element env sigma is_prop t_ in
  (sigma, t_)

(* From Γ ⊢ A : Type produce
   - ⟦A⟧ s.t. ⟦Γ⟧ ⊢ ⟦A⟧ : Type
   - [A]ᴱ s.t. ⟦Γ⟧ ⊢ [A]ᴱ : E → ⟦A⟧ *)
and otranslate_type_and_err env sigma t = match EConstr.kind sigma t with
| App (c, args) when isInd sigma c ->
  let (ind, u) = destInd sigma c in
  let fold sigma c = otranslate env sigma c in
  let (sigma, args) = Array.fold_left_map fold sigma args in
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  let (sigma, ind_def) = mk_default_ind env sigma (ind, u) in
  let ind_def = mkApp (ind_def, args) in
  (sigma, mkApp (c, args), ind_def)
| Ind (ind, u) ->
  let (sigma, c) = apply_global env sigma (IndRef ind) in
  let (sigma, ind_def) = mk_default_ind env sigma (ind, u) in
  (sigma, c, ind_def)
| Prod (na, t, u) ->
  let (sigma, te) = otranslate_type env sigma t in
  let env = push_assum na (t, te) env in
  let (sigma, ue, def) = otranslate_type_and_err env sigma u in
  let def = mkApp (Vars.liftn 1 2 def, [| mkRel 2 |]) in
  let e = mkRel (Environ.nb_rel env.env_tgt - 1) in
  let prod_def = mkLambda (Name name_err, e, mkLambda (na, Vars.lift 1 te, def)) in
  (sigma, mkProd (na, te, ue), prod_def)
| _ ->
  let is_prop = Sorts.is_prop (Typing.e_sort_of env.env_src (ref sigma) t) in
  let (sigma, t_) = otranslate env sigma t in
  let (sigma, err) = fresh_global env sigma err_e in
  let e = mkRel (Environ.nb_rel env.env_tgt) in
  let t_def = mkApp (err, [|e; t_|]) in
  let (sigma, t_) = element env sigma is_prop t_ in
  (sigma, t_, t_def)

(** Special handling of potentially partially applied inductive types not to
    clutter the translation *)
and otranslate_ind env sigma (ind, u) args =
  let (mib, mip) = Inductive.lookup_mind_specif env.env_src ind in
  let is_prop = ind_in_prop mip in
  let fold sigma c = otranslate env sigma c in
  let (sigma, args) = Array.fold_left_map fold sigma args in
  if is_prop then
    let (sigma, c) = apply_global env sigma (IndRef ind) in
    (sigma, if Array.length args == 0 then c else mkApp (c, args))
  else if Inductive.is_primitive_record (mib, mip) then
    (** Primitive default constructor
        This is wrong *)
    let e_var = mkRel (Environ.nb_rel env.env_tgt) in
    let (sigma, c) = apply_global env sigma (IndRef ind) in
    let (sigma, gen, _, def) = mk_default_primitive_record env sigma (ind, u) in
    let (sigma, typeval) = fresh_global env sigma typeval_e in
    let r = mkApp (typeval, [| e_var; mkApp (c, args); mkApp (def, args) |]) in
    let () = assert false in
    (sigma, r)
  else if Int.equal (Array.length args) (mib.mind_nparams + mip.mind_nrealargs) then
    (** Fully applied *)
    let e = mkRel (Environ.nb_rel env.env_tgt) in
    let (sigma, c) = apply_global env sigma (IndRef ind) in
    let (sigma, typeval) = fresh_global env sigma typeval_e in
    let (sigma, def) = mk_default_ind env sigma (ind, u) in
    let r = mkApp (typeval, [| e; mkApp (c, args); mkApp (def, args) |]) in
    (sigma, r)
  else
    (** Partially applied, we need to eta-expand it. *)
    let gen, ind = get_ind env ind in
    let (_, mip) = Inductive.lookup_mind_specif env.env_src ind in
    let (sigma, (ind, u)) = Evd.fresh_inductive_instance env.env_tgt sigma ind in
    let subst c = CVars.subst_instance_constr u c in
    let nctx = List.length mip.mind_arity_ctxt in
    let map d =
      let d = Rel.Declaration.map_constr subst d in
      of_rel_decl d
    in
    let ctx = List.map map mip.mind_arity_ctxt in
    let (sigma, typeval) = fresh_global env sigma typeval_e in
    let make_arg (n, accu) = function
    | LocalAssum _ -> (succ n, mkRel n :: accu)
    | LocalDef _ -> (succ n, accu)
    in
    let (_, arity) = List.fold_left make_arg (1, []) mip.mind_arity_ctxt in
    let u = EInstance.make u in
    let typ = applist (mkIndU (ind, u), arity) in
    let def_c = (ind, Array.length mip.mind_consnames) in
    let def = applist (mkConstructU (def_c, u), arity) in
    let r = mkApp (typeval, [| mkRel nctx; typ; def |]) in
    let r = it_mkLambda_or_LetIn r ctx in
    let r = if gen then mkApp (r, [| mkRel (Environ.nb_rel env.env_tgt) |]) else r in
    let r = mkApp (r, args) in
    (sigma, r)

(* From ⊢ Γ produce ⊢ ⟦Γ⟧ *)
and otranslate_context env sigma = function
| [] -> sigma, env, []
| LocalAssum (na, t) :: params ->
  let (sigma, env, ctx) = otranslate_context env sigma params in
  let (sigma, te) = otranslate_type env sigma t in
  (sigma, push_assum na (t, te) env, LocalAssum (na, te) :: ctx)
| LocalDef (na, b, t) :: params ->
  let (sigma, env, ctx) = otranslate_context env sigma params in
  let (sigma, te) = otranslate_type env sigma t in
  let (sigma, be) = otranslate env sigma b in
  (sigma, push_def na (b, be) (t, te) env, LocalDef (na, be, te) :: ctx)

let make_error err env sigma = match err with
| None ->
  let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env sigma InType in
  let d = LocalAssum (Name name_errtype, Constr.mkSort s) in
  (sigma, d)
| Some gr ->
  let (sigma, s) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env sigma InType in
  let (sigma, c) = Evd.fresh_global env sigma gr in
  let d = LocalDef (Name name_errtype, c, Constr.mkSort s) in
  (sigma, d)

let make_context error translator env sigma =
  let (sigma, decl) = make_error error env sigma in
  let env_tgt = Environ.push_rel decl env in
  let env = {
    error;
    translator;
    env_src = env;
    env_tgt;
  } in
  (sigma, env)

let get_exception env =
  let rels = EConstr.rel_context env.env_tgt in
  List.last rels

let translate err translator env0 sigma c =
  let (sigma, env) = make_context err translator env0 sigma in
  let (sigma, c_) = otranslate env sigma c in
  let decl = get_exception env in
  let c_ = mkLambda_or_LetIn decl c_ in
  let (sigma, _) = Typing.type_of env.env_src sigma c_ in
  (sigma, c_)

let translate_type err translator env sigma c =
  let (sigma, env) = make_context err translator env sigma in
  let (sigma, c_) = otranslate_type env sigma c in
  let decl = get_exception env in
  let c_ = mkProd_or_LetIn decl c_ in
  let (sigma, _) = Typing.type_of env.env_src sigma c_ in
  (sigma, c_)

let to_local_entry = function
| LocalAssum (Name id, t) -> (id, Entries.LocalAssumEntry t)
| LocalDef (Name id, b, t) -> (id, Entries.LocalDefEntry b)
| _ -> assert false

let dummy_kn id =
  KerName.make (MPfile DirPath.empty) DirPath.empty (Label.of_id id)

let trans_name translation_function = function
  | Anonymous as anon -> anon
  | Name id -> Name (translation_function id)

let name_projection_translate sigma translation_function record_builder =
  let rec aux sigma record_builder =
    match EConstr.kind sigma record_builder with
    | Prod (na, ty, bd) ->
       let trans_body = aux sigma bd in
       mkProd (trans_name translation_function na, ty, trans_body)
    | _ -> record_builder
  in
  aux sigma record_builder

(** Locally extend a translator to fake an inductive definition *)
let extend_inductive env mind0 mind =
  let open Univ in
  let univs = match mind0.mind_universes with
  | Monomorphic_ind _ -> Monomorphic_ind ContextSet.empty
  | Polymorphic_ind _ -> Polymorphic_ind AUContext.empty
  | Cumulative_ind _ -> Polymorphic_ind AUContext.empty (** FIXME *)
  in
  (** Dummy inductive. It is only used for its universe context, that we set to
      be empty. *)
  let mbi = { mind0 with mind_universes = univs } in
  let ind_name = dummy_kn (EUtil.translate_inductive_name mind0.mind_packets.(0).mind_typename) in
  let mind = MutInd.make1 ind_name in
  let env_tgt = Environ.add_mind mind mbi env.env_tgt in
  let ext = match env.error with
  | None -> GlobGen mind
  | Some exn -> GlobImp (Refmap.singleton exn mind)
  in
  let translator = { env.translator with inds = Mindmap.add mind ext env.translator.inds } in
  mind, { env with translator; env_tgt }

let abstract_mind sigma mind n k c =
  let rec aux k c = match EConstr.kind sigma c with
  | Rel m ->
    if m <= k then c
    else mkRel (k + m)
  | Ind ((ind, m), _) when MutInd.equal mind ind ->
    mkRel (k + n - m)
  | _ ->
    map_with_binders sigma succ aux k c
  in
  aux k c

let translate_constructors env sigma mind0 mind ind0 ind =
  let mutind, env = extend_inductive env mind0 mind in
  let nblock = Array.length mind0.mind_packets in
  let mk_ind n = mkInd (mutind, nblock - (n + 1)) in
  let subst0 = List.init nblock mk_ind in
  let map sigma t =
    (** A bit of term mangling: indices in the context referring to the
        inductive types we're building do not have the right type. *)
    let t = EConstr.of_constr t in
    let t = Vars.substnl subst0 (Environ.nb_rel env.env_src) t in
    let (sigma, te) = otranslate_type env sigma t in
    let te = abstract_mind sigma mutind nblock (Environ.nb_rel env.env_tgt) te in
    (sigma, te)
  in
  List.fold_left_map map sigma ind.mind_entry_lc

let translate_inductive_body env sigma mind0 mind n ind0 ind =
  let typename = EUtil.translate_inductive_name ind.mind_entry_typename in
  let is_prop = match ind0.mind_arity with
    | RegularArity ar -> Sorts.is_prop ar.mind_sort
    | TemplateArity _ -> false
  in
  let constructors = List.map EUtil.translate_name ind.mind_entry_consnames in
  let nindices = List.length ind0.mind_arity_ctxt - List.length mind0.mind_params_ctxt in
  let arity_ctx, _ = List.chop nindices ind0.mind_arity_ctxt in
  let (sigma, arity_env, arity_ctx') = otranslate_context env sigma (List.map EConstr.of_rel_decl arity_ctx) in
  let inSort = if is_prop then InProp else InType in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.env_tgt sigma inSort in
  let arity = it_mkProd_or_LetIn (mkSort sort) arity_ctx' in
  let (sigma, _) = Typing.type_of env.env_tgt sigma arity in
  let (sigma, lc) = translate_constructors env sigma mind0 mind ind0 ind in
  let lc = List.map (fun c -> EConstr.to_constr sigma c) lc in
  let fail_name = EUtil.translate_failure ind.mind_entry_typename in
  let fail_arg (n, accu) = function
  | LocalAssum _ -> (succ n, mkRel n :: accu)
  | LocalDef _ -> (succ n, accu)
  in
  (** FIXME, probably wrong indices for mutual inductive blocks *)
  let (arity, fail_name_list, fail_case_list) =
    let arity = EConstr.to_constr sigma arity in
    if not is_prop then
      let (_, fail_args) = List.fold_left fail_arg (2, []) (Environ.rel_context arity_env.env_tgt) in
      let n = 1 + (mind0.mind_ntypes - n) + Environ.nb_rel arity_env.env_tgt in
      let fail_case = applist (mkRel n, fail_args) in
      let fail_ctx = LocalAssum (Anonymous, mkRel (1 + List.length ind0.mind_arity_ctxt)) :: arity_ctx' in
      let fail_case = it_mkProd_or_LetIn fail_case fail_ctx in
      (arity, [fail_name], [EConstr.to_constr sigma fail_case])
    else
      (arity, [], [])
  in
  let ind = { ind with
    mind_entry_typename = typename;
    mind_entry_arity = arity;
    mind_entry_consnames = constructors @ fail_name_list;
    mind_entry_lc = lc @ fail_case_list;
  } in
  (sigma, ind)

let translate_primitive_record env sigma mind_d mind_e =
  let _, env = extend_inductive env mind_d mind_e in
  let ind_e = List.hd mind_e.mind_entry_inds in
  let ind_d = mind_d.mind_packets.(0) in
  let ind_name = EUtil.translate_inductive_name ind_e.mind_entry_typename in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.env_tgt sigma InType in
  let ar = mkSort sort in
  let cons_name = EUtil.translate_name (List.hd ind_e.mind_entry_consnames) in
  let (sigma, constr_type) = translate_constructors env sigma mind_d mind_e ind_d ind_e in
  let constr_type = List.hd constr_type in
  let constr_type_name = name_projection_translate sigma EUtil.translate_name constr_type in

  let ind = { ind_e with
              mind_entry_typename = ind_name;
              mind_entry_arity = EConstr.to_constr sigma ar;
              mind_entry_consnames = [cons_name];
              mind_entry_lc = [EConstr.to_constr sigma constr_type_name]
            }
  in
  (sigma, ind)

let translate_inductive err translator env _ mind0 (mind : Entries.mutual_inductive_entry) =
  let sigma = Evd.from_env env in
  let (sigma, env) = make_context err translator env sigma in
  let (sigma, env, _) = otranslate_context env sigma (List.map EConstr.of_rel_decl mind0.mind_params_ctxt) in
  let (sigma, inds) =
    if Inductive.is_primitive_record (mind0,mind0.mind_packets.(0)) then
       let (sigma, pind) = translate_primitive_record env sigma mind0 mind in
       (sigma, [pind])
    else
      let inds = List.combine (Array.to_list mind0.mind_packets) mind.mind_entry_inds in
      let inds = List.mapi (fun i (ind, ind0) -> (i, ind, ind0)) inds in
      let map sigma (n, ind0, ind) = translate_inductive_body env sigma mind0 mind n ind0 ind in
      let sigma, inds = List.fold_left_map map sigma inds in
      (sigma, inds)
  in
  let sigma, inds, params = EUtil.retype_inductive env.env_tgt sigma (EConstr.rel_context env.env_tgt) inds in
  let params = List.map to_local_entry params in
  let uctx = UState.context (Evd.evar_universe_context sigma) in
  let univs = match mind.mind_entry_universes with
  | Monomorphic_ind_entry _ -> Monomorphic_ind_entry (Univ.ContextSet.of_context uctx)
  | Polymorphic_ind_entry _ -> Polymorphic_ind_entry uctx
  | Cumulative_ind_entry _ -> Polymorphic_ind_entry uctx (** FIXME *)
  in
  let mind = { mind with
    mind_entry_inds = inds;
    mind_entry_params = params;
    mind_entry_universes = univs;
  } in
  mind

(** Generate parametric inductive for a given inductive *)

let param_lift param_offset c =
  let n = List.length param_offset in
  let fold accum i =
    let current = accum + i in (current, mkRel current)
  in
  let total,offsets = List.fold_left_map fold 0 param_offset in
  Vars.substl offsets (Vars.liftn n (n + 1) c)

let param_top_decls env is_ind_prop =
  List.firstn (if is_ind_prop then 2 else 1) (EConstr.rel_context env.env_tgt)


let param_env_accum_up_to param_env n =
     List.fold_left (fun a acc -> a + acc) 0 (List.firstn n param_env)

let rec otranslate_param env param_env sigma (ind, ind_e) c = match EConstr.kind sigma c with
| Rel n ->
   let m = param_env_accum_up_to param_env n  in
   (sigma, mkRel m)
| Sort _ | Prod _ ->

   let (sigma, c_) = otranslate_param env param_env sigma (ind, ind_e) c in
   let c_ = param_lift param_env c_ in
   let (sigma, w) = otranslate_param_type env param_env sigma (ind, ind_e) c in
   let w = mkLambda (Anonymous, c_, w) in
   (sigma, w)
| Lambda (na, t, u) -> assert false
| LetIn (na, c, t, u) ->
   let (sigma, c_) = otranslate_param env param_env sigma (ind, ind_e) c in
   let (sigma, t_) = otranslate_param_type env param_env sigma (ind, ind_e) t in
   let is_ind_param = EUtil.term_finish_in_ind sigma t ind in
   let (sigma, ctw, param_env) =
     if is_ind_param then (sigma, (None, None), 1 :: param_env)
     else let (s, cw) = otranslate_param env param_env sigma (ind, ind_e) c in
          let (s, tw) = otranslate_param_type env param_env s (ind, ind_e) t in
          (s, (Some cw, Some tw), 2 :: param_env)
   in
   let nenv = push_def na (c, c_) (t, t_) env in
   let ctx = param_top_decls nenv is_ind_param in
   let (sigma, ur) = otranslate_param nenv param_env sigma (ind, ind_e) u in
   let r = it_mkLambda_or_LetIn ur ctx in
   (sigma, r)
| App (t, args) ->
   let args = Array.to_list args in
   let (sigma, tw) = otranslate_param env param_env sigma (ind, ind_e) t in
   let fold t (sigma, accum) =
     let (sigma, t_) = otranslate_param env param_env sigma (ind, ind_e) t in
     (sigma, t_ :: accum)
   in
   let (sigma, argsw) = List.fold_right fold args (sigma, []) in
   let w = applist (tw, argsw) in
   (sigma, w)
| Var id ->
   apply_global env sigma (VarRef id)
| Const (p, _) ->
   let (sigma, c) = apply_global env sigma (ConstRef p) in
   (sigma, c)
| Ind ((ind', n), u) when MutInd.equal ind ind' ->
   let mind,_ = Inductive.lookup_mind_specif env.env_tgt (ind',n) in
   let e = Environ.nb_rel env.env_tgt in
   let mind_t = mkRel (e + mind.mind_ntypes - n) in
   let gen, _ = get_ind env (ind',n) in
   let mind_t = if gen then mkApp (mind_t, [|mkRel e|]) else mind_t in
   (sigma, mind_t)
| Ind (ind, _) ->
   let (sigma, c) = apply_global env sigma (IndRef ind) in
   (sigma, c)
| Construct (c, _) ->
   let (sigma, c) = apply_global env sigma (ConstructRef c) in
   (sigma, c)
| Case (ci, r, d, p) -> assert false
| Cast (c, k, t) ->
  let (sigma, ce) = otranslate_param env param_env sigma (ind, ind_e) c in
  let (sigma, te) = otranslate_param_type env param_env sigma (ind, ind_e) t in
  let r = mkCast (ce, k, te) in
  (sigma, r)
| _ ->
   (sigma, c)
and otranslate_param_type env param_env sigma (ind, ind_e) c = match EConstr.kind sigma c with
| Sort s ->
   otranslate_type env sigma c
| Prod (na,t,u) ->
   let (sigma, t_) = otranslate_type env sigma t in
   let t_ = param_lift param_env t_ in
   let is_ind_param = EUtil.term_finish_in_ind sigma t ind in
   let nenv = push_assum na (t, t_) env in
   let (sigma, nenv, param_env) =
     if not is_ind_param then (sigma, nenv, 1 :: param_env)
     else let (sigma, tp) = otranslate_param_type env param_env sigma (ind, ind_e) t in
          let assum_env = EConstr.push_rel (LocalAssum (na, tp)) nenv.env_tgt in
          let new_env = { nenv with env_tgt = assum_env; } in
          (sigma, new_env, 2 :: param_env)
   in
   let (sigma, uw) = otranslate_param_type nenv param_env sigma (ind, ind_e) u in
   let n = if is_ind_param then 3 else 2 in
   let uw = Vars.liftn 1 (if is_ind_param then 4 else 3) uw in
   let uw = Vars.subst1 (mkApp (mkRel n, [| mkRel (n - 1) |])) uw in
   let ctx = param_top_decls nenv is_ind_param in
   let ctx = lift_rel_context 1 ctx in
   let r = it_mkProd_or_LetIn uw ctx in
   (sigma, r)
| _ ->
   let (sigma, cr) = otranslate_param env param_env sigma (ind, ind_e) c in
   (sigma, mkApp (Vars.lift 1 cr, [| mkRel 1 |]))

let param_constr err env sigma gen (block, block_e, n) mind_d mind_e one_d one_e =
  (*let _, env = extend_inductive env mind_d mind_e in*)
  let nblock = Array.length mind_d.mind_packets in
  let gen = Option.is_empty err in
  let mk_ind n = mkInd (block, nblock - (n + 1)) in
  let subst0 = List.init nblock mk_ind in
  let map (c, sigma) t =
    let t = EConstr.of_constr t in
    let t = Vars.substnl subst0 (Environ.nb_rel env.env_src) t in
    let param_env = List.init (List.length mind_e.mind_entry_params) (fun i -> 1) in
    let (sigma, te) = otranslate_param_type env param_env sigma (block, block_e) t in

    let (sigma, (c_, u)) = Evd.fresh_constructor_instance env.env_tgt sigma ((block_e,n), c) in
    let constr = mkConstructU (c_, EInstance.make u) in

    let args = List.init (List.length mind_e.mind_entry_params) (fun i -> mkRel (i + 1)) in
    let args = List.rev args in
    let n_params = List.length mind_e.mind_entry_params in
    let e = n_params + 1 in
    let constr = if gen then mkApp (constr, [|mkRel e|]) else constr in
    let constr = applist (constr, args) in
    let te = Vars.subst1 constr te in
    ((succ c, sigma), te)
  in
  let ((_, sigma), lc) = List.fold_left_map map (1,sigma) one_e.mind_entry_lc in
  (sigma, lc)

let param_inductive err env sigma (block, block_e, n as total_ind) mind_d mind_e one_d one_e =
  let typename = EUtil.translate_param_name one_e.mind_entry_typename in
  let mind_arity_ctxt = List.map EConstr.of_rel_decl one_d.mind_arity_ctxt in
  let nindices = List.length one_d.mind_arity_ctxt - List.length mind_d.mind_params_ctxt in
  let index_ctxt, _ =  List.chop nindices mind_arity_ctxt in
  let (sigma, arity_env, arity_ctx') = otranslate_context env sigma index_ctxt in
  let gen = Option.is_empty err  in
  let (sigma, (ind_, u)) = Evd.fresh_inductive_instance env.env_tgt sigma (block_e, n) in
  let ind_ = mkIndU (ind_, EInstance.make u) in
  let make_arg (n, accu) = function
    | LocalAssum _ -> (succ n, mkRel n :: accu)
    | LocalDef _ -> (succ n, accu)
  in
  let (_, args) = List.fold_left make_arg (1,[]) mind_arity_ctxt  in
  let args = if gen then mkRel (Environ.nb_rel arity_env.env_tgt) :: args else args in
  let ind_ = applist (ind_, args) in
  let self = LocalAssum (Anonymous, ind_) in
  let (sigma, sort) = Evd.fresh_sort_in_family ~rigid:Evd.UnivRigid env.env_tgt sigma InProp in
  let arity = it_mkProd_or_LetIn (mkSort sort) (self :: arity_ctx') in
  let (sigma, _) = Typing.type_of env.env_tgt sigma arity in

  (*let ext = match env.error with
  | None -> GlobGen block_e
  | Some exn -> GlobImp (Refmap.singleton exn block_e)
  in
  let translator = { env.translator with inds = Mindmap.add block ext env.translator.inds } in
  let env = { env with translator } in*)
  let (sigma, lc) = param_constr err env sigma gen total_ind mind_d mind_e one_d one_e in
  let lc = List.map (fun c -> EConstr.to_constr sigma c) lc in

  let consnames = List.map EUtil.translate_param_name one_e.mind_entry_consnames in
  let ind = { one_e with
    mind_entry_typename = typename;
    mind_entry_arity = EConstr.to_constr sigma arity;
    mind_entry_consnames = consnames;
    mind_entry_lc = lc;
  } in
  (sigma, ind)

let param_mutual_inductive err translator env (block, block_e) mind_d mind_e =
  let sigma = Evd.from_env env in
  let (sigma, env) = make_context err translator env sigma in

  let of_rel_decl_param_ctxt = List.map EConstr.of_rel_decl mind_d.mind_params_ctxt in
  let (sigma, env, _) = otranslate_context env sigma of_rel_decl_param_ctxt in
  let inds = List.combine (Array.to_list mind_d.mind_packets) mind_e.mind_entry_inds in
  let inds = List.mapi (fun i (l,r) -> (i,l,r)) inds in
  let map sigma (n, ind_d, ind_e) =
    param_inductive err env sigma (block, block_e, n) mind_d mind_e ind_d ind_e
  in
  let (sigma, param_inds) = List.fold_left_map map sigma inds in

  let env_context = EConstr.rel_context env.env_tgt in
  let sigma, inds, params = EUtil.retype_inductive env.env_tgt sigma env_context param_inds in
  let params = List.map to_local_entry params in
  let uctx = UState.context (Evd.evar_universe_context sigma) in
  let univs = match mind_e.mind_entry_universes with
  | Monomorphic_ind_entry _ -> Monomorphic_ind_entry (Univ.ContextSet.of_context uctx)
  | Polymorphic_ind_entry _ -> Polymorphic_ind_entry uctx
  | Cumulative_ind_entry _ -> Polymorphic_ind_entry uctx (** FIXME *)
  in
  let mind = { mind_e with
    mind_entry_inds = inds;
    mind_entry_params = params;
    mind_entry_universes = univs;
  } in
  mind

let param_instance_inductive err translator env (name,name_e,name_param) (one_d, n) =
  let sigma = Evd.from_env env in
  let gen = Option.is_empty err in

  let arity = Declarations.(one_d.mind_arity_ctxt) in
  let ctx = List.map EConstr.of_rel_decl arity in
  let param_ind = (param_mod, 0) in
  let sigma,(param_ind, u) = Evd.fresh_inductive_instance env sigma param_ind in
  let param_ind = mkIndU (param_ind, EInstance.make u) in
  let args = List.rev (List.init (List.length ctx) (fun i -> mkRel (i + 1))) in
  let sigma, (ind, u) = Evd.fresh_inductive_instance env sigma (name, n) in
  let ind = mkIndU (ind, EInstance.make u) in
  let ty = applist (ind, args) in
  let body = mkApp (param_ind, [| ty |]) in
  let instance_ty = it_mkProd_or_LetIn body ctx in
  let sigma,_ = Typing.type_of env sigma instance_ty in

  let (sigma, cenv) = make_context err translator env sigma in
  let (sigma, decl_e) = make_error err env sigma in

  let arity_ctx = List.map EConstr.of_rel_decl one_d.mind_arity_ctxt in
  let (sigma, cenv, _) = otranslate_context cenv sigma arity_ctx in
  let ctx = EConstr.rel_context cenv.env_tgt in
  let e = List.length ctx in
  let param_constr = ((param_mod_e, 0), 1) in
  let sigma,(param_constr, u) = Evd.fresh_constructor_instance env sigma param_constr in
  let param_constr = mkConstructU (param_constr, EInstance.make u) in
  let param_constr = mkApp (param_constr, [|mkRel e|]) in
  let args =  List.rev (List.init (List.length ctx - 1) (fun i -> mkRel (i + 1))) in
  let sigma, (ind, u) = Evd.fresh_inductive_instance env sigma (name_e, n) in
  let ind = mkIndU (ind, EInstance.make u) in
  let ind = if gen then mkApp (ind, [|mkRel e|]) else ind in
  let ty = applist (ind, args) in
  let (sigma, typeval) = Evd.fresh_global env sigma typeval_e in
  let typeval = EConstr.of_constr typeval in
  let def_cons = Array.length one_d.mind_user_lc in
  let (sigma, (def, u)) = Evd.fresh_constructor_instance env sigma ((name_e,n), def_cons + 1) in
  let def = mkConstructU (def, EInstance.make u) in
  let def_args = if gen then mkRel e :: args else args in
  let param_ty = mkApp (typeval, [| mkRel e; ty; applist (def, def_args) |]) in

  (* param of target *)
  let sigma, (ind_p, u) = Evd.fresh_inductive_instance env sigma (name_param, n) in
  let ind_p = mkIndU (ind_p, EInstance.make u) in
  let gen = Option.is_empty err in
  let ind_p = if gen then mkApp (ind_p, [|mkRel (List.length ctx + 1)|]) else ind_p in
  let args = List.map (fun i -> Vars.lift 1 i) args in
  let inner_func = applist (ind_p, args) in
  let func = mkLambda (Anonymous, ty, mkApp (inner_func, [| mkRel 1 |])) in

  (* param_correct of target *)
  let param_raise_ctx = Context.Rel.empty in
  let sigma, tm_exc_e = Evd.fresh_global env sigma (ConstRef tm_exception_e) in
  let tm_exc_e = EConstr.of_constr tm_exc_e in
  let tm_exc_e_tm = mkApp (tm_exc_e, [|mkRel e|]) in
  let sigma, tm_el = Evd.fresh_global env sigma el_e in
  let tm_exc_e_tm = mkApp (EConstr.of_constr tm_el, [|mkRel e; tm_exc_e_tm|]) in
  let tm_exec_name = Name (Id.of_string "e") in
  let param_raise_ctx = Context.Rel.add (LocalAssum (tm_exec_name, tm_exc_e_tm)) param_raise_ctx in

  let exc_constructor = ((name_e, n), (Array.length one_d.mind_user_lc) + 1) in
  let sigma,(exc_constr, u) = Evd.fresh_constructor_instance env sigma exc_constructor in
  let exc_constr = mkConstructU (exc_constr, EInstance.make u) in
  let exc_constr = if gen then mkApp (exc_constr, [|mkRel (e + 1)|]) else exc_constr in
  let exc_constr = applist (exc_constr, args) in
  let sigma, tm_typeval_e = fresh_global cenv sigma typeval_e in
  let type_arg = mkApp (tm_typeval_e, [|mkRel (e + 1); Vars.lift 1 ty; exc_constr|]) in
  let sigma, raise_e = fresh_global cenv sigma (ConstRef tm_raise_e) in
  let raise_tm = mkApp (raise_e, [|mkRel (e + 1); type_arg; mkRel 1|]) in
  let param_raise_tm = mkApp (Vars.lift 1 func, [|raise_tm|]) in
  let param_raise_ctx = Context.Rel.add (LocalAssum (Anonymous, param_raise_tm)) param_raise_ctx in

  let sigma, (tm_false_e, tm_false_univ) = Evd.fresh_inductive_instance env sigma (tm_False_e, 0) in
  let tm_false_e = EConstr.mkIndU (tm_false_e, EInstance.make tm_false_univ) in
  let contradiction = mkApp (tm_false_e, [|mkRel (e + 2)|]) in

  let theorem = it_mkProd_or_LetIn contradiction param_raise_ctx in
  let new_theorem = EConstr.it_mkProd_or_LetIn theorem (EConstr.rel_context cenv.env_tgt) in

  let ustate = Evd.evar_universe_context sigma in
  let inv_tactic = Misctypes.(Inv.inv FullInversion None (AnonHyp 1)) in
  let param_correct, _, state = Pfedit.build_by_tactic cenv.env_tgt ustate new_theorem inv_tactic in
  let param_correct  = EConstr.of_constr param_correct in
  let _, param_correct = EConstr.decompose_lam_n_assum sigma (List.length ctx) param_correct in
  let sigma = Evd.merge_universe_context sigma state in

  let body = mkApp (param_constr, [|param_ty; func; param_correct|]) in
  let param_instance = it_mkLambda_or_LetIn body ctx in
  let sigma,_ = Typing.type_of env sigma param_instance in

  (sigma, instance_ty, param_instance)

module SourceInduction = struct

  let rec induction_generator sigma params_number constr_ty ind n_ind =
    match EConstr.kind sigma constr_ty with
    | App (t, args) ->
       let _, arity = Array.chop params_number args in
       let arity = Array.map (fun a -> Vars.lift 2 a) arity in
       mkApp (mkRel 2, Array.append arity [| mkRel 1 |])
    | Ind (name, _) ->
       mkApp (mkRel 2, [| mkRel 1 |])
    | Prod (na, t, b) ->
       let end_in_ind = EUtil.term_finish_in_ind_exact sigma t ind n_ind in
       let rest = induction_generator sigma params_number b ind n_ind in
       let body =
         if end_in_ind then
           let ty = induction_generator sigma params_number t ind n_ind in
           let ty = Vars.liftn 1 2 ty in
           let rest = Vars.liftn 4 4 rest in
           let subst = [mkApp (mkRel 3, [| mkRel 2|]); mkRel 4; mkRel 2] in
           let rest = Vars.substnl subst 0 rest in
           mkProd (Anonymous, ty, rest)
         else
           let rest = Vars.liftn 3 4 rest in
           let subst = [(mkApp (mkRel 2, [| mkRel 1 |])); mkRel 3; mkRel 1] in
           let rest = Vars.substnl subst 0 rest in
           rest
       in
       let t = mkProd (na, Vars.lift 2 t, body) in
       t
    | _ -> constr_ty

  let source_induction sigma env name mind_d n  =
    let one_d = mind_d.mind_packets.(n) in

    let nindices = List.length one_d.mind_arity_ctxt - List.length mind_d.mind_params_ctxt in
    let nparams = Declarations.(mind_d.mind_nparams) in
    let mind_arity_ctxt = List.map EConstr.of_rel_decl one_d.mind_arity_ctxt in
    let (arity_ctx, param_ctx) = List.chop nindices mind_arity_ctxt in
    let real_param_ctx = List.filter (fun decl -> Rel.Declaration.is_local_assum decl) param_ctx in
    let (sigma, sort) = Evd.fresh_sort_in_family env.env_tgt sigma InProp in

    let (sigma, (ind, u)) = Evd.fresh_inductive_instance env.env_tgt sigma (name, n) in
    let ind = mkIndU (ind, EInstance.make u) in
    let app_args = List.init (List.length one_d.mind_arity_ctxt) (fun i -> mkRel (i + 1)) in
    let app_ind = applist (ind, List.rev app_args) in
    let predicate = it_mkProd_or_LetIn (mkProd (Anonymous, app_ind, (mkSort sort))) arity_ctx in
    let substl_ind = List.init mind_d.mind_ntypes (fun i -> mkInd (name, i)) in
    let decompose_map cty =
      let _, non_param_cty = EConstr.decompose_prod_n_assum sigma nparams cty in
      let non_param_cty = Vars.substnl substl_ind nparams non_param_cty in
      non_param_cty
    in
    let mind_user_lc = Array.to_list one_d.mind_user_lc in
    let mind_user_lc = List.map  EConstr.of_constr mind_user_lc in
    let constr_types = List.map decompose_map mind_user_lc in
    let params_args = List.rev (List.init nparams (fun n -> mkRel (n + 2))) in
    let map i constr =
      let constr_ind = induction_generator sigma nparams constr name n in
      let constr_ind = Vars.liftn 1 3 constr_ind in
      let ind_constr = mkConstruct ((name, n), (i + 1)) in
      let constr_constr = Vars.substl [(applist (ind_constr, params_args)); mkRel 1] constr_ind in
      Vars.lift i constr_constr
    in
    let pred_map = List.map_i map 0 constr_types in
    let predicates_ctx = List.map (fun i -> Rel.Declaration.LocalAssum (Anonymous, i)) pred_map in

    let n_predicates = List.length predicates_ctx in
    let arity_ctx = Rel.map (fun i -> Vars.lift (n_predicates + 1) i) arity_ctx in

    let param_inds = List.init nparams (fun n -> mkRel (n_predicates + nindices + 1 + n + 1)) in
    let param_inds = List.rev param_inds in
    let index_inds = List.rev (List.init nindices (fun n -> mkRel (n + 1))) in
    let full_args_ind = param_inds @ index_inds in
    let ind_cons = applist (ind, full_args_ind) in

    let ctxt = Rel.add (Rel.Declaration.LocalAssum
                          (Name (Id.of_string "P"), predicate)) real_param_ctx
    in
    let ctxt = List.fold_left (fun acc d -> Rel.add d acc) ctxt predicates_ctx in
    let ctxt = List.fold_left (fun acc d -> Rel.add d acc) ctxt (List.rev arity_ctx) in
    let ctxt = Rel.add (Rel.Declaration.LocalAssum (Anonymous, ind_cons)) ctxt in

    let base_instance_name = EUtil.translate_instance_name Declarations.(one_d.mind_typename) in
    let instance_name = Constant.make1 (Lib.make_kn base_instance_name) in
    let (sigma, (instance_t, u)) = Evd.fresh_constant_instance env.env_src sigma instance_name in
    let instance_t = mkConstU (instance_t, EInstance.make u) in
    let instance_t = applist (instance_t, List.map (Vars.lift 1) full_args_ind) in
    let param_ind = mkApp (mkProj ((Projection.make param_cst false), instance_t), [| mkRel 1 |] ) in
    let ctxt = Rel.add (Rel.Declaration.LocalAssum (Anonymous, param_ind)) ctxt in

    let predicate = mkRel (nindices + 2 + n_predicates + 1) in
    let predicate_args = List.init nindices (fun n -> mkRel (n + 3)) in
    let predicate_args = List.rev (mkRel 2 :: predicate_args) in
    let induction_pr = it_mkProd_or_LetIn (applist (predicate, predicate_args)) ctxt in
    induction_pr

end

let dummy_param mind =
  let _,_,l = MutInd.repr3 mind in
  Lib.make_kn  (Nameops.add_suffix (Label.to_id l) "_dummy_param")

let rec induction_predicate_gen sigma params_number constr_ty ind n_ind dummy =
match EConstr.kind sigma constr_ty with
| Ind _ ->
    dummy
| App (_, args) ->
   let args = Array.map (fun i -> Vars.lift 1 i) args in
   let _,args = Array.chop params_number args in
   mkApp (dummy, args)
| Prod (na, t, b) ->
   let bp = induction_predicate_gen sigma params_number b ind n_ind dummy in
   let bp = Vars.liftn 2 3 bp in
   let subst = [mkRel 2; mkRel 1] in
   let bp = Vars.substnl subst 0 bp in
   mkProd (na, Vars.lift 1 t, bp)
| _ -> constr_ty

let rec induction_predicate_generator sigma params_number constr_ty ind n_ind dummy =
match EConstr.kind sigma constr_ty with
| (App _ | Ind _) ->
   mkRel 1
| Prod (na, t, b) ->
   let end_in_ind = EUtil.term_finish_in_ind_exact sigma t ind n_ind in
   let bp = induction_predicate_generator sigma params_number b ind n_ind dummy in
   let body =
     if end_in_ind then
       let tp = induction_predicate_gen sigma params_number t ind n_ind dummy in
       let tp = Vars.liftn 3 2 tp in
       let tp = Vars.subst1 (mkRel 3) tp in
       let bp = Vars.liftn 4 4 bp in
       let subst = [mkApp (mkRel 3, [|mkRel 1|]); mkRel 4;  mkRel 2] in
       let bp = Vars.substnl subst 0  bp in
       mkLambda (Anonymous, tp, bp)
     else
       let bp = Vars.liftn 3 4 bp in
       let subst = [mkApp (mkRel 2, [|mkRel 1|]); mkRel 3; mkRel 1] in
       Vars.substnl subst 0 bp
   in
   let t = mkLambda (na, Vars.lift 2 t, body) in
   t
| _ -> constr_ty

let recover_param sigma name predicate term =
  let rec map_binder n term =
    match EConstr.kind sigma term with
    | Ind ((m,_), _) when MutInd.equal name m -> mkRel n
    | App (t, args) when (EConstr.isInd sigma t) &&
                           MutInd.equal name (fst (fst (EConstr.destInd sigma t))) ->
       mkApp (mkRel n, args)
    | _ -> map_with_binders sigma succ map_binder n term
  in
  map_binder predicate term

let parametric_induction err translator env name mind_d =
  let sigma = Evd.from_env env in
  let (sigma, env) = make_context err translator env sigma in

  let n = 0 in
  let one_d = mind_d.mind_packets.(n) in
  let nparams = Declarations.(mind_d.mind_nparams) in
  let nindices = List.length one_d.mind_arity_ctxt - List.length mind_d.mind_params_ctxt in
  let induction_pr = SourceInduction.source_induction sigma env name mind_d n in

  let sigma,induction_pr_tr = otranslate_type env sigma induction_pr in
  let induction_pr_tr_ctx, _ = EConstr.decompose_prod_assum sigma induction_pr_tr in

  let (_,_,l) = MutInd.repr3 name in
  let name_param = Nameops.add_suffix (Label.to_id l) "_param" in
  let name_param = MutInd.make1 (Lib.make_kn name_param) in

  let mind_d_param,_ = Inductive.lookup_mind_specif env.env_src (name_param, 0) in
  let one_d_param = mind_d_param.mind_packets.(n) in
  let mind_param = List.init mind_d.mind_ntypes (fun n -> n) in
  let fold_map sigma n =
    let (sigma, (ind, u)) = Evd.fresh_inductive_instance env.env_src sigma (name_param, n) in
    (sigma, mkIndU (ind, EInstance.make u))
  in
  let sigma, ind_subst = List.fold_left_map fold_map sigma mind_param in

  let ind_param_induction = Nameops.add_suffix one_d.mind_typename "_param_ind" in
  let sigma, (ind_param_induction, u) =
    let cst = (Constant.make1 (Lib.make_kn ind_param_induction)) in
    Evd.fresh_constant_instance env.env_src sigma cst
  in
  let cst = mkConstU (ind_param_induction, EInstance.make u) in
  let n_preds = Array.length one_d.mind_user_lc in
  let params_offset = nindices + n_preds + 3 in

  let map m constr_ty =
    let constr_ty = EConstr.of_constr constr_ty in
    let constr_ty = Vars.substnl ind_subst 0 constr_ty in
    let _,constr_ty = EConstr.decompose_prod_n_assum sigma (nparams + 1) constr_ty in
    let ind_pred_gen = induction_predicate_generator in
    let dummy_param_name = MutInd.make1 (dummy_param name) in
    let dummy_term  = mkInd (dummy_param_name, 0) in
    let generator_predicates = ind_pred_gen sigma (nparams + 1) constr_ty name_param m dummy_term in
    let generator_predicates = recover_param sigma dummy_param_name 2 generator_predicates in
    let lift = n_preds + nindices + 2 in
    let generator_predicates = Vars.liftn lift 2 generator_predicates in
    Vars.subst1 (mkRel (2 + nindices + n_preds - m)) generator_predicates
  in
  let pred_trans = Array.mapi map one_d_param.mind_user_lc in

  let cst_predicate =
    let param_arity_ctx,_ = List.chop (nindices + 1) Declarations.(one_d_param.mind_arity_ctxt) in
    let param_arity_ctx = List.map EConstr.of_rel_decl param_arity_ctx in
    let pind_arity = List.rev (List.init (nindices + 1) (fun n -> mkRel (n + 1))) in
    let pind_param = List.rev (List.init (nparams + 1) (fun n -> mkRel (n + nindices + 2))) in
    let pind = List.nth ind_subst n in
    let pind_arg = applist (pind, pind_param @ pind_arity) in
    let body_predicate = mkLambda (Anonymous, pind_arg, mkRel 0) in
    let predicate = it_mkLambda_or_LetIn body_predicate param_arity_ctx in
    let predicate = Vars.lift 1 predicate in
    let predicate_ctx,_ = EConstr.decompose_lam_assum sigma predicate in
    let predicate_rel = nindices + 3 in
    let body_predicate = applist (mkRel predicate_rel, List.map (Vars.lift 1) pind_arity) in
    it_mkLambda_or_LetIn body_predicate predicate_ctx
  in
  let cst_predicate = Vars.lift (params_offset - 1) cst_predicate in
  let cst_params = Array.init (nparams + 1) (fun n -> mkRel (n + 1 + params_offset)) in
  let cst_arity = Array.init (nindices + 2) (fun n -> mkRel (n + 1)) in
  let () = Array.rev cst_params in
  let () = Array.rev cst_arity in
  let cst_args = Array.(append (append cst_params (cons cst_predicate pred_trans)) cst_arity) in
  let app_cst = mkApp (cst, cst_args) in
  let trans_pred = it_mkLambda_or_LetIn app_cst induction_pr_tr_ctx in
  let e = get_exception env in
  let trans_pred = mkLambda_or_LetIn e trans_pred in
  let sigma,_ = Typing.type_of env.env_src sigma trans_pred in
  (sigma, induction_pr, trans_pred, mkProd_or_LetIn e induction_pr_tr)


module InductionCatch = struct

  (* Similar (same) to SourceInduction.induction_generator. This function works on a single
   * constructor and defines the predicate structure. This method should only be applied
   * if `constr_ty` is strictly positive  respect to `ind` and instead of an actual
   * constructor type, it has already replaced the Rel to inductives with Ind*)
  let rec inductive_predicate_structure_gen sigma params_number constr_ty ind n_ind =
    match EConstr.kind sigma constr_ty with
    | App (t, args) ->
       let _, arity = Array.chop params_number args in
       let arity = Array.map (fun a -> Vars.lift 2 a) arity in
       mkApp (mkRel 2, Array.append arity [| mkRel 1 |])
    | Ind ((ind_name, ind_constructor), _)
           when (Names.MutInd.equal ind ind_name) && (ind_constructor == n_ind) ->
       mkApp (mkRel 2, [| mkRel 1 |])
    | Prod (na, t, b) ->
       let end_in_ind = EUtil.term_finish_in_ind_exact sigma t ind n_ind in
       let rest = inductive_predicate_structure_gen sigma params_number b ind n_ind in
       let body =
         if end_in_ind then
           let ty = inductive_predicate_structure_gen sigma params_number t ind n_ind in
           let ty = Vars.liftn 1 2 ty in
           let rest = Vars.liftn 4 4 rest in
           let subst = [mkApp (mkRel 3, [| mkRel 2|]); mkRel 4; mkRel 2] in
           let rest = Vars.substnl subst 0 rest in
           mkProd (Anonymous, ty, rest)
         else
           let rest = Vars.liftn 3 4 rest in
           let subst = [(mkApp (mkRel 2, [| mkRel 1 |])); mkRel 3; mkRel 1] in
           let rest = Vars.substnl subst 0 rest in
           rest
       in
       let t = mkProd (na, Vars.lift 2 t, body) in
       t
    | _ -> constr_ty

  let constr_rel_replaced_by_ind sigma name n_ind_types nparams one_d =
    let substl_ind = List.init n_ind_types (fun i -> mkInd (name, i)) in
    let decompose_map cty =
      let _, non_param_cty = EConstr.decompose_prod_n_assum sigma nparams cty in
      let non_param_cty = Vars.substnl substl_ind nparams non_param_cty in
      non_param_cty
    in
    let mind_user_lc = Array.to_list one_d.mind_user_lc in
    let mind_user_lc = List.map  EConstr.of_constr mind_user_lc in
    List.map decompose_map mind_user_lc

  (* Assumes a context for rels Predicate :: Param_n :: ... :: Param_1 *)
  let case_for_exceptional_constructor sigma env (mind_name, mind_n) nparams one_d_arity =
    let sigma, inst_raise = fresh_global env sigma (ConstRef tm_raise) in
    let sigma, (ind_, u) = Evd.fresh_inductive_instance env.env_tgt sigma (mind_name, mind_n) in
    let inst_ind_ = mkIndU (ind_, EInstance.make u) in
    let arity_length = Context.Rel.length one_d_arity in
    let param_rel = List.init nparams (fun n -> mkRel (n + arity_length + 3)) in
    let arity_rel = List.init arity_length (fun n -> mkRel (n + 2)) in
    let app_ind_ = applist (inst_ind_, (List.rev param_rel) @ (List.rev arity_rel)) in
    let app_raise = mkApp (inst_raise, [| app_ind_; mkRel 1 |]) in
    let predicate_index_args =
      List.init (Context.Rel.length one_d_arity) (fun n -> mkRel (n + 2))
    in
    let predicate_index_args = List.rev predicate_index_args in
    let predicate_index_args = predicate_index_args @ [ app_raise ] in
    let predicate_raise = applist (mkRel (arity_length + 2), predicate_index_args) in
    let sigma, inst_exc_ty = fresh_global env sigma (ConstRef tm_exception) in
    let exc_raise_fun = mkProd (Name.mk_name (Id.of_string "e"), inst_exc_ty, predicate_raise) in
    let exc_case = it_mkProd_or_LetIn exc_raise_fun one_d_arity in
    sigma, exc_case

  let source_induction sigma env name (mind_d, mind_n) =
    let one_d = mind_d.mind_packets.(mind_n) in
    let nindices = List.length one_d.mind_arity_ctxt - List.length mind_d.mind_params_ctxt in
    let nparams = Declarations.(mind_d.mind_nparams) in
    let n_ind_types = mind_d.mind_ntypes in

    let constr_types = constr_rel_replaced_by_ind sigma name n_ind_types nparams one_d in

    let mind_arity_ctxt = List.map EConstr.of_rel_decl one_d.mind_arity_ctxt in
    let (arity_ctx, param_ctx) = List.chop nindices mind_arity_ctxt in
    let real_param_ctx = List.filter (fun decl -> Rel.Declaration.is_local_assum decl) param_ctx in
    let (sigma, sort) = Evd.fresh_sort_in_family env.env_tgt sigma InType in

    let (sigma, (ind, u)) = Evd.fresh_inductive_instance env.env_tgt sigma (name, mind_n) in
    let ind = mkIndU (ind, EInstance.make u) in
    let app_args = List.init (List.length one_d.mind_arity_ctxt) (fun i -> mkRel (i + 1)) in
    let app_ind = applist (ind, List.rev app_args) in
    let predicate = it_mkProd_or_LetIn (mkProd (Anonymous, app_ind, (mkSort sort))) arity_ctx in

    let params_args = List.rev (List.init nparams (fun n -> mkRel (n + 2))) in
    let map i constr =
      let constr_ind = inductive_predicate_structure_gen sigma nparams constr name mind_n in
      let constr_ind = Vars.liftn 1 3 constr_ind in
      let ind_constr = mkConstruct ((name, mind_n), (i + 1)) in
      let constr_constr = Vars.substl [(applist (ind_constr, params_args)); mkRel 1] constr_ind in
      Vars.lift i constr_constr
    in
    let pred_map = List.map_i map 0 constr_types in
    let predicates_ctx = List.map (fun i -> Rel.Declaration.LocalAssum (Anonymous, i)) pred_map in

    let n_predicates = List.length predicates_ctx in

    (*
       It must add 2 to consider the new exceptional branch plus the predicate which
       are now in context
     *)
    let lift_arity_ctx = Rel.map (fun i -> Vars.lift (n_predicates + 2) i) arity_ctx in

    let param_inds = List.init nparams (fun n -> mkRel (n_predicates + nindices + n + 3)) in
    let param_inds = List.rev param_inds in
    let index_inds = List.rev (List.init nindices (fun n -> mkRel (n + 1))) in
    let full_args_ind = param_inds @ index_inds in
    let ind_cons = applist (ind, full_args_ind) in

    let ctxt = Rel.add (Rel.Declaration.LocalAssum
                          (Name (Id.of_string "P"), predicate)) real_param_ctx
    in
    let ctxt = List.fold_left (fun acc d -> Rel.add d acc) ctxt predicates_ctx in
    let sigma, exc_case =
      (* The below function assumes that the predicates is in context, hence the lift *)
      let arity_ctx = Rel.map (fun i -> Vars.lift 1 i) arity_ctx in
      case_for_exceptional_constructor sigma env (name, mind_n) nparams arity_ctx
    in
    let lifted_exc_case = Vars.lift (Array.length one_d.mind_user_lc) exc_case in
    let ctxt_w_exc_case = Rel.add (Rel.Declaration.LocalAssum (Anonymous, lifted_exc_case)) ctxt in
    let ctxt_w_arity =
      List.fold_left (fun acc d -> Rel.add d acc) ctxt_w_exc_case (List.rev lift_arity_ctx)
    in
    let ctxt_w_ind = Rel.add (Rel.Declaration.LocalAssum (Anonymous, ind_cons)) ctxt_w_arity in

    let predicate = mkRel (nindices + 3 + n_predicates) in
    let predicate_args = List.init nindices (fun n -> mkRel (n + 2)) in
    let predicate_args_w_instance = List.rev (mkRel 1 :: predicate_args) in
    let induction_pr =
      it_mkProd_or_LetIn (applist (predicate, predicate_args_w_instance)) ctxt_w_ind
    in
    sigma, induction_pr

  let rec is_predicate_e sigma pred_index ty =
    match EConstr.kind sigma ty with
    | App (app, args) ->
       if Array.length args >= 2 then
         let poss_app = args.(1) in
         if EConstr.isApp sigma poss_app then
           let poss_pred, _ = EConstr.destApp sigma poss_app in
           EConstr.isRel sigma poss_pred && EConstr.destRel sigma poss_pred == pred_index
         else
           false
       else
         false
    | Prod (na, ty, body) ->
       is_predicate_e sigma (pred_index + 1) body
    | Const _ ->
       false
    | Rel _ ->
       false
    | _ -> raise BadFormingCatchInduction

  type catch_gen =
    | UseCase
    | UseFix

  let is_case = function
    | UseCase -> true
    | UseFix -> false

  (* This function take as a parameters the type corresponding to a specific branch in the target
     translation and assumes that their index are related to a context P :: arguments :: E. *)
  let case_catch_induction sigma case_ty_e =
    let rec case_catch_induction_rec sigma catch_gen recursion_index case_ty_e =
      match EConstr.kind sigma case_ty_e with
      | App (app, args) ->
         if is_case catch_gen then
           mkRel 1
         else
           let poss_app, poss_args = EConstr.destApp sigma args.(1) in
           let n_args = Array.map (Vars.lift 1) poss_args in
           mkApp (mkRel (recursion_index + 2), n_args)
      | Prod (na, ty, body) ->
         let body_e = case_catch_induction_rec sigma catch_gen (recursion_index + 1)  body in
         let prod_e =
           if is_predicate_e sigma (recursion_index + 1) ty then
             let ty_e = case_catch_induction_rec sigma UseFix recursion_index ty in
             let ty_app = mkApp (mkRel 1, [|ty_e|]) in
             let sbt_body_e = Vars.subst1 ty_app body_e in
             sbt_body_e
           else
             let bd_app = mkApp (mkRel 2,[| mkRel 1 |]) in
             let lf_body_e = Vars.liftn 1 3 body_e in
             let sbt_body_e = Vars.subst1 bd_app lf_body_e in
             mkLambda (na, Vars.lift 1 ty, sbt_body_e)
         in
         prod_e
      | _ -> case_ty_e
    in
    case_catch_induction_rec sigma UseCase 0 case_ty_e

  let lift_predicate_declarations lift_by ctx =
    let open Context.Rel in
    let fold_func d (n, ctx) =
      (n + 1, add (Declaration.map_type (Vars.liftn lift_by n) d) ctx)
    in
    let _, new_ctx = fold_outside fold_func ctx ~init:(1, empty) in
    new_ctx

  let target_induction env sigma name (mind_d, mind_n) source_ind_ty =
    let one_d = Declarations.(mind_d.mind_packets.(mind_n)) in
    let sigma, target_ind_ty = otranslate_type env sigma source_ind_ty in
    let nparams = mind_d.mind_nparams in
    let nargs = one_d.mind_nrealargs in
    let ncons = Array.length one_d.mind_user_lc in
    let predicate_pre_args = nparams + ncons + 2 in (* predicate arg plus exceptional constr *)
    let predicate_ctx, predicate_fix_args =
      EConstr.decompose_prod_n_assum sigma predicate_pre_args target_ind_ty
    in
    let sigma, fix_body =
      let partial_fix_ctx, _  = EConstr.decompose_prod_assum sigma predicate_fix_args in
      let sigma, predicate =
        let sigma, predicate_body =
          let array_init = Array.init (nargs + 1) (fun n -> mkRel (nargs + 1 - n)) in
          let predicate_index = ncons + 1 + 2 * (nargs + 1) + 2 in
          let body = mkApp (mkRel predicate_index, array_init) in
          let sigma, el_const = fresh_global env sigma el_e in
          let final_body = mkApp (el_const, [|mkRel (predicate_index + nparams + 1); body|]) in
          sigma, final_body
        in
        let new_partial_fix = lift_predicate_declarations (nargs + 2) partial_fix_ctx in
        sigma, it_mkLambda_or_LetIn predicate_body new_partial_fix
      in
      let init_case_constr n =
        let specific_cons = Context.Rel.lookup (ncons + 1 - n) predicate_ctx in
        let specific_cons_ty = Context.Rel.Declaration.get_type specific_cons in
        let specific_cons_ty = Vars.lift (-n) specific_cons_ty in
        let case = case_catch_induction sigma specific_cons_ty in
        let lifted_case = Vars.liftn (nargs + ncons + 3) 3 case in
        let subst_case = Vars.subst1 (mkRel (nargs + ncons + 3 - n)) lifted_case in
        let lifted_subst_case = Vars.liftn 1 2 subst_case in
        let final_subst_case = Vars.subst1 (mkRel (nargs + 2)) lifted_subst_case in
        final_subst_case
      in
      let match_cases_branch = Array.init (ncons + 1) init_case_constr in
      let case_info_e = Inductiveops.make_case_info env.env_src (name, mind_n) LetPatternStyle in
      let match_body = EConstr.mkCase (case_info_e, predicate, (mkRel 1), match_cases_branch) in
      let new_partial_fix_ctx = lift_predicate_declarations 1 partial_fix_ctx in
      let body = it_mkLambda_or_LetIn match_body new_partial_fix_ctx in
      sigma, body
    in

    let fix_fi = ([|nargs|], 0) in
    let fix_recdeclaration =
      let fix_name = [| Name.Name (Id.of_string "F") |] in
      let fix_typarray = [| predicate_fix_args |] in
      let fix_bodies = [| fix_body |] in
      (fix_name, fix_typarray, fix_bodies)
    in
    let fix_term = mkFix (fix_fi, fix_recdeclaration) in
    let ind_rect = it_mkLambda_or_LetIn fix_term predicate_ctx in
    let exceptional_decl = get_exception env in
    let ind_rect = mkLambda_or_LetIn exceptional_decl ind_rect in
    sigma, ind_rect

  let catch err translator env name (mind_d, mind_n) =
    let sigma = Evd.from_env env in
    let (sigma, env) = make_context err translator env sigma in
    let sigma, induction_pr = source_induction sigma env name (mind_d, mind_n) in
    let sigma, _ = Typing.type_of env.env_src sigma induction_pr in

    let _, (name_e, _) = get_ind env (name, mind_n) in
    let sigma, induction_pr_e = target_induction env sigma name_e (mind_d, mind_n) induction_pr in
    let sigma, _ = Typing.type_of env.env_tgt sigma induction_pr_e in
    (sigma, induction_pr, induction_pr_e)

end

let catch_induction = InductionCatch.catch
