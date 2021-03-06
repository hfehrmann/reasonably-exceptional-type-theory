open Names
open Globnames

type effect = global_reference option

exception MissingGlobal of effect * global_reference
exception MissingPrimitive of global_reference
exception MatchEliminationNotSupportedOnTranslation

type 'a global_translation =
| GlobGen of 'a
  (** Implementation generic over the type of exceptions *)
| GlobImp of 'a Refmap.t
  (** For every type of exceptions, a specialized implementation. *)

val get_instance : effect -> 'a global_translation -> bool * 'a

val instantiate_error : effect -> Environ.env -> Evd.evar_map -> bool -> EConstr.t -> Evd.evar_map * EConstr.t

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

val empty_translator: translator

val translate :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val translate_type :
  effect -> translator -> Environ.env -> Evd.evar_map -> EConstr.t -> Evd.evar_map * EConstr.t

val translate_inductive :
  effect -> translator -> Environ.env -> MutInd.t -> Declarations.mutual_inductive_body ->
    Entries.mutual_inductive_entry -> Entries.mutual_inductive_entry

val param_mutual_inductive :
  effect -> translator -> Environ.env -> MutInd.t * MutInd.t -> Declarations.mutual_inductive_body ->
    Entries.mutual_inductive_entry -> Entries.mutual_inductive_entry

val param_instance_inductive :
  effect -> translator -> Environ.env -> MutInd.t * MutInd.t * MutInd.t->
    Declarations.one_inductive_body * int -> Evd.evar_map * EConstr.t * EConstr.t

val parametric_induction :
  effect -> translator -> Environ.env -> MutInd.t -> Declarations.mutual_inductive_body ->
    Evd.evar_map * EConstr.t * EConstr.t * EConstr.t

val catch_induction :
  effect -> translator -> Environ.env -> MutInd.t ->
    Declarations.mutual_inductive_body * int -> Evd.evar_map * EConstr.t * EConstr.t
