open Entries
open Declarations
open Environ
open Evd

val retype_inductive :
  env -> evar_map -> EConstr.rel_context ->
  one_inductive_entry list ->
  evar_map * one_inductive_entry list * Context.Rel.t

val process_inductive : mutual_inductive_body -> mutual_inductive_entry

val primitive_record : mutual_inductive_body -> bool

(* Name operations *)
val translate_name: Names.Id.t -> Names.Id.t
val translate_inductive_name: Names.Id.t -> Names.Id.t
val translate_failure: Names.Id.t -> Names.Id.t
val translate_param_name: Names.Id.t -> Names.Id.t
val translate_instance_name: Names.Id.t -> Names.Id.t

(* term_finish_in_ind *)
val term_finish_in_ind: Evd.evar_map -> EConstr.t -> Names.MutInd.t -> bool
val term_finish_in_ind_exact: Evd.evar_map -> EConstr.t -> Names.MutInd.t -> int -> bool
