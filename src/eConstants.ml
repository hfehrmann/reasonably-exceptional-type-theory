open Util
open Names

let effect_path =
  DirPath.make (List.map Id.of_string ["Effects"; "Weakly"])

let make_kn name =
  KerName.make2 (MPfile effect_path) (Label.make name)

let prop_e = ConstRef (Constant.make1 (make_kn "Propᵉ"))
let type_e = ConstRef (Constant.make1 (make_kn "Typeᵉ"))
let el_e = ConstRef (Constant.make1 (make_kn "El"))
let prod_e = ConstRef (Constant.make1 (make_kn "Prodᵉ"))
let err_e = ConstRef (Constant.make1 (make_kn "Err"))
let typeval_e = ConstructRef ((MutInd.make1 (make_kn "type"), 0), 1)

let param_mod = MutInd.make1 (make_kn "Param")
let param_mod_e = MutInd.make1 (make_kn "Paramᵉ")

let param_cst = Constant.make1 (make_kn "param")
let param_cst_e = Constant.make1 (make_kn "paramᵉ")

let param_correct_cst = Constant.make1 (make_kn "param_correct")
let param_correct_cst_e = Constant.make1 (make_kn "param_correctᵉ")

let tm_exception = Constant.make1 (make_kn "Exception")
let tm_exception_e = Constant.make1 (make_kn "Exceptionᵉ")

let tm_raise = Constant.make1 (make_kn "raise")
let tm_raise_e = Constant.make1 (make_kn "raiseᵉ")

let tm_False, _ = Globnames.destIndRef (Lazy.force Coqlib.coq_False_ref)
let tm_False_e = MutInd.make1 (make_kn "Falseᵒ")

let name_errtype = Id.of_string "E"
let name_err = Id.of_string "e"
