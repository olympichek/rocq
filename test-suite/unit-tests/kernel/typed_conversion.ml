open Utest
open Constr

let log_out_ch = open_log_out_ch __FILE__
let env = Environ.empty_env
let annot = Context.make_annot Names.Name.Anonymous Sorts.Relevant
let lambda domain = mkLambda (annot, domain, mkProp)
let product domain = mkProd (annot, domain, mkProp)
let identity = mkLambda (annot, mkProp, mkRel 1)
let beta_identity = mkLambda (annot, mkProp, mkApp (identity, [|mkRel 1|]))

let compare a b expected =
  ignore (Typeops.infer env a);
  ignore (Typeops.infer env b);
  Result.is_ok (Conversion.default_conv Conversion.CONV env a b) = expected
  && Result.is_ok (Conversion.conv env a b) = expected

(* An identical opaque head does not give its applications a common type
   until all preceding arguments have been converted. *)
let top = mkSort (Sorts.sort_of_univ Univ.Universe.type1)
let head = Names.Constant.make2 (Names.ModPath.MPfile Names.DirPath.empty)
  (Names.Id.of_string "typed_conversion_head")
let head_type = mkProd (annot, top,
  mkProd (annot, mkProd (annot, mkRel 1, top), top))
let head_env =
  ignore (Typeops.infer env head_type);
  let declaration = {
    Declarations.const_hyps = [];
    const_univ_hyps = UVars.Instance.empty;
    const_body = Declarations.Undef None;
    const_type = head_type;
    const_relevance = Sorts.Relevant;
    const_body_code = Vmemitcodes.BCuncompiled;
    const_universes = Declarations.Monomorphic;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
    const_def_height = None;
  } in
  Environ.add_constant head declaration env
let apply_head domain body = mkApp (mkConstU (head, UVars.Instance.empty),
  [|domain; mkLambda (annot, domain, body)|])
let head_left = apply_head mkProp mkProp
let head_good = apply_head mkProp
  (mkApp (mkLambda (annot, top, mkRel 1), [|mkProp|]))
let head_bad_prefix = apply_head mkSet mkProp
let head_bad_body = apply_head mkProp mkSet
let compare_head right expected =
  ignore (Typeops.infer head_env head_left);
  ignore (Typeops.infer head_env right);
  Result.is_ok (Conversion.default_conv Conversion.CONV head_env head_left right) = expected
  && Result.is_ok (Conversion.conv head_env head_left right) = expected

let tests = [
  mk_bool_test "typed-conv-constant-prefix-beta"
    "matching constant prefixes retain beta conversion"
    (compare_head head_good true);
  mk_bool_test "typed-conv-constant-prefix-mismatch"
    "different preceding arguments do not establish a common type"
    (compare_head head_bad_prefix false);
  mk_bool_test "typed-conv-constant-body-mismatch"
    "common lambda domains do not erase body comparisons"
    (compare_head head_bad_body false);
  mk_bool_test "typed-conv-lambda-domains"
    "separately well-typed lambdas need not have a common domain"
    (compare (lambda mkProp) (lambda mkSet) false);
  mk_bool_test "typed-conv-product-domains"
    "product domains are still compared"
    (compare (product mkProp) (product mkSet) false);
  mk_bool_test "typed-conv-beta"
    "ordinary lambda conversion remains available"
    (compare identity beta_identity true);
]

let () = run_tests __FILE__ log_out_ch tests
