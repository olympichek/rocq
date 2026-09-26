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

let tests = [
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
