open Utest
open Constr
open CClosure

let log_out_ch = open_log_out_ch __FILE__

let identity = Esubst.subs_id 0, UVars.Instance.empty
let annot = Context.make_annot Names.Name.Anonymous Sorts.Relevant
let body = mkLambda (annot, mkSort Sorts.prop, mkRel 1)
let other_body = mkLambda (annot, mkSort Sorts.prop, mkRel 2)

let closure_env term = usubs_cons (mk_clos identity term) identity
let left = closure_env body
let right = closure_env body

let equal a b = equal_usubs_bounded ~fuel:128 a b
let reify env = term_of_fconstr (mk_clos env (mkRel 1))

let requires_new_path e1 e2 =
  let s1 = fst e1 and s2 = fst e2 in
  s1 != s2 && not (Esubst.is_subs_id s1) && not (Esubst.is_subs_id s2)
  && not (Esubst.Internal.equal subs_content_equal s1 s2)
  && let f1 = mk_clos e1 (mkRel 1) in
     let f2 = mk_clos e2 (mkRel 1) in
     f1 != f2 && match fterm_of f1, fterm_of f2 with
     | FCLOS (c1, _), FCLOS (c2, _) -> c1 == c2
     | _ -> false

let nested = mkLambda (annot, mkSort Sorts.prop, mkRel 2)
let nested_left = usubs_cons (mk_clos left nested) identity
let nested_right = usubs_cons (mk_clos right nested) identity

let universe_env n =
  fst identity,
  UVars.Instance.of_array ([||], [|Univ.Level.var n|])

let quality_env q =
  fst identity, UVars.Instance.of_array ([|q|], [||])

let long_left = ref identity
let long_right = ref identity
let () =
  for _ = 1 to 1000 do
    long_left := usubs_cons (mk_clos identity body) !long_left;
    long_right := usubs_cons (mk_clos identity body) !long_right
  done

let deep_left = ref identity
let deep_right = ref identity
let () =
  for _ = 1 to 3000 do
    deep_left := usubs_cons (mk_clos !deep_left nested) identity;
    deep_right := usubs_cons (mk_clos !deep_right nested) identity
  done

let shared_reduced = mk_clos identity (mkRel 1)
let shared_reduced_left = usubs_cons shared_reduced identity
let shared_reduced_right = usubs_cons shared_reduced identity

let bounded_callbacks =
  let left = ref (Esubst.subs_id 0) in
  let right = ref (Esubst.subs_id 0) in
  for i = 1 to 1000 do
    left := Esubst.subs_cons (ref i) !left;
    right := Esubst.subs_cons (ref i) !right
  done;
  let calls = ref 0 in
  let fuel = ref 8 in
  let result = Esubst.Internal.equal_bounded fuel
    (fun _ _ -> incr calls; true) !left !right in
  not result && !fuel >= 0 && !calls <= 8

let values_enabled = Sys.getenv_opt "ROCQ_CLOS_ENV_VALUES" <> Some "0"
let reduced_app term =
  let c = inject term in
  let infos = create_clos_infos RedFlags.betaiotazeta Environ.empty_env in
  let _ = whd_val infos (create_tab ()) c in c
let app_body = mkApp (mkRel 1, [|mkRel 2; mkRel 3|])
let app_left = reduced_app app_body
let app_right = reduced_app app_body
let app_other = reduced_app (mkApp (mkRel 1, [|mkRel 2; mkRel 4|]))
let app_env c = usubs_cons c identity
let app_shape c = match fterm_of c with FApp _ -> true | _ -> false
let lifted = mk_clos (usubs_liftn 2 (app_env (mk_clos identity body))) (mkRel 3)
let lifted_again = mk_clos (usubs_liftn 2 (app_env (mk_clos identity body))) (mkRel 3)
let lift_shape c = match fterm_of c with FLIFT _ -> true | _ -> false
let const_name = Names.Constant.make2
  (Names.ModPath.MPfile Names.DirPath.empty) (Names.Id.of_string "closure_test")
let const_env u = closure_env (mkConstU (const_name, u))
let var_name = Names.Id.of_string "closure_x"
let var_env = closure_env (mkVar var_name)
let app_short = reduced_app (mkApp (mkRel 1, [|mkRel 2|]))
let long_app_body = mkApp (mkRel 1, Array.make 1000 (mkRel 2))
let long_app_left = reduced_app long_app_body
let long_app_right = reduced_app long_app_body
let lifted_other = mk_clos
  (usubs_liftn 3 (app_env (mk_clos identity body))) (mkRel 4)
let tests = [
  mk_bool_test "closure-values-constant" "same constant and universe instance"
    (equal (const_env (snd (universe_env 0)))
           (const_env (snd (universe_env 0))) = values_enabled);
  mk_bool_test "closure-values-constant-universe" "constant instances must agree"
    (not (equal (const_env (snd (universe_env 0)))
                (const_env (snd (universe_env 1)))));
  mk_bool_test "closure-values-constant-quality" "constant qualities must agree"
    (not (equal (const_env (snd (quality_env Sorts.Quality.qprop)))
                (const_env (snd (quality_env Sorts.Quality.qtype)))));
  mk_bool_test "closure-values-named-variable" "same named variable"
    (equal var_env (closure_env (mkVar var_name)) = values_enabled);
  mk_bool_test "closure-values-different-name" "different named variables"
    (not (equal var_env (closure_env (mkVar (Names.Id.of_string "closure_y")))));
  mk_bool_test "closure-values-array-length" "application arity must agree"
    (not (equal (app_env app_left) (app_env app_short)));
  mk_bool_test "closure-values-array-budget" "array traversal respects shared fuel"
    (not (equal_usubs_bounded ~fuel:8
       (app_env long_app_left) (app_env long_app_right)));
  mk_bool_test "closure-values-unequal-delayed-lifts" "delayed shifts must agree"
    (not (equal (app_env lifted) (app_env lifted_other)));

  mk_bool_test "closure-values-app-shape" "fixture reaches reduced application"
    (app_shape app_left && app_shape app_right && app_left != app_right);
  mk_bool_test "closure-values-application" "equal reduced application components"
    (equal (app_env app_left) (app_env app_right) = values_enabled);
  mk_bool_test "closure-values-application-reification" "equal applications reify equally"
    (Constr.equal (term_of_fconstr app_left) (term_of_fconstr app_right));
  mk_bool_test "closure-values-application-negative" "different application arguments"
    (not (equal (app_env app_left) (app_env app_other)));
  mk_bool_test "closure-values-lift-shape" "fixture reaches matching delayed lifts"
    (lift_shape lifted && lift_shape lifted_again);
  mk_bool_test "closure-values-matching-lifts" "matching lifts with equal closures"
    (equal (app_env lifted) (app_env lifted_again) = values_enabled);
  mk_bool_test "closure-values-different-rel" "different reduced variables"
    (not (equal (closure_env (mkRel 1)) (closure_env (mkRel 2))));

  mk_bool_test "closure-env-separate-closures"
    "same body and separate closure cells"
    (requires_new_path left right && equal left right &&
     Constr.equal (reify left) (reify right));
  mk_bool_test "closure-env-nested"
    "nested shared bodies and equal environments"
    (requires_new_path nested_left nested_right && equal nested_left nested_right &&
     Constr.equal (reify nested_left) (reify nested_right));
  mk_bool_test "closure-env-different-body"
    "different substituted bodies leave equality unknown"
    (not (equal left (closure_env other_body)));
  mk_bool_test "closure-env-different-universe"
    "same substitution and distinct universe instances"
    (not (equal (universe_env 0) (universe_env 1)));
  mk_bool_test "closure-env-different-quality"
    "same substitution and distinct relevance qualities"
    (not (equal (quality_env Sorts.Quality.qprop)
                (quality_env Sorts.Quality.qtype)));
  mk_bool_test "closure-env-nested-universe"
    "universe differences inside substituted closures"
    (not (equal
      (usubs_cons (mk_clos (universe_env 0) body) identity)
      (usubs_cons (mk_clos (universe_env 1) body) identity)));
  mk_bool_test "closure-env-lift"
    "unequal substitution shifts leave equality unknown"
    (not (equal left (usubs_lift right)));
  mk_bool_test "closure-env-equal-lifts"
    "matching binder shifts preserve equality"
    (equal (usubs_liftn 3 left) (usubs_liftn 3 right));
  mk_bool_test "closure-env-budget-zero"
    "budget zero does not compare distinct environment trees"
    (not (equal_usubs_bounded ~fuel:0 left right));
  mk_bool_test "closure-env-budget-negative"
    "negative fuel cannot wrap into a large budget"
    (not (equal_usubs_bounded ~fuel:min_int left right));
  mk_bool_test "closure-env-budget-cap"
    "the public helper bounds deeply nested probes even with maximal fuel"
    (not (equal_usubs_bounded ~fuel:max_int !deep_left !deep_right));
  mk_bool_test "closure-env-shared-reduced"
    "existing physical equality remains valid at reduced payloads"
    (equal shared_reduced_left shared_reduced_right);
  mk_bool_test "closure-env-budget-long"
    "long equal environments return unknown at a small budget"
    (not (equal_usubs_bounded ~fuel:8 !long_left !long_right));
  mk_bool_test "closure-env-no-unbounded-retry"
    "substitution comparison stops without a repr fallback"
    bounded_callbacks;
  mk_bool_test "closure-env-reduced-cells"
    "identical reduced variable indices require value mode"
    (equal (closure_env (mkRel 1)) (closure_env (mkRel 1)) = values_enabled);
  mk_bool_test "closure-env-mixed-cells"
    "a reduced cell and an unreduced closure remain unknown"
    (not (equal left (closure_env (mkRel 1))));
]

let _ = run_tests __FILE__ log_out_ch tests
