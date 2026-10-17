open Utest
open Constr

let log_out_ch = open_log_out_ch __FILE__
let annot = Context.make_annot Names.Name.Anonymous Sorts.Relevant
let level n = Univ.Level.make (Univ.UGlobal.make Names.DirPath.empty "inference_cache" n)
let a, b, top = level 0, level 1, level 2
let sort l = mkSort (Sorts.sort_of_univ (Univ.Universe.make l))
let required = Univ.UnivConstraints.singleton (a, Univ.UnivConstraint.Eq, b)

let graph =
  let g = List.fold_left (fun g l -> UGraph.add_universe l ~strict:false g)
    UGraph.initial_universes [a; b; top] in
  UGraph.merge_constraints (List.fold_left (fun s c -> Univ.UnivConstraints.add c s)
    Univ.UnivConstraints.empty
    [a, Univ.UnivConstraint.Lt, top; b, Univ.UnivConstraint.Lt, top]) g

let constant s =
  Names.Constant.make2 (Names.ModPath.MPfile Names.DirPath.empty)
    (Names.Id.of_string s)
let f, k = constant "cache_F", constant "cache_K"

let declaration env body ty = {
  Declarations.const_hyps = [];
  const_univ_hyps = UVars.Instance.empty;
  const_body = body;
  const_type = ty;
  const_relevance = Sorts.Relevant;
  const_body_code = Vmemitcodes.BCuncompiled;
  const_universes = Declarations.Monomorphic;
  const_inline_code = false;
  const_typing_flags = Environ.typing_flags env;
  const_def_height = None;
}
let reference c = mkConstU (c, UVars.Instance.empty)

let env =
  let open Context.Rel.Declaration in
  let env = Environ.set_universes graph Environ.empty_env in
  let ty = mkProd (annot, sort top, sort top) in
  ignore (Typeops.infer env ty);
  let env = Environ.add_constant f (declaration env (Declarations.Undef None) ty) env in
  (* K (flag : Prop) (A : Type@top) ignores flag and returns opaque F A. *)
  let body = mkLambda (annot, mkProp,
    mkLambda (annot, sort top, mkApp (reference f, [|mkRel 1|]))) in
  let ty = (Typeops.infer env body).Environ.uj_type in
  let env = Environ.add_constant k (declaration env (Declarations.Def body) ty) env in
  let env = Environ.push_rel (LocalAssum (annot, mkProp)) env in
  Environ.push_rel (LocalAssum (annot, mkProp)) env

let p, q = mkRel 2, mkRel 1
let apply flag ty = mkApp (reference k, [|flag; ty|])
let ta, tb = sort a, sort b
let left, right = apply p ta, apply q tb
let nested_left, nested_right = apply p left, apply q right
let sigma = Evd.from_env env

let () =
  assert (not (UGraph.check_constraints required graph));
  List.iter (fun t -> ignore (Typeops.infer env t))
    [left; right; nested_left; nested_right]

let comparer = {
  Conversion.compare_sorts = (fun _ x y s ->
    Ok (UnivProblem.Set.add (UnivProblem.UEq (x, y)) s));
  compare_instances = (fun ~flex u v s ->
    Ok (UnivProblem.enforce_eq_instances_univs flex u v s));
  compare_cumul_instances = (fun pb variance u v s ->
    Ok (UnivProblem.compare_cumulative_instances pb variance u v s));
  compare_irrelevant = true;
}

let obligation =
  UnivProblem.UEq (Sorts.sort_of_univ (Univ.Universe.make a),
    Sorts.sort_of_univ (Univ.Universe.make b))

let generic initial l r =
  match Conversion.generic_conv Conversion.CONV ~l2r:false
    TransparentState.full env (initial, comparer) l r with
  | Ok s -> UnivProblem.Set.equal (UnivProblem.Set.add obligation initial) s
  | Error _ -> false

let arbitrary_comparer () =
  let log = {
    Conversion.compare_sorts = (fun _ x y s -> Ok ((x, y) :: s));
    compare_instances = (fun ~flex:_ _ _ s -> Ok s);
    compare_cumul_instances = (fun _ _ _ _ s -> Ok s);
    compare_irrelevant = true;
  } in
  match Conversion.generic_conv Conversion.CONV ~l2r:false
    TransparentState.full env ([], log) left right with
  | Ok [_] -> true
  | _ -> false

let inferred l r =
  match Reductionops.infer_conv ~pb:Conversion.CONV env sigma
    (EConstr.of_constr l) (EConstr.of_constr r) with
  | Some s -> UGraph.check_constraints required (Evd.universes s)
  | None -> false

(* Congruence compares the physically shared ta/tb pair, then rejects p/q.
   FFlex delta fallback drops that speculative state and reaches the same
   pair in K's opaque application. A Boolean hit must not lose the
   required equality. *)
let tests = [
  mk_bool_test "inference-cache-rollback" "frontend preserves rolled-back equality"
    (inferred left right);
  mk_bool_test "inference-cache-nested" "nested fallbacks preserve equality"
    (inferred nested_left nested_right);
  mk_bool_test "inference-cache-generic" "custom generic accumulation is correct"
    (generic UnivProblem.Set.empty left right);
  mk_bool_test "inference-cache-arbitrary"
    "arbitrary comparers keep their returned state"
    (arbitrary_comparer ());
  mk_bool_test "inference-cache-seeded" "duplicate obligations survive fallback"
    (generic (UnivProblem.Set.singleton obligation) nested_left nested_right);
]

let () = run_tests __FILE__ log_out_ch tests
