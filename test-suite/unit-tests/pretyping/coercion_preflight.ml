open Utest
open Constr

let log_out_ch = open_log_out_ch __FILE__
let annot = Context.make_annot Names.Name.Anonymous Sorts.Relevant
let level n = Univ.Level.make (Univ.UGlobal.make Names.DirPath.empty "preflight" n)
let a, b, top = level 0, level 1, level 2
let sort l = mkSort (Sorts.sort_of_univ (Univ.Universe.make l))
let graph =
  let g = List.fold_left (fun g l -> UGraph.add_universe l ~strict:false g)
    UGraph.initial_universes [a; b; top] in
  UGraph.merge_constraints (List.fold_left (fun s c -> Univ.UnivConstraints.add c s)
    Univ.UnivConstraints.empty
    [a, Univ.UnivConstraint.Lt, top; b, Univ.UnivConstraint.Lt, top]) g
let env = Environ.set_universes graph Environ.empty_env
let sigma = Evd.from_env env
let e = EConstr.of_constr
let assume ty env =
  Environ.push_rel (Context.Rel.Declaration.LocalAssum (annot, ty)) env
let judgment env value =
  let j = Typeops.infer env value in
  { Environ.uj_val = e j.Environ.uj_val; uj_type = e j.Environ.uj_type }
let coerce known ?loc ?flags env sigma j expected =
  let api = if known then Coercion.inh_conv_coerce_to_known_types
    else Coercion.inh_conv_coerce_to in
  api ?loc ~program_mode:false ~resolve_tc:false env sigma ?flags j expected
let both test = List.for_all (fun known -> try test known with _ -> false) [false; true]

let ground known =
  let env = assume mkProp env in
  let j = judgment env (mkRel 1) in
  let expected = e (mkApp (mkLambda (annot, sort top, mkRel 1), [|mkProp|])) in
  let result, j', _ = coerce known env sigma j expected in
  (* The legacy path may allocate an equivalent map; checked success must
     preserve the original map as well as the value. *)
  (not known || result == sigma)
  && Univ.ContextSet.equal (Evd.universe_context_set result)
       (Evd.universe_context_set sigma)
  && EConstr.eq_constr result j.Environ.uj_val j'.Environ.uj_val

let new_universe known =
  let required = Univ.UnivConstraints.singleton (a, Univ.UnivConstraint.Le, b) in
  assert (not (UGraph.check_constraints required graph));
  let env = assume (sort a) env in
  let result, _, _ = coerce known env sigma (judgment env (mkRel 1)) (e (sort b)) in
  UGraph.check_constraints required (Evd.universes result)

let quality_problem () =
  let sigma, q = Evd.new_quality_variable sigma in
  let env = Environ.set_qualities (Evd.elim_graph sigma) env in
  let qsort = mkSort (Sorts.vsort q (Univ.Universe.make a)) in
  let env = assume (mkProd (annot, sort top, sort top)) env in
  let inferred = mkApp (mkRel 1, [|qsort|]) in
  ignore (Typeops.infer env inferred);
  let env = assume inferred env in
  let expected = e (mkApp (mkRel 2, [|sort a|])) in
  env, sigma, q, judgment env (mkRel 1), expected

let quality_equal sigma q =
  (Evd.evar_handler sigma).CClosure.qual_equal
    (Sorts.Quality.QVar q) Sorts.Quality.qtype

let new_quality known =
  let env, sigma, q, j, expected = quality_problem () in
  assert (not (quality_equal sigma q));
  let result, _, _ = coerce known env sigma j expected in
  quality_equal result q

let existing_quality known =
  let env, sigma, q, j, expected = quality_problem () in
  let sigma, _, _ = coerce false env sigma j expected in
  assert (quality_equal sigma q);
  let result, _, _ = coerce known env sigma j expected in
  (not known || result == sigma) && quality_equal result q

let solve_evar known =
  let sigma, ty = Evarutil.new_evar env sigma (e (sort top)) in
  let sigma, value = Evarutil.new_evar env sigma ty in
  let j = { Environ.uj_val = value; uj_type = ty } in
  let result, j', _ = coerce known env sigma j (e mkProp) in
  EConstr.eq_constr result ty (e mkProp)
  && EConstr.eq_constr result value j'.Environ.uj_val

(* Defensive compatibility on this deliberately unsafe input, not a typing
   guarantee for arbitrary judgments. An identical meta pair can also pass
   a structural shortcut, so this does not isolate guard execution. *)
let meta_compatibility () =
  let meta = EConstr.mkMeta (Evarutil.new_meta ()) in
  let j = { Environ.uj_val = e (mkRel 1); uj_type = meta } in
  let env = assume mkProp env in
  both (fun known ->
    let result, j', _ = coerce known env sigma j meta in
    EConstr.eq_constr result meta j'.Environ.uj_type
    && EConstr.eq_constr result j.Environ.uj_val j'.Environ.uj_val
    && Evarutil.has_undefined_evars_or_metas result j'.Environ.uj_type)


let flags_compatibility () =
  let env = assume mkProp env in
  let j = judgment env (mkRel 1) in
  let expected = e (mkApp (mkLambda (annot, sort top, mkRel 1), [|mkProp|])) in
  let flags = { (Evarconv.default_flags_of TransparentState.full) with modulo_betaiota = false;
    open_ts = TransparentState.empty; closed_ts = TransparentState.empty } in
  let attempt known =
    try ignore (coerce known ~flags env sigma j expected); true
    with Pretype_errors.PretypeError _ -> false in
  attempt false = attempt true

let transparency_and_location known =
  let name = Names.Constant.make2 (Names.ModPath.MPfile Names.DirPath.empty)
    (Names.Id.of_string "preflight_alias") in
  let body = mkProp in
  let ty = (Typeops.infer env body).Environ.uj_type in
  let declaration = {
    Declarations.const_hyps = [];
    const_univ_hyps = UVars.Instance.empty;
    const_body = Declarations.Def body;
    const_type = ty;
    const_relevance = Sorts.Relevant;
    const_body_code = Vmemitcodes.BCuncompiled;
    const_universes = Declarations.Monomorphic;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
  } in
  let env = Environ.add_constant name declaration env in
  let env = assume (mkConstU (name, UVars.Instance.empty)) env in
  let j = judgment env (mkRel 1) in
  ignore (coerce known env sigma j (e mkProp));
  let flags = Evarconv.default_flags_of TransparentState.empty in
  let loc = Loc.make_loc (3, 8) in
  try ignore (coerce known ~loc ~flags env sigma j (e mkProp)); false
  with Pretype_errors.PretypeError _ as exn ->
    let _, info = Exninfo.capture exn in
    match Loc.get_loc info with
    | Some actual -> Loc.unloc actual = Loc.unloc loc
    | None -> false

(* Equality in the graph is not an assignment of a flexible level. Both
   APIs must preserve unification's normalization side effect, including
   when a beta redex prevents the cheap structural comparison. *)
let flexible_equality beta known =
  let u, v = level 3, level 4 in
  let equality = Univ.UnivConstraints.singleton (u, Univ.UnivConstraint.Eq, v) in
  let constraints = List.fold_left (fun s c -> Univ.UnivConstraints.add c s)
    equality [u, Univ.UnivConstraint.Lt, top; v, Univ.UnivConstraint.Lt, top] in
  let levels = Univ.Level.Set.add u (Univ.Level.Set.singleton v) in
  let sigma = Evd.merge_universe_context_set UState.univ_flexible
    (Evd.from_env env) (levels, constraints) in
  let env = Environ.set_universes (Evd.universes sigma) env in
  let name = Names.Constant.make2 (Names.ModPath.MPfile Names.DirPath.empty)
    (Names.Id.of_string "preflight_flexible") in
  let ty = mkProd (annot, sort top, sort top) in
  ignore (Typeops.infer env ty);
  let declaration = {
    Declarations.const_hyps = [];
    const_univ_hyps = UVars.Instance.empty;
    const_body = Declarations.Undef None;
    const_type = ty;
    const_relevance = Sorts.Relevant;
    const_body_code = Vmemitcodes.BCuncompiled;
    const_universes = Declarations.Monomorphic;
    const_inline_code = false;
    const_typing_flags = Environ.typing_flags env;
  } in
  let env = Environ.add_constant name declaration env in
  let apply arg = mkApp (mkConstU (name, UVars.Instance.empty), [|arg|]) in
  let argument = if beta then
    mkApp (mkLambda (annot, sort top, mkRel 1), [|sort u|]) else sort u in
  let actual, expected = apply argument, apply (sort v) in
  List.iter (fun ty -> ignore (Typeops.infer env ty)) [actual; expected];
  let normalized_equal sigma =
    Univ.Universe.equal
      (UState.nf_universe (Evd.ustate sigma) (Univ.Universe.make u))
      (UState.nf_universe (Evd.ustate sigma) (Univ.Universe.make v)) in
  assert (UGraph.check_constraints equality (Evd.universes sigma));
  assert (not (normalized_equal sigma));
  let env = assume actual env in
  let j = judgment env (mkRel 1) in
  if beta then
    assert (EConstr.leq_constr_universes env sigma j.Environ.uj_type
      (e expected) = None);
  let result, j', _ = coerce known env sigma j (e expected) in
  normalized_equal result
  && EConstr.eq_constr result j.Environ.uj_val j'.Environ.uj_val

let tests = [
  mk_bool_test "preflight-ground" "ground conversion preserves state and value"
    (both ground);
  mk_bool_test "preflight-universe" "new universe obligations are inferred"
    (both new_universe);
  mk_bool_test "preflight-quality" "new quality obligations are inferred"
    (both new_quality);
  mk_bool_test "preflight-existing-quality"
    "checked success uses the existing quality equality without new state"
    (both existing_quality);
  mk_bool_test "preflight-evar" "term evars are solved by the original path"
    (both solve_evar);
  mk_bool_test "preflight-meta" "meta inputs preserve legacy compatibility"
    (meta_compatibility ());
  mk_bool_test "preflight-transparency-location"
    "opaque conversion rejects with the original error location"
    (both transparency_and_location);
  mk_bool_test "preflight-flexible-equality"
    "entailed flexible equality is assigned, not only graph-checked"
    (both (flexible_equality false));
  mk_bool_test "preflight-flexible-beta"
    "beta conversion still assigns an entailed flexible equality"
    (both (flexible_equality true));
  mk_bool_test "preflight-flags" "supplied reduction flags preserve legacy behavior"
    (flags_compatibility ());
]

let () = run_tests __FILE__ log_out_ch tests
