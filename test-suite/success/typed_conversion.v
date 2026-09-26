Set Primitive Projections.

Definition alias (A : Set) := A.
Record Dep := dep { carrier : Set; action : carrier -> nat }.
Definition pair_a := dep nat (fun x : nat => x).
Definition pair_b := dep (alias nat) (fun x : alias nat => (fun y => y) x).
Definition pair_bad_body := dep nat (fun x : nat => S x).
Definition pair_bad_prefix := dep bool (fun _ : bool => 0).

Goal pair_a = pair_b.
Proof. now exact_no_check (eq_refl pair_a). Defined.

(** Bypass elaboration so these failures exercise kernel conversion. *)
Goal pair_a = pair_bad_body.
Proof. exact_no_check (eq_refl pair_a). Fail Defined. Abort.
Goal pair_a = pair_bad_prefix.
Proof. exact_no_check (eq_refl pair_a). Fail Defined. Abort.

Parameter f : nat -> nat.
Goal dep nat f = dep (alias nat) (fun x => f x).
Proof. now exact_no_check (eq_refl (dep nat f)). Defined.

Record Nested := nested { first : Set; later : forall x : first, first -> first }.
Definition nested_a := nested nat (fun _ x : nat => x).
Definition nested_b := nested (alias nat) (fun _ x : alias nat => (fun z => z) x).
Definition nested_bad := nested nat (fun x _ : nat => x).
Goal nested_a = nested_b.
Proof. now exact_no_check (eq_refl nested_a). Defined.
Goal nested_a = nested_bad.
Proof. exact_no_check (eq_refl nested_a). Fail Defined. Abort.

Inductive Strict : SProp := strict.
Record WithStrict := with_strict { witness : Strict; use_witness : Strict -> nat }.
Definition strict_a := with_strict strict (fun _ => 0).
Definition strict_b := with_strict strict (fun _ => (fun x => x) 0).
Definition strict_bad := with_strict strict (fun _ => 1).
Goal strict_a = strict_b.
Proof. now exact_no_check (eq_refl strict_a). Defined.
Goal strict_a = strict_bad.
Proof. exact_no_check (eq_refl strict_a). Fail Defined. Abort.

Polymorphic Inductive UBox@{u} : Type@{u+1} :=
  ubox : (Type@{u} -> nat) -> UBox.
Universe test_lo test_hi.
Constraint test_lo < test_hi.
Definition universe_a := ubox@{test_lo} (fun _ : Type@{test_lo} => 0).
Definition universe_b := ubox@{test_hi} (fun _ : Type@{test_hi} => 0).
Definition universe_alias :=
  ubox@{test_lo} (fun _ : Type@{test_lo} => (fun x => x) 0).
Goal universe_a = universe_alias.
Proof. now exact_no_check (eq_refl universe_a). Defined.

Parameter observe : forall A : Type, A -> Type.
Goal observe _ universe_a = observe _ universe_b.
Proof. exact_no_check (eq_refl (observe _ universe_a)). Fail Defined. Abort.

Definition domain_a := fun _ : nat => 0.
Definition domain_b := fun _ : bool => 0.
Goal observe _ domain_a = observe _ domain_b.
Proof. exact_no_check (eq_refl (observe _ domain_a)). Fail Defined. Abort.

Goal (nat -> nat) = (bool -> nat).
Proof. exact_no_check (eq_refl (nat -> nat)). Fail Defined. Abort.
