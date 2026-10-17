Set Primitive Projections.
Record Wrapper := wrap { unwrap : nat }.
Coercion unwrap : Wrapper >-> nat.

Definition ground_conversion : nat := (fun n => n) 0.
Definition inserted_coercion (x : Wrapper) : nat := x.
Definition product_coercion (f : nat -> Wrapper) : nat -> nat := f.
Example inserted_coercion_computes : inserted_coercion (wrap 3) = 3 := eq_refl.
Example product_coercion_computes :
  product_coercion (fun n => wrap n) 3 = 3 := eq_refl.

Definition unresolved_argument : exists n : nat, n = 0.
Proof. eexists. now reflexivity. Defined.
Parameter observe : forall A : Type, A -> Type.
Definition dependent_evars : exists A : Type, exists x : A,
  observe A x = observe nat 0.
Proof. do 2 eexists. now reflexivity. Defined.

(* Neither level is initially constrained; elaboration must record a < b. *)
Universe a b.
Definition new_universe_obligation : Type@{b} := Type@{a}.

Class Choice := { chosen : Type }.
#[local] Instance nat_choice : Choice := {| chosen := nat |}.
Definition typeclass_conversion : @chosen _ := 0.

Definition hidden (n : nat) := n.
Definition transparent_accepted : hidden 0 = 0 := eq_refl.

Fail Definition wrong_type : bool := (0 : nat).
Goal False.
Proof.
  exact_no_check I.
Fail Defined.
Abort.
Print Assumptions ground_conversion.
Print Assumptions product_coercion.

From Corelib Require Import Setoid CMorphisms.

(* Graph equality alone does not replace assignments of flexible universes.
   Leaving those assignments unresolved breaks later relation inference. *)
Section FlexibleUniverses.
  Context (A : Set) (R : A -> A -> Prop) (f : A -> Set).
  Context (PF : CMorphisms.Proper
    (CMorphisms.respectful R CRelationClasses.iffT) f).

  Definition inferred_relation :
    { rel : CRelationClasses.crelation (A -> Set) & CMorphisms.Proper rel f }.
  Proof. eexists. now exact PF. Defined.

  Context (ER : CRelationClasses.Equivalence R).
  #[local] Existing Instances ER PF.

  Lemma rewrite_set_valued x x' : R x x' -> f x -> f x'.
  Proof. intros H H0. now rewrite H in H0. Qed.
End FlexibleUniverses.
