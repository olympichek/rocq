(* Tests for the [rewrite_bfs] tactic: like [rewrite], but the occurrence used
   to instantiate a pattern left-hand side is chosen by a breadth-first
   (shallowest-first) search that stops at the first match, instead of the
   default depth-first outermost-leftmost order. *)

Section Difference.
  Variable P : nat -> nat -> Prop.
  Variables f g : nat -> nat.
  Variables a b : nat.
  Hypothesis H : forall x, f x = x.

  (* The pattern [f ?x] matches [f a] deep inside the left argument (nested under
     two [g]s) and [f b] shallow in the right argument. Depth-first descends into
     the left argument and finds [f a]; breadth-first reaches the shallower [f b]
     first and stops there, without descending into the left nest. *)

  (* Default [rewrite] : depth-first, rewrites the deep [f a]. *)
  Goal P (g (g a)) (f b) -> P (g (g (f a))) (f b).
  Proof. intros h. rewrite H. exact h. Qed.

  (* [rewrite_bfs] : breadth-first, rewrites the shallow [f b]. *)
  Goal P (g (g (f a))) b -> P (g (g (f a))) (f b).
  Proof. intros h. rewrite_bfs H. exact h. Qed.

  (* The two tactics genuinely disagree on which occurrence is rewritten. *)
  Goal P (g (g (f a))) b -> P (g (g (f a))) (f b).
  Proof. intros h. Fail (rewrite H; exact h). rewrite_bfs H. exact h. Qed.
End Difference.

Section GroundAndClauses.
  Variable P : nat -> nat -> Prop.

  (* For a ground equation, [rewrite_bfs] behaves like [rewrite]: it rewrites
     every occurrence of the left-hand side. *)
  Goal forall c, c = 0 -> P 0 0 -> P c c.
  Proof. intros c e h. rewrite_bfs e. exact h. Qed.

  (* Rewriting in a hypothesis. *)
  Goal forall c, c = 0 -> P c c -> True.
  Proof. intros c e h. rewrite_bfs e in h. exact I. Qed.

  (* Right-to-left orientation, in a hypothesis. *)
  Goal forall c, c = 0 -> P 0 0 -> P c c.
  Proof. intros c e h. rewrite_bfs <- e in h. exact h. Qed.
End GroundAndClauses.
