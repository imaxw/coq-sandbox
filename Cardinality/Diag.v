Require Import Utf8.


Definition Surjective {A B} (f : A -> B) :=
  forall y, exists x, f x = y.


Section Cantor.

  Variable A : Type.
  Variable f : A -> (A -> bool).

  Definition diagb : A -> bool := λ x, negb (f x x).

  Theorem Cantor_Theorem : forall x, f x ≠ diagb.
  Proof.
    intros x Eq.
    assert (Eq': diagb x = f x x) by now rewrite Eq.
    unfold diagb in Eq'.
    now destruct (f x x).
  Qed.

  Corollary Cantor_Theorem_2 : ~Surjective f.
  Proof.
    firstorder using Cantor_Theorem.
  Qed.

End Cantor.
