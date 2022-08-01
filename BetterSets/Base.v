Require Export Relations Morphisms.

Require Import List.
Import ListNotations.

Set Primitive Projections.
Set Implicit Arguments.

Local Notation negate P := (fun x => ~P x).
Local Notation conjoin P Q := (fun x => P x /\ Q x).
Local Notation disjoin P Q := (fun x => P x \/ Q x).
Local Notation const x := (fun _ => x).
Local Notation "f ∘ g" := (fun x => f (g x)) (at level 30).

Module set.
  Section Basics.

    Variable V : Type.

    Record t := of { spec : (V -> Prop) }.

    Implicit Type a b c x y z : V.
    Implicit Type A B C X Y Z : t.

    Inductive elem x A : Prop := elem_ext : A.(spec) x -> elem x A.

    Definition eq A B := forall x, elem x A <-> elem x B.

    Definition subset A B := forall x, elem x A -> elem x B.

    Property eq_refl : Reflexive eq.
    Proof.
      unfold eq; intros A x.
      reflexivity.
    Qed.

    Property eq_sym : Symmetric eq.
    Proof.
      unfold eq; intros A B H1 x.
      specialize (H1 x).
      symmetry; assumption.
    Qed.

    Property eq_trans : Transitive eq.
    Proof.
      unfold  eq; intros A B C H1 H2 x.
      specialize (H1 x); specialize (H2 x).
      etransitivity; eassumption.
    Qed.

    Property subset_refl : Reflexive subset.
    Proof. cbv; auto. Qed.
    
    Property subset_trans : Transitive subset.
    Proof. cbv; auto. Qed.

    Global Add Relation t eq
      reflexivity proved by eq_refl
      symmetry proved by eq_sym
      transitivity proved by eq_trans
    as eq_rel.

    Global Add Relation t subset
      reflexivity proved by subset_refl
      transitivity proved by subset_trans
    as subset_rel.

    Property eq_subset A B : eq A B <-> subset A B /\ subset B A.
    Proof. cbv; do 2 split; apply H. Qed.

    Global Add Morphism elem : elem_morphism.
    Proof. intros x ? ? ?; revert x; assumption. Qed.

    Global Add Morphism subset : subset_morphism.
    Proof. 
      now_show (Proper (eq ==> eq ==> iff) subset).
      unfold subset; solve_proper.
    Qed.

    Definition empty := of (fun x => False).

    Definition full := of (fun x => True).

    Definition union A B := of (disjoin A.(spec) B.(spec)).

    Definition intersection A B := of (conjoin A.(spec) B.(spec)).

    Definition complement A := of (negate A.(spec)).

  End Basics.

End set.

Notation set := set.t.

Declare Scope set_scope.
Bind Scope set_scope with set.
Delimit Scope set_scope with set.

Notation "x ∈ A" := (set.elem x A) (at level 70, right associativity) : set_scope.
Notation "x ∉ A" := (~set.elem x A) (at level 70, right associativity) : set_scope.
Notation "A ∋ x" := (set.elem x A) (at level 71, left associativity, only parsing) : set_scope.
Notation "A ∌ x" := (~set.elem x A) (at level 71, left associativity, only parsing) : set_scope.
Notation "A ⊆ B" := (set.subset A B) (at level 70, right associativity) : set_scope.
Notation "A ⊈ B" := (~set.subset A B) (at level 70, right associativity) : set_scope.
Notation "B ⊇ A" := (set.subset A B) (at level 71, left associativity, only parsing) : set_scope.
Notation "B ⊉ A" := (~set.subset A B) (at level 71, left associativity, only parsing) : set_scope.
Notation "A == B" := (set.eq A B) (at level 70, no associativity) : set_scope.
Notation "A =/= B" := (~set.eq A B) (at level 70, no associativity) : set_scope.
Notation "∅" := (set.empty _) : set_scope.
Notation "[ X ]" := (set.full X) : set_scope.
Notation "A ∪ B" := (set.union A B) (at level 50, left associativity) : set_scope.
Notation "A ∩ B" := (set.intersection A B) (at level 40, left associativity) : set_scope.
Notation "- A" := (set.complement A) : set_scope.
