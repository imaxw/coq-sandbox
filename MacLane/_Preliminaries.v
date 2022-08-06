Require Export ProofIrrelevance FunctionalExtensionality.

Require Export CRelationClasses CMorphisms RelationClasses Morphisms Program.

#[export] Set Universe Polymorphism.
#[export] Set Polymorphic Inductive Cumulativity.
#[export] Set Primitive Projections.
#[export] Set Implicit Arguments.

Reserved Notation "A → B" (at level 99, right associativity, B at level 200).
Reserved Notation "f ⋅ g" (at level 40, left associativity).
Reserved Notation "A *" (at level 10, no associativity).
Reserved Notation "f ⁻¹" (at level 10, no associativity).
Reserved Notation "A ≅ B" (at level 70, no associativity).
Reserved Notation "A ≃ B" (at level 70, no associativity).

Notation refl := (eq_refl _).

Definition notT_Empty_set := Empty_set_ind _ : notT (Empty_set).

#[export] Hint Resolve notT_Empty_set : core.
#[export] Hint Resolve functional_extensionality : core.
#[export] Hint Resolve functional_extensionality_dep : core.
#[export] Hint Immediate proof_irrelevance : core.

#[global] Declare Scope category_scope.

#[global] Create HintDb categories.
