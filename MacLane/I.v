Require Import RelationClasses Morphisms Program.

Require Import ProofIrrelevance FunctionalExtensionality.

Set Primitive Projections.
Set Implicit Arguments.
Generalizable All Variables.

Notation refl := (eq_refl _).

Definition notT_Empty_set := Empty_set_ind _ : notT (Empty_set).
Local Hint Resolve notT_Empty_set : core.

Create HintDb categories.
Global Hint Resolve functional_extensionality : categories.
Global Hint Resolve functional_extensionality_dep : categories.
Global Hint Resolve proof_irrelevance : categories.

#[universes(polymorphic, cumulative)]
Record Category@{u0 u1} :=
{
  (* data *)
  Obj :> Type@{u0} ;
  Hom (A B : Obj) : Type@{u1} ;
  compose (A B C : Obj) : Hom B C -> Hom A B -> Hom A C ;
  id (A : Obj) : Hom A A ;

  (* axioms *)
  compose_assoc [A B C D] (f : Hom C D) (g : Hom B C) (h : Hom A B) :
    compose f (compose g h) = compose (compose f g) h;
  compose_id_left [A B] (f : Hom A B) : compose (id B) f = f;
  compose_id_right [A B] (f : Hom A B) : compose f (id A) = f
}.

Arguments Hom {_} _ _.
Arguments compose {_ _ _ _} _ _.
Arguments id {_} _.
Global Opaque compose_assoc compose_id_left compose_id_right.
Global Hint Resolve compose_assoc : categories.
Global Hint Resolve compose_id_left : categories.
Global Hint Resolve compose_id_right : categories.
Global Hint Rewrite -> compose_id_left : categories.
Global Hint Rewrite -> compose_id_right : categories.


Declare Scope category_scope.
Bind Scope category_scope with Category Obj Hom.
Delimit Scope category_scope with cat.

Notation "A → B" := (Hom A B)
(at level 99, right associativity, B at level 200): category_scope.
Notation "f ∘ g" := (compose f g) : category_scope.
Notation "1" := (id _) : category_scope.

Local Open Scope category_scope.


Section Very_Small_Categories.

  #[canonical, program]
  Definition EmptyCategory : Category@{Set Set} :=
  {|
    Obj := Empty_set : Set ;
    Hom A B := Empty_set_rect _ A
  |}.
  Solve All Obligations with contradiction.

  #[canonical, program]
  Definition UnitCategory : Category@{Set Set} :=
  {|
    Obj := unit : Set ;
    Hom x y := True 
  |}.
  Solve All Obligations with (destruct f; reflexivity).

  #[canonical, program]
  Definition BoolCategory : Category@{Set Set} :=
  {|
    Obj := bool : Set ;
    Hom (x y : bool) := (implb x y = true)
  |}.
  Solve All Obligations with (Bool.destr_bool; apply proof_irrelevance).

End Very_Small_Categories.


#[universes(polymorphic), canonical]
Definition TypeCategory : Category :=
  {| Obj := Type ;
     Hom A B := forall _ : A, B ;
     compose _ _ _ f g x := f (g x) ;
     id _ x := x ;
     compose_assoc _ _ _ _ _ _ _ := refl ;
     compose_id_left _ _ _ := refl ;
     compose_id_right _ _ _ := refl |}.


Section More_Example_Categories.

  Program Example PreOrderCategory `(preo : PreOrder A R) :=
  {|
    Obj := A ;
    Hom x y := R x y ;
    compose _ _ _ f g := transitivity g f ;
    id := reflexivity
  |}.
  Solve All Obligations with (intros; apply proof_irrelevance).

  Program Example IndiscreteCategory A :=
  {|
    Obj := A ;
    Hom x y := unit ;
    compose _ _ _ _ _ := tt ;
    id _ := tt
  |}.
  Solve All Obligations with (destruct f; reflexivity).

  Program Example DiscreteCategory A :=
  {|
    Obj := A ;
    Hom := eq ;
    compose _ _ _ _ _ := refl;
    id _ := refl
  |}.

End More_Example_Categories.


#[universes(polymorphic), program]
Definition OppositeCategory@{u v} (𝐂 : Category@{u v}) : Category@{u v} :=
{|
  Obj := Obj 𝐂 ;
  Hom A B := 𝐂.(Hom) B A ;
  compose _ _ _ f g := 𝐂.(compose) g f ;
  id A := 1
|}.
Next Obligation. apply eq_sym, compose_assoc. Qed.
Next Obligation. apply compose_id_right. Qed.
Next Obligation. apply compose_id_left. Qed.

Notation "𝐂 *" := (OppositeCategory 𝐂)
(at level 0, no associativity) : category_scope.


Section Arrows.

  Variable 𝐂 : Category.
  Variables X Y : Obj 𝐂.

  Definition Retract (f : X → Y) (g : Y → X) := g ∘ f = 1.
  Definition Section (f : X → Y) (g : Y → X) := f ∘ g = 1.
  Definition Inverse (f : X → Y) (g : Y → X) :=
    Retract f g /\ Section f g.

  #[universes(polymorphic)]
  Class Retractible (f : X → Y) := {
    retract : Y → X ;
    retract_property : Retract f retract
  }.

  #[universes(polymorphic)]
  Class Sectionable (f : X → Y) := {
    section : Y → X ;
    section_property : Section f section
  }.

  #[universes(polymorphic)]
  Class Isomorphism (f : X → Y) := {
    inverse : Y → X ;
    inverse_property : Inverse f inverse
  }.


  Lemma Isomorphism_unique f {iso : Isomorphism f} :
    forall g : Y → X, Inverse f g -> inverse = g.
  Proof.
    intros g H. destruct iso as [g' H']; simpl.
    now rewrite
      <- compose_id_right,
      <- (proj2 H'),
      -> compose_assoc,
      -> (proj1 H),
      -> compose_id_left.
  Qed.

  Class Monic (f : X → Y) :=
    rcancel : forall D (g g' : D → X), f ∘ g = f ∘ g' -> g = g'.

  Class Epic (f : X → Y) :=
    lcancel : forall C (g g' : Y → C), g ∘ f = g' ∘ f -> g = g'.

  Global Instance Retractible_Monic `{Retractible f} : Monic f.
  Proof.
    intros D g g' Eq.
    apply (f_equal (compose retract)) in Eq.
    now repeat
      (rewrite compose_assoc, retract_property, compose_id_left in Eq).
  Qed.

  Global Instance Sectionable_Epic `{Sectionable f} : Epic f.
  Proof.
    intros C g g' Eq.
    apply (f_equal (fun x => compose x section)) in Eq.
    now repeat
      (rewrite <- compose_assoc, section_property, compose_id_right in Eq).
  Qed.
  
  Global Instance Isomorphism_Retractible `{Isomorphism f} : Retractible f :=
  {|
    retract := inverse ;
    retract_property := proj1 inverse_property
  |}.

  Global Instance Isomorphism_Sectionable `{Isomorphism f} : Sectionable f :=
  {|
    section := inverse ;
    section_property := proj2 inverse_property
  |}.

  #[universes(polymorphic)]
  Class Isomorphic :=
  {
    isomorphism : X → Y ;
    isomorphism_property :> Isomorphism isomorphism
  }.

End Arrows.

Arguments Retractible {_} [_ _] f.
Arguments Sectionable {_} [_ _] f.
Arguments Isomorphism {_} [_ _] f.

Notation "f ⁻¹" := (inverse f) (at level 0) : category_scope.
Notation "A ≅ B" := (Isomorphic A B) (at level 70, no associativity) : category_scope.

Definition Groupoid (𝐂 : Category) :=
  forall (X Y : 𝐂) (f : X → Y), Isomorphism f.


Section Special_Objects.

  Variable 𝐂 : Category.

  Class HasTerminal := {
    terminal_object : 𝐂 ;
    terminal_arrow {D : 𝐂} : D → terminal_object ;
    terminal_arrow_unique [D : 𝐂] : forall f : D → terminal_object, terminal_arrow = f
  }.

  Class HasInitial := {
    initial_object : 𝐂 ;
    initial_arrow {C : 𝐂} : initial_object → C ;
    initial_arrow_unique [C : 𝐂] : forall f : initial_object → C, initial_arrow = f
  }.

  Class HasNull := {
    null_object : 𝐂 ;
    null_arrow_in {D : 𝐂} : D → null_object ;
    null_arrow_in_unique [D : 𝐂] : forall f : D → null_object, null_arrow_in = f ;
    null_arrow_out {C : 𝐂} : null_object → C ;
    null_arrow_out_unique [C : 𝐂] : forall f : null_object → C, null_arrow_out = f
  }.

  Global Instance Null_Terminal `(HasNull) : HasTerminal :=
  {| terminal_object := null_object ;
     terminal_arrow D := null_arrow_in ;
     terminal_arrow_unique := null_arrow_in_unique |}.

  Global Instance Null_Initial `(HasNull) : HasInitial :=
  {| initial_object := null_object ;
     initial_arrow C := null_arrow_out ;
     initial_arrow_unique := null_arrow_out_unique |}.

  Definition zero `{Hnull : HasNull} {A B : 𝐂} : A → B
    := null_arrow_out ∘ null_arrow_in.

End Special_Objects.


#[universes(polymorphic)]
Record Functor (𝐂 : Category) (𝐃 : Category) :=
{
  map₀ :> Obj 𝐂 -> Obj 𝐃 ;
  map [A B] : Hom A B -> Hom (map₀ A) (map₀ B) ;

  id_compat A : map (id A) = 1 ;
  compose_compat [A B C] (f : Hom B C) (g : Hom A B) :
    map (f ∘ g) = (map f) ∘ (map g)
}.

Global Opaque id_compat compose_compat.
Arguments map {_ _} _ [_ _] _.

Global Hint Resolve id_compat : categories.
Global Hint Resolve compose_compat : categories.
Global Hint Rewrite -> id_compat : categories.
Global Hint Rewrite -> compose_compat : categories.

Notation "𝐂 ==> 𝐃" := (Functor 𝐂 𝐃) : category_scope.

Module Functor.
  Section Equality.
    Variables 𝐂 𝐃 : Category.
    Variables F G : 𝐂 ==> 𝐃.

    Hypothesis Heq₀ : forall X : Obj 𝐂, F.(map₀) X = G.(map₀) X.

    Let obj_eq_rect `(f : Hom X Y) :
    Hom (map₀ G X) (map₀ G Y) -> Hom (map₀ F X) (map₀ F Y).
      intro Gf.
      rewrite <- (Heq₀ X), <- (Heq₀ Y) in Gf.
      exact Gf.
    Defined.

    Hypothesis Heq₁ : forall `(f : Hom X Y),
      F.(map) f = obj_eq_rect f (G.(map) f).
    
    Proposition extensionality : F = G.
    Proof.
      case F as [F₀ F₁ F₂ F₃], G as [G₀ G₁ G₂ G₃]; simpl in *.
      assert (Eq₀ : F₀ = G₀).
      { apply functional_extensionality; assumption. }
      destruct Eq₀. subst obj_eq_rect.
      assert (E : (fun x => refl) = Heq₀). { apply proof_irrelevance. }
      destruct E; clear G; unfold Datatypes.id in Heq₁.
      assert (Eq₁ : F₁ = G₁).
      { repeat (apply functional_extensionality_dep; intro).
        apply Heq₁. }
      destruct Eq₁.
      assert (Eq₂ : F₂ = G₂). { apply proof_irrelevance. }
      assert (Eq₃ : F₃ = G₃). { apply proof_irrelevance. }
      destruct Eq₂, Eq₃.
      reflexivity.
    Qed.
  End Equality.

  Program Definition compose `(F : 𝐁 ==> 𝐂) `(G : 𝐀 ==> 𝐁) : 𝐀 ==> 𝐂 :=
  {|
    map₀ A := F (G A) ;
    map _ _ f := map F (map G f)
  |}.
  Next Obligation. repeat rewrite id_compat; reflexivity. Qed.
  Next Obligation.  repeat rewrite compose_compat; reflexivity. Qed.

  Program Definition id {𝐂 : Category} : 𝐂 ==> 𝐂 := 
  {|
    map₀ A := A ;
    map _ _ f := f
  |}.

  Lemma compose_assoc [𝐀 𝐁 𝐂 𝐃] (F: 𝐂 ==> 𝐃) (F' : 𝐁 ==> 𝐂) (F'' : 𝐀 ==> 𝐁) :
    compose F (compose F' F'') = compose (compose F F') F''.
  Proof.
    eapply (extensionality _ _ ?[Heq₀]).
    [Heq₀] : reflexivity.
    reflexivity.
  Qed.

  Lemma compose_id_left [𝐂 𝐃] (F : 𝐂 ==> 𝐃) : compose id F = F.
  Proof.
    eapply (extensionality _ _ ?[Heq₀]).
    [Heq₀] : reflexivity.
    reflexivity.
  Qed.

  Lemma compose_id_right [𝐂 𝐃] (F : 𝐂 ==> 𝐃) : compose F id = F.
  Proof.
    eapply (extensionality _ _ ?[Heq₀]).
    [Heq₀] : reflexivity.
    reflexivity.
  Qed.

End Functor.

Global Hint Resolve Functor.compose_assoc : categories.
Global Hint Resolve Functor.compose_id_left : categories.
Global Hint Resolve Functor.compose_id_right : categories.
Global Hint Rewrite -> Functor.compose_assoc : categories.
Global Hint Rewrite -> Functor.compose_id_left : categories.
Global Hint Rewrite -> Functor.compose_id_right : categories.

#[universes(polymorphic), canonical]
Definition CategoryCategory : Category :=
{|
  Obj := Category ;
  Hom A B := Functor A B ;
  compose _ _ _ f g := Functor.compose f g ;
  id A := Functor.id ;
  compose_assoc := @Functor.compose_assoc ;
  compose_id_left := @Functor.compose_id_left ;
  compose_id_right := @Functor.compose_id_right
|}.

#[universes(polymorphic)]
Definition HomFunctor [𝐂 : Category] (A : Obj 𝐂) : 𝐂 ==> TypeCategory :=
{|
  map₀ := Hom A;
  map _ _ f := fun α => f ∘ α ;
  id_compat _ := functional_extensionality _ _ (fun f => compose_id_left 𝐂 f);
  compose_compat X Y Z f g :=
    functional_extensionality _ _ (fun α => symmetry (compose_assoc _ f g α))
|}.


Class Full `(F : 𝐂 ==> 𝐃) :=
  fullness :
  forall (X Y : Obj 𝐂) (g : Hom (F X) (F Y)),
  exists f : Hom X Y, g = map _ f.

Class Faithful `(F : 𝐂 ==> 𝐃) :=
  faithfulness:
  forall (X Y : Obj 𝐂) (f₁ f₂ : Hom X Y),
  (map F f₁ = map F f₂) -> f₁ = f₂.

#[universes(polymorphic)]
Class Natural [𝐂 𝐃 : Category] [F G : Functor 𝐂 𝐃]
     (τ : forall X : 𝐂, Hom (F X) (G X)) :=
  naturality : forall `(f : Hom X Y), (map G f) ∘ τ X = τ Y ∘ (map F f).

#[universes(polymorphic, cumulative)]
Record NaturalTransformation [𝐂 𝐃 : Category] (F G : Functor 𝐂 𝐃) := mk_nt
{
  transformation :> forall X, Hom (F X) (G X) ;
  transformation_natural :> Natural transformation
}.
Arguments mk_nt [_ _ _ _] _ _.

Module Natural.

  Lemma extensionality [𝐂 𝐃 : Category] [F G : 𝐂 ==> 𝐃] :
  forall (τ τ' : NaturalTransformation F G),
  (forall X : 𝐂, τ X = τ' X) -> τ = τ'.
  Proof.
    intros τ τ' H.
    destruct τ as [τ n], τ' as [τ' n'].
    simpl in H; apply functional_extensionality_dep in H.
    destruct H. f_equal. apply proof_irrelevance.
  Qed.

  Section Horizontal_Composition.

    Variables 𝐀 𝐁 𝐂 : Category.
    Variables F F' : 𝐀 ==> 𝐁.
    Variables G G' : 𝐁 ==> 𝐂.
    Variable σ : forall X : 𝐀, Hom (F X) (F' X).
    Variable τ : forall Y : 𝐁, Hom (G Y) (G' Y).

    Definition hcompose : forall X : 𝐀, Hom ((G ∘ F) X) ((G' ∘ F') X) :=
      fun X => (τ (F' X)) ∘ (map G (σ X)).

    Context {nₛ : Natural σ}.
    Context {nₜ : Natural τ}.

    Instance hcompose_natural : Natural hcompose.
    Proof.
      intros X X' f; unfold hcompose; simpl.
      specialize (nₛ X X' f).
      specialize (nₜ (F' X) (F' X') (map F' f)).
      rewrite -> compose_assoc, -> nₜ.
      repeat (rewrite <- compose_assoc, <- compose_compat).
      repeat f_equal.
      exact nₛ.
    Qed.

  End Horizontal_Composition.

  Section Vertical_Composition.

    Variables 𝐂 𝐃 : Category.
    Variables F G H : 𝐂 ==> 𝐃.
    Variable τ : forall X : 𝐂, Hom (G X) (H X).
    Variable τ' : forall X : 𝐂, Hom (F X) (G X).

    Definition compose : forall X : 𝐂, Hom (F X) (H X) :=
      fun X => τ X ∘ τ' X.

    Context {nat : Natural τ}.
    Context {nat' : Natural τ'}.

    Instance compose_natural : Natural compose.
    Proof.
      intros X Y f; unfold compose.
      specialize (nat X Y f); specialize (nat' X Y f).
      now rewrite
        -> compose_assoc, -> nat,
        <- compose_assoc, -> nat',
        -> compose_assoc.
    Qed.

  End Vertical_Composition.
  Arguments compose [_ _ _ _ _] _ _.

  Lemma compose_assoc [𝐂 𝐃 : Category] [A B C D : 𝐂 ==> 𝐃] :
  forall (τ : forall X, Hom (C X) (D X)),
  forall (τ' : forall X, Hom (B X) (C X)),
  forall (τ'' : forall X, Hom (A X) (B X)),
  compose τ (compose τ' τ'') = compose (compose τ τ') τ''.
  Proof.
    intros; unfold compose.
    apply functional_extensionality_dep.
    intro; apply compose_assoc.
  Qed.

  Section Identity.
    Context `(F : 𝐂 ==> 𝐃).

    Let ι : forall X : 𝐂, Hom (F X) (F X) := fun X => 1.
    
    #[export]
    Instance id_natural : Natural ι.
    Proof.
      unfold Natural; intros.
      subst ι.
      now autorewrite with categories.
    Qed.

    Definition id := mk_nt ι _.
  End Identity.

End Natural.

#[canonical, universes(polymorphic), program]
Definition FunctorCategory (𝐂 𝐃 : Category) :=
{|
  Obj := 𝐂 ==> 𝐃 ;
  Hom F G := NaturalTransformation F G ;
  compose _ _ _ τ τ' := mk_nt (Natural.compose τ τ')
    ltac:(apply Natural.compose_natural; apply transformation_natural) ;
  id F := Natural.id F
|}.
Next Obligation.
  destruct f as [τ], g as [τ'], h as [τ''].
  apply Natural.extensionality; simpl.
  apply equal_f_dep, Natural.compose_assoc.
Qed.
Next Obligation.
  destruct f as [τ]; apply Natural.extensionality.
  intro X. cbv. auto with categories.
Qed.
Next Obligation.
  destruct f as [τ]; apply Natural.extensionality.
  intro X. cbv. apply compose_id_right.
Qed.


Section Yoneda_Lemma.

  Variable 𝐂 : Category.
  Variable F : 𝐂 ==> TypeCategory.

  #[program]
  Definition N : 𝐂 ==> TypeCategory :=
    {| map₀ A := NaturalTransformation (HomFunctor A) F ;
       map A B f τ := mk_nt (fun X g => τ X (g ∘ f)) _ |}.
  Next Obligation.
    intros X Y g.
    destruct τ as [τ H]; unfold Natural in H; simpl.
    specialize (H X Y g); simpl in H.
    set (ϕ := fun x : A → X => map F g (τ X x)) in H.
    set (ψ := fun x : A → X => τ Y (g ∘ x)) in H.
    apply functional_extensionality. intro x.
    pose proof (H' := equal_f H (x ∘ f)).
    subst ϕ ψ; simpl in H'.
    rewrite -> compose_assoc in H'.
    exact H'.
  Qed.
  Next Obligation.
    apply functional_extensionality; simpl; intro τ.
    apply Natural.extensionality; simpl; intro X.
    apply functional_extensionality; intro f.
    autorewrite with categories. reflexivity.
  Qed.
  Next Obligation.
    apply functional_extensionality; simpl; intro τ.
    apply Natural.extensionality; simpl; intro X.
    apply functional_extensionality; intro α.
    rewrite -> compose_assoc. reflexivity.
  Qed.

  #[program]
  Definition yoneda : NaturalTransformation N F
    := mk_nt (fun A τ => τ A 1) _.
  Next Obligation.
    intros A B f.
    apply functional_extensionality; simpl; intro τ.
    pose proof (H := @naturality _ _ _ _ τ τ.(transformation_natural) A B f).
    pose proof (H' := equal_f H 1). simpl in H'.
    rewrite -> compose_id_left. rewrite -> compose_id_right in H'.
    exact H'.
  Qed.
  
  #[program]
  Definition yoneda' : NaturalTransformation F N := mk_nt _ _.
  Next Obligation.
    eexists (fun A f => map F f X0).
    intros A B f; apply functional_extensionality; simpl; intro g.
    rewrite compose_compat; reflexivity.
  Defined.
  Next Obligation.
    intros X Y f; apply functional_extensionality; intro fx; simpl.
    apply Natural.extensionality; intro A; simpl.
    apply functional_extensionality; intro g; simpl.
    rewrite compose_compat; reflexivity.
  Qed.

End Yoneda_Lemma.