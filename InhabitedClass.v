(** A typeclass for easily finding some term of an inhabited type. *)

Set Implicit Arguments.
Generalizable Variables A B C.

Local Arguments id {_} _.


(** Our Inhabited class is in Type rather than Prop, so that we can
    eliminate it to construct terms in Type. However, the retreival
    function 'any' is made opaque since one should not depend on
    the particular element retrieved. *)

Class Inhabited (A: Type) : Type := Inhabits { any : A }.

Global Opaque any.


(** General mechanisms for inhabitation across maps *)

Global Instance Inhabited_hom_refl A : Inhabited (A -> A) := Inhabits id.

Global Instance Inhabited_hom_from_codomain A `(Inhabited B) : Inhabited (A -> B)
:= Inhabits (fun _ => any).

Global Instance Inhabited_hom_trans `(Inhabited (A -> B)) `(Inhabited (B -> C))
: Inhabited (A -> C)
:= Inhabits (fun a => @any (B -> C) _ (@any (A -> B) _ a)).

Global Instance Inhabited_forall `(P : A -> Type) (H : forall x, Inhabited (P x))
: Inhabited (forall x, P x)
:= Inhabits (fun x => any).

Global Instance Inhabited_dependent_codomain `(P : A -> Type) `(Inhabited A)
: Inhabited (forall x, P x) -> Inhabited (P any)
:= fun inhP => Inhabits (@any _ inhP any).

Global Instance Inhabited_codomain `(Inhabited A) `(Inhabited (A -> B))
: Inhabited B | 3
:= Inhabited_dependent_codomain _ _ _.

Global Instance Inhabited_from_Empty_set A : Inhabited (Empty_set -> A)
:= Inhabits (Empty_set_rect _).


(** Concrete instances *)

Global Instance Inhabited_unit : Inhabited unit := Inhabits tt.

Global Instance Inhabited_bool : Inhabited bool := Inhabits false.

Global Instance Inhabited_nat : Inhabited nat := Inhabits 174.

Global Instance Inhabited_comparison : Inhabited comparison := Inhabits Lt.

Global Instance Inhabited_option A : Inhabited (option A) := Inhabits None.

Global Instance Inhabited_list A : Inhabited (list A) := Inhabits nil.

Global Instance byte_Inhabited : Inhabited Byte.byte := Inhabits Byte.x55.

Section Decimal.

  Import Decimal.

  Global Instance Inhabited_Decimal_uint : Inhabited uint :=
    Inhabits (D1 (D0 Nil)).

  Global Instance Inhabited_Decimal_int : Inhabited int :=
    Inhabits (Pos any).

  Global Instance Inhabited_decimal : Inhabited decimal :=
    Inhabits (Decimal any any).

End Decimal.

Section Hexadecimal.

  Import Hexadecimal.

  Global Instance Inhabited_Hexadecimal_uint : Inhabited uint :=
    Inhabits (D5 (Da Nil)).

  Global Instance Inhabited_Hexadecimal_int : Inhabited int :=
    Inhabits (Pos any).
  
  Global Instance Inhabited_hexadecimal : Inhabited hexadecimal :=
    Inhabits (Hexadecimal any any).

End Hexadecimal.

Section Number.

  Import Number.

  Global Instance Inhabited_Number_uint : Inhabited uint :=
    Inhabits (UIntDecimal any).

  Global Instance Inhabited_Number_int : Inhabited int :=
    Inhabits (IntHexadecimal any).

  Global Instance Inhabited_number : Inhabited number :=
    Inhabits (Decimal any).

End Number.


(** Derived instances *)

Global Instance Inhabited_sum_inl A B `(Inhabited A) : Inhabited (A + B) :=
  Inhabits (inl any).

Global Instance Inhabited_sum_inr A B `(Inhabited B) : Inhabited (A + B) | 2 :=
  Inhabits (inr any).

Global Instance Inhabited_prod `(Inhabited A) `(Inhabited B) : Inhabited (A * B) :=
  Inhabits (pair any any).


(** Inhabited instances from Init.Specif. *)

Global Instance Inhabited_sigT `(P : A -> Type)
: forall a, Inhabited (P a) -> Inhabited (sigT P)
:= fun a _ => Inhabits (existT _ a any).

Global Instance Inhabited_sigT_irrel `(Inhabited A) `(Inhabited B)
: Inhabited {x : A & B}
:= Inhabits (existT _ any any).

#[global]
Instance Inhabited_sigT2 `(P : A -> Type) (Q : A -> Type)
: forall a, Inhabited (P a) -> Inhabited (Q a) -> Inhabited (sigT2 P Q)
:= fun a _ _ => Inhabits (existT2 _ _ a any any).

#[global]
Instance Inhabited_sigT2_irrel `(Inhabited A) `(Inhabited B) `(Inhabited C)
: Inhabited {x : A & B & C}
:= Inhabits (existT2 _ _ any any any).

#[global]
Instance Inhabited_sumor_left `(Inhabited A) (B : Prop) : Inhabited (A + {B})
:= Inhabits (inleft any).
