Generalizable Variables A B C D.

Class Inhabited (A: Type) : Type := any : A.

Global Opaque any.

(** General mechanisms for inhabitation across maps. *)

Global Instance Inhabited_hom_refl 
: forall A, Inhabited (A -> A)
:= @id.

Global Instance Inhabited_hom_trans (A B C : Type)
: Inhabited (A -> B) -> Inhabited (B -> C) -> Inhabited (A -> C)
:= fun f g => fun a => g (f a).

Global Instance Inhabited_forall `(P : A -> Type)
: (forall x, Inhabited (P x)) -> Inhabited (forall x, P x)
:= id (A := forall x, P x).

Global Instance Inhabited_dependent_codomain `(P : A -> Type)
: forall (inhA : Inhabited A), Inhabited (forall x, P x) -> Inhabited (P any)
:= fun a p => p a.

Global Instance Inhabited_codomain (A B : Type)
: Inhabited A -> Inhabited (A -> B) -> Inhabited B | 3
:= Inhabited_dependent_codomain (fun x => B).

(** Inhabited instances from Init.Datatypes *)

Global Instance Inhabited_unit : Inhabited unit := tt.

Global Instance Inhabited_from_Empty_set (A : Type) : Inhabited (Empty_set -> A)
:= Empty_set_rect (fun _ => A).

Global Instance Inhabited_bool : Inhabited bool := false.

Global Instance Inhabited_nat : Inhabited nat := 174.

Global Instance Inhabited_option A : Inhabited (option A) := None.

Global Instance Inhabited_sum_inl A B : Inhabited A -> Inhabited (A + B) := inl.

Global Instance Inhabited_sum_inr A B : Inhabited B -> Inhabited (A + B) | 2 := inr.

Global Instance prod_Inhabited A B : Inhabited A -> Inhabited B -> Inhabited (A * B) := pair.

Global Instance list_Inhabited A : Inhabited (list A) := nil.

Global Instance comparison_Inhabited : Inhabited comparison := Lt.

(** Inhabited instances from Init.Specif *)

Global Instance Inhabited_sigT (A : Type) (P : A -> Type)
: forall a, Inhabited (P a) -> Inhabited (sigT P)
:= existT P.

Global Instance Inhabited_sigT_irrel (A B : Type)
: Inhabited A -> Inhabited B -> Inhabited {x : A & B}
:= existT (fun _ => B).

#[global]
Instance Inhabited_sigT2 (A : Type) (P Q : A -> Type)
: forall a, Inhabited (P a) -> Inhabited (Q a) -> Inhabited (sigT2 P Q)
:= existT2 P Q.

#[global]
Instance Inhabited_sigT2_irrel (A B C : Type)
: Inhabited A -> Inhabited B -> Inhabited C -> Inhabited {x : A & B & C}
:= existT2 (fun _ => B) (fun _ => C).

#[global]
Instance Inhabited_sumor_left (A : Type) (B : Prop)
: Inhabited A -> Inhabited (A + {B})
:= inleft.


(** Other instances from Init *)

Global Instance byte_Inhabited : Inhabited Byte.byte := Byte.x55.

Section Decimal.

  Import Decimal.

  Global Instance Inhabited_Decimal_uint : Inhabited uint := D2 (D1 (D0 Nil)).

  Global Instance Inhabited_Decimal_int : Inhabited int := Pos any.

  Global Instance Inhabited_decimal : Inhabited decimal := Decimal any any.

End Decimal.

Section Hexadecimal.

  Import Hexadecimal.

  Global Instance Inhabited_Hexadecimal_uint : Inhabited uint := D1 (D5 (Da Nil)).

  Global Instance Inhabited_Hexadecimal_int : Inhabited int := Pos any.
  
  Global Instance Inhabited_hexadecimal : Inhabited hexadecimal := Hexadecimal any any.

End Hexadecimal.

Section Number.

  Import Number.

  Global Instance Inhabited_Number_uint : Inhabited uint := UIntDecimal any.

  Global Instance Inhabited_Number_int : Inhabited int := IntHexadecimal any.

  Global Instance Inhabited_number : Inhabited number := Decimal any.

End Number.
