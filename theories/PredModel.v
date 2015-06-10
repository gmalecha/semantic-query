Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Shallow.

Definition Pred (T: Type) : Type := T -> Prop.

Global Instance DataModel_Pred : DataModel Pred :=
{ Mret := fun _ x y => x = y
; Mzero := fun _ _ => False
; Mbind := fun _ _ c k x =>
             exists y, c y /\ k y x
; Mimpl := fun _ a b => forall x, a x -> b x
; makeM := fun _ ls x => List.In x ls
}.
Proof.
{ red. eauto. }
{ red; eauto. }
{ firstorder. }
{ red. red. intros. subst. auto. }
{ firstorder. }
{ firstorder. subst. assumption. }
{ firstorder. subst. assumption. }
{ firstorder. }
{ firstorder. }
{ firstorder. }
{ firstorder. }
{ firstorder. }
Defined.
