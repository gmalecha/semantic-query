Require Import Coq.Bool.Bool.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.DataModel.

Definition Pred (T: Type) : Type := T -> Prop.

Lemma Pred_chaseable
: forall (S S' T U : Type) (P : Pred S) (C : S -> bool) 
     (E : S -> T) (F : Pred S') (Gf : S' -> bool) (B : Pred U)
     (Gb : S' -> U -> bool),
   (forall x : S',
    (exists y : S',
       F y /\ (if Gf y then fun y0 : S' => y = y0 else fun _ : S' => False) x) ->
    exists y : S' * U,
      (exists y0 : S', F y0 /\ (exists y1 : U, B y1 /\ (y0, y1) = y)) /\
      (if Gf (fst y) && Gb (fst y) (snd y)
       then fun y0 : S' => fst y = y0
       else fun _ : S' => False) x) /\
   (forall x : S',
    (exists y : S' * U,
       (exists y0 : S', F y0 /\ (exists y1 : U, B y1 /\ (y0, y1) = y)) /\
       (if Gf (fst y) && Gb (fst y) (snd y)
        then fun y0 : S' => fst y = y0
        else fun _ : S' => False) x) ->
    exists y : S',
      F y /\ (if Gf y then fun y0 : S' => y = y0 else fun _ : S' => False) x) ->
   forall h : S -> S',
   (forall x : S', (exists y : S, P y /\ h y = x) -> F x) ->
   (forall x : S, C x = true -> Gf (h x) = true) ->
   (forall x : T,
    (exists y : S,
       P y /\ (if C y then fun y0 : T => E y = y0 else fun _ : T => False) x) ->
    exists y : S * U,
      (exists y0 : S, P y0 /\ (exists y1 : U, B y1 /\ (y0, y1) = y)) /\
      (if C (fst y) && Gb (h (fst y)) (snd y)
       then fun y0 : T => E (fst y) = y0
       else fun _ : T => False) x) /\
   (forall x : T,
    (exists y : S * U,
       (exists y0 : S, P y0 /\ (exists y1 : U, B y1 /\ (y0, y1) = y)) /\
       (if C (fst y) && Gb (h (fst y)) (snd y)
        then fun y0 : T => E (fst y) = y0
        else fun _ : T => False) x) ->
    exists y : S,
      P y /\ (if C y then fun y0 : T => E y = y0 else fun _ : T => False) x).
Proof.
Admitted.

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
{ apply Pred_chaseable. }
Defined.
