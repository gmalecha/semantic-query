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
  intros.
  split; intros.
  { forward_reason; simpl in *.
    consider (C x0); intros; try contradiction.
    subst.
    specialize (H (h x0)).
    destruct H.
    { eexists. split.
      { eapply H0. eexists; split; eauto. }
      { rewrite H1; eauto. } }
    forward_reason; subst; simpl in *.
    eexists. split; eauto.
    simpl.
    consider (Gf x1 && Gb x1 x2); intros; try contradiction.
    subst.
    eapply andb_true_iff in H5. destruct H5.
    rewrite H3. rewrite H7. reflexivity. }
  { forward_reason; simpl in *.
    consider (C (fst x0) && Gb (h (fst x0)) (snd x0)); intros; try contradiction.
    subst. simpl in *.
    eapply andb_true_iff in H3. destruct H3.
    specialize (H6 (h x1)). destruct H6.
    { eexists. split.
      { eexists; split; eauto. }
      simpl. rewrite H5. rewrite H1; auto. reflexivity. }
    { forward_reason.
      eexists; split; eauto.
      rewrite H3. reflexivity. } }
Defined.

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
