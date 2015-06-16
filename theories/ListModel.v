Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.DataModel.

Set Implicit Arguments.
Set Strict Implicit.

Definition FSet (T : Type) : Type := list T.

Definition FSet_empty {T} : FSet T := nil.
Definition FSet_singleton {T} (v : T) : FSet T := v :: nil.
Fixpoint FSet_cross {T U : Type} (ts : FSet T) (f : T -> FSet U)
: FSet U :=
  match ts with
  | nil => nil
  | t :: ts => f t ++ FSet_cross ts f
  end.

Definition FSet_subset {T} (a b : FSet T) : Prop :=
  forall x, List.In x a -> List.In x b.

Instance Refl_FSet_subset : forall A : Type, Reflexive (@FSet_subset A).
Proof. red. red. tauto. Qed.

Instance Trans_FSet_subset : forall A : Type, Transitive (@FSet_subset A).
Proof. red. unfold FSet_subset. firstorder. Qed.

Lemma In_cross : forall {T U} (us : T -> FSet U) (ts : FSet T),
    forall x,
      In x (FSet_cross ts us) <->
      exists t u,
        In t ts /\ In x (us t) /\ x = u.
Proof.
  induction ts; simpl; intros.
  { split.
    { inversion 1. }
    { intros.
      forward_reason. assumption. } }
  { rewrite List.in_app_iff.
    rewrite IHts; clear IHts.
    split; intros; forward_reason.
    { destruct H; forward_reason.
      { subst. do 2 eexists; eauto. }
      { do 2 eexists; eauto. } }
    { destruct H; subst.
      { left; eauto. }
      { right. eauto. } } }
Qed.

Instance Proper_cross : forall A B : Type,
   Proper (FSet_subset ==> pointwise_relation A FSet_subset ==> FSet_subset)
     (@FSet_cross A B).
Proof.
Admitted.

Lemma cross_assoc :
 forall (A B C : Type) (c1 : FSet A) (c2 : A -> FSet B) (c3 : B -> FSet C),
 FSet_subset (FSet_cross (FSet_cross c1 c2) c3)
             (FSet_cross c1 (fun x : A => FSet_cross (c2 x) c3)) /\
 FSet_subset (FSet_cross c1 (fun x : A => FSet_cross (c2 x) c3))
             (FSet_cross (FSet_cross c1 c2) c3).
Proof.
  induction c1.
  { simpl. split; red; eauto. }
  { simpl; intros. split; red; intros.
    { eapply In_cross in H. forward_reason.
      subst. eapply in_app_iff in H.
      destruct H.
      { eapply in_app_iff.
        left. eapply In_cross. do 2 eexists; split; eauto. }
      { eapply in_app_iff.
        right. eapply IHc1.
        eapply In_cross. do 2 eexists; split; eauto. } }
    { eapply in_app_iff in H.
      destruct H.
      { eapply In_cross in H. forward_reason.
        subst. eapply In_cross. do 2 eexists; split; eauto.
        eapply in_app_iff; eauto. }
      { eapply IHc1 in H.
        eapply In_cross.
        eapply In_cross in H.
        forward_reason. subst.
        do 2 eexists; split.
        eapply in_app_iff. eauto. eauto. } } }
Qed.

Lemma FSet_subset_singleton :
 forall (A B : Type) (x : A) (c : A -> FSet B),
 FSet_subset (FSet_cross (FSet_singleton x) c) (c x) /\
 FSet_subset (c x) (FSet_cross (FSet_singleton x) c).
Proof.
  simpl. intros; split; red; intros.
  { eapply in_app_iff in H.
    destruct H; auto. inversion H. }
  { apply in_app_iff. eauto. }
Qed.

Lemma FSet_subset_cross_singleton :
 forall (A : Type) (c : FSet A),
 FSet_subset (FSet_cross c FSet_singleton) c /\
 FSet_subset c (FSet_cross c FSet_singleton).
Proof.
  simpl; intros. split; red; intros.
  { eapply In_cross in H. forward_reason.
    subst. simpl in H0. destruct H0; try contradiction.
    subst. assumption. }
  { eapply In_cross. do 2 eexists; split; eauto.
    split; eauto.
    simpl. auto. }
Qed.

Lemma FSet_subset_cross_empty :
 forall (A B : Type) (x : A -> FSet B),
 FSet_subset (FSet_cross FSet_empty x) FSet_empty /\
 FSet_subset FSet_empty (FSet_cross FSet_empty x).
Proof.
  simpl; intros. split; red; intros; inversion H.
Qed.

Lemma FSet_subset_ignore :
 forall (T U : Type) (x : FSet T) (y : FSet U),
 FSet_subset (FSet_cross x (fun _ : T => y)) y.
Proof.
  intros.
  red. intros. eapply In_cross in H.
  forward_reason.
  subst. eauto.
Qed.

Lemma FSet_subset_empty :
 forall (T : Type) (c : FSet T), FSet_subset FSet_empty c.
Proof.
  red. intros. inversion H.
Qed.

Lemma FSet_subset_cross_perm :
 forall (T U V : Type) (m1 : FSet T) (m2 : FSet U) (f : T -> U -> FSet V),
 FSet_subset (FSet_cross m1 (fun x : T => FSet_cross m2 (f x)))
   (FSet_cross m2 (fun y : U => FSet_cross m1 (fun x : T => f x y))) /\
 FSet_subset
   (FSet_cross m2 (fun y : U => FSet_cross m1 (fun x : T => f x y)))
   (FSet_cross m1 (fun x : T => FSet_cross m2 (f x))).
Proof.
  intros. split; red; intros;
          repeat match goal with
                 | H : In _ (FSet_cross _ _) |- _ =>
                   eapply In_cross in H; forward_reason
                 end; subst.
  { subst. eapply In_cross. do 2 eexists; split; eauto.
    split; eauto.
    eapply In_cross. do 2 eexists; split; eauto. }
  { subst. eapply In_cross. do 2 eexists; split; eauto.
    split; eauto.
    eapply In_cross. do 2 eexists; split; eauto. }
Qed.

Lemma FSet_subset_diag :
 forall (T U : Type) (m : FSet T) (f : T * T -> FSet U),
 FSet_subset (FSet_cross m (fun x : T => f (x, x)))
   (FSet_cross m (fun x : T => FSet_cross m (fun y : T => f (x, y)))).
Proof.
  intros. red; intros.
  repeat match goal with
                 | H : In _ (FSet_cross _ _) |- _ =>
                   eapply In_cross in H; forward_reason
                 end; subst.
   eapply In_cross. do 2 eexists; split; eauto.
   split; eauto.
   eapply In_cross. do 2 eexists; split; eauto.
Qed.

Instance DataModel_FSet : DataModel FSet :=
{ Mret := @FSet_singleton
; Mzero := @FSet_empty
; Mbind := @FSet_cross
; Mimpl := @FSet_subset
; makeM := fun _ x => x
}.
all: abstract eauto using FSet_subset_diag, FSet_subset_empty, FSet_subset_ignore,
     FSet_subset_cross_singleton, FSet_subset_singleton,
     cross_assoc, FSet_subset_cross_empty, FSet_subset_cross_perm.
Defined.
