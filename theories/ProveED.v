Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.DataModel.
Require Import SemanticQuery.ListModel.

Fixpoint check_in {T} {Req : RelDec (@eq T)} x (a : list T) : bool :=
  match a with
  | nil => false
  | a :: a' => if x ?[ eq ] a then true else check_in x a'
  end.

Lemma check_in_sound : forall {T} {Req : RelDec (@eq T)} {ReqC : RelDec_Correct Req} x (a : list T),
    check_in x a = true ->
    In x a.
Proof.
  induction a; simpl; try congruence.
  intros.
  consider (x ?[ eq ] a); eauto.
Qed.

Definition check_meq {T} {Req : RelDec (@eq T)} (a b : list T)
: bool :=
  if List.forallb (fun x => check_in x b) a then
    List.forallb (fun x => check_in x a) b
  else
    false.

Lemma Meq_decide : forall {T} {Req : RelDec (@eq T)} {ReqOk : RelDec_Correct Req} (a b : list T),
    check_meq a b = true ->
    Meq a b.
Proof.
  intros. unfold check_meq in H.
  consider (forallb (fun x : T => check_in x b) a); intros.
  split; simpl; red; intros.
  { rewrite forallb_forall in H.
    eapply H in H1.
    eapply check_in_sound in H1; eauto. }
  { rewrite forallb_forall in H0.
    eapply H0 in H1.
    eapply check_in_sound in H1; eauto. }
Qed.

Instance RelDec_typeD {ts} : RelDec (@eq (typeD ts)) :=
  { rel_dec := fun x y =>
                 match val_dec x y with
                 | left _ => true
                 | right _ => false
                 end }.

Instance RelDec_Correct_row {ts} : RelDec_Correct (@RelDec_typeD ts).
Proof. constructor.
       unfold rel_dec. simpl. intros.
       match goal with
       | |- context [ match ?X with _ => _ end ] =>
         destruct X
       end; subst; try tauto.
       split; auto.
       congruence.
Qed.

Instance RelDec_hlist {ts} : RelDec (@eq (hlist typeD ts)).
constructor.
induction 1.
{ refine (fun x => true). }
{ refine (fun x => if f ?[ eq ] hlist_hd x then
                     IHX (hlist_tl x)
                   else false); eauto with typeclass_instances. }
Defined.

Instance RelDec_Correct_hlist {ts} : RelDec_Correct (@RelDec_hlist ts).
Proof.
  constructor.
  induction x; intros.
  { rewrite (hlist_eta y). simpl. tauto. }
  { rewrite (hlist_eta y). simpl.
    consider (f ?[ eq ] hlist_hd y).
    { intros; subst. intros.
      split.
      { intros. f_equal. eapply IHx. eapply H. }
      { intros. eapply IHx.
        inv_all. auto. } }
    { intros; split; intros; try congruence.
      inv_all. subst.
      congruence. } }
Qed.
