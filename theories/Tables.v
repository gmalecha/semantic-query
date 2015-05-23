Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.

Set Implicit Arguments.
Set Strict Implicit.

Definition row_type : Type := list type.

Definition row (r : row_type) : Type := typeD (Tuple r).

Definition table (r : row_type) := list (row r).

Definition DB (ls : list type) := hlist (fun x => list (typeD x)) ls.


(** Cross-product of tables **)
Fixpoint cross {T U V : Type} (f : T -> U -> V) (ts : list T) (us : list U)
: list V :=
  match ts with
  | nil => nil
  | t :: ts => List.map (f t) us ++ cross f ts us
  end.

Lemma In_cross : forall {T U V} (f : T -> U -> V) us ts,
    forall x,
      In x (cross f ts us) <->
      exists t u,
        In t ts /\ In u us /\ x = f t u.
Proof.
  induction ts; simpl; intros.
  { split.
    { inversion 1. }
    { intros.
      forward_reason. assumption. } }
  { rewrite List.in_app_iff.
    rewrite IHts; clear IHts.
    rewrite in_map_iff.
    split; intros; forward_reason.
    { destruct H; forward_reason.
      { subst. do 2 eexists; eauto. }
      { do 2 eexists; eauto. } }
    { destruct H; subst.
      { left; eauto. }
      { right. eauto. } } }
Qed.

Export ExtLib.Data.HList.
Export ExtLib.Data.Member.
