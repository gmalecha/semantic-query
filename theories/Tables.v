Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Tactics.

Set Implicit Arguments.
Set Strict Implicit.

Record dec_type :=
{ type : Type
; eq_dec : forall a b : type, {a = b} + {a <> b}
}.

Definition dec_type_from_EqDec (T : Type)
           {ED : RelDec (@eq T)} {EDO : RelDec_Correct ED}
: dec_type :=
{| type := T
 ; eq_dec := fun a b : T =>
               match a ?[ eq ] b as t return a ?[ eq ] b = t -> {a = b} + {a <> b} with
               | true => fun pf =>
                           left (proj1 (@rel_dec_correct _ _ _ EDO a b) pf)
               | false => fun pf =>
                            right (proj2 (@neg_rel_dec_correct _ _ _ EDO a b) pf)
               end eq_refl
 |}.

Arguments dec_type_from_EqDec _ {_ _}.

Definition row_type : Type := list dec_type.

Definition row (r : row_type) : Type := hlist type r.

Definition table (r : row_type) := list (row r).

Module Demo.
  Require Import ExtLib.Data.Nat.
  Require Import ExtLib.Data.String.

  Definition nat_type : dec_type := dec_type_from_EqDec nat.
  Definition string_type : dec_type := dec_type_from_EqDec string.

  Definition tt_names : row_type := nat_type :: string_type :: nil.
  Definition tt_manager : row_type := nat_type :: nat_type :: nil.

  Fixpoint tuple (r : row_type) : Type :=
    match r with
    | nil => unit
    | r :: rs => type r * tuple rs
    end%type.

  Fixpoint Row (r : row_type) : tuple r -> hlist type r :=
    match r as r return tuple r -> hlist type r with
    | nil => fun _ => Hnil
    | r :: rs => fun v => Hcons (fst v) (Row rs (snd v))
    end.

  Definition tbl_names : table tt_names :=
    (Row tt_names (0, ("Ryan"%string, tt))) ::
    (Row tt_names (1, ("Gregory"%string, tt))) ::
    nil.

  Definition tbl_manager : table tt_manager :=
    (Row tt_manager (1, (0, tt))) :: nil.
End Demo.

(** Deeply embedded expressions **)
Inductive expr (vars : list row_type) : dec_type -> Type :=
| Proj : forall T r, member r vars -> member T r -> expr vars T.

Fixpoint expr_weaken vars rt T (e : expr vars T) {struct e}
  : expr (rt :: vars) T :=
  match e in @expr _ T return expr (rt :: vars) T with
  | Proj _ _ t f => Proj (Member.MN _ t) f
  end.


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
