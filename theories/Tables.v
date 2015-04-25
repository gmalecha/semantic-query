Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.

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

Inductive expr (T : dec_type) (ls : list row_type) : Type :=
| Proj : forall r, member r ls -> member T r -> expr T ls.

Export ExtLib.Data.HList.
Export ExtLib.Data.Member.
