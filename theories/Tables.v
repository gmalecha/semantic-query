Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.
(* Only for examples *)
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.String.

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

Definition table_type : Type := list dec_type.

Definition table (r : table_type) := list (hlist type r).

Section example.
  Definition nat_type : dec_type := dec_type_from_EqDec nat.
  Definition string_type : dec_type := dec_type_from_EqDec string.

  Definition tt_names : table_type := nat_type :: string_type :: nil.
  Definition tt_manager : table_type := nat_type :: nat_type :: nil.

  Fixpoint tuple (r : table_type) : Type :=
    match r with
    | nil => unit
    | r :: rs => type r * tuple rs
    end%type.

  Fixpoint row (r : table_type) : tuple r -> hlist type r :=
    match r as r return tuple r -> hlist type r with
    | nil => fun _ => Hnil
    | r :: rs => fun v => Hcons (fst v) (row rs (snd v))
    end.

  Definition tbl_names : table tt_names :=
    (row tt_names (0, ("Ryan"%string, tt))) ::
    (row tt_names (1, ("Gregory"%string, tt))) ::
    nil.

  Definition tbl_manager : table tt_manager :=
    (row tt_manager (1, (0, tt))) :: nil.
End example.

Module shallow.

  Definition tableaux (T : Type) : Type := list T.
  Fixpoint tget {T U} (t : tableaux T) (k : T -> tableaux U) : tableaux U :=
    match t with
    | nil => nil
    | t :: ts => k t ++ tget ts k
    end.
  Definition tret {T} (v : T) : tableaux T := v :: nil.
  Definition tguard {T} (g : bool) (t : tableaux T) : tableaux T :=
    match g with
    | true => t
    | false => nil
    end.

  Definition trial :=
    tget tbl_names (fun n =>
    tget tbl_manager (fun m =>
    tguard (hlist_hd n ?[ eq ] hlist_hd  m) (tret (n,m)))).

End shallow.



Inductive expr (T : dec_type) (ls : list table_type) : Type :=
| Proj : forall r, member r ls -> member T r -> expr T ls.

Module record.
Record tableaux (tbls : list table_type) :=
{ types : list table_type
; binds : hlist (fun x => member x tbls) types
; filter : list { T : dec_type & expr T types & expr T types }
}.

End record.

Module inductive.
Inductive tableaux (tbls : list table_type) (res : list table_type) : list table_type -> Type :=
| Bind : forall r vars,
    member r tbls ->
    tableaux tbls res (r :: vars) ->
    tableaux tbls res vars
| Done : tableaux tbls res res.

Fixpoint tableauxD tbls res vars (t : tableaux tbls res vars)
: hlist table tbls -> hlist table vars -> hlist table res :=
  match t in tableaux _ _ vars
        return hlist table tbls -> hlist table vars -> hlist table res
  with
  | Done => fun _ x => x
  | Bind r vars m t => fun tbls tbls_vars =>
                         tableauxD _ _ _ t tbls (Hcons (hlist_get m tbls) tbls_vars)
  end.
End inductive.