Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import SemanticQuery.Tables.

Set Implicit Arguments.
Set Strict Implicit.

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
  tget Demo.tbl_names (fun n =>
  tget Demo.tbl_manager (fun m =>
  tguard (hlist_hd n ?[ eq ] hlist_hd  m) (tret (n,m)))).