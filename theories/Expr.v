Require Import Coq.Lists.List.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import SemanticQuery.Types.

Set Implicit Arguments.
Set Strict Implicit.

(** Deeply embedded expressions **)
Inductive expr (vars : list type) : type -> UU :=
| Var : forall T, member T vars -> expr vars T
| Proj : forall T r, expr vars (Tuple r) -> member T r -> expr vars T
| Eq : forall T, expr vars T -> expr vars T -> expr vars Bool.

Definition Env : list type -> U := hlist typeD.
Definition exprT (ls : list type) (T : Type) : Type :=
  Env ls -> T.

Fixpoint exprD {vars} {t} (e : expr vars t)
: exprT vars (typeD t) :=
  match e in expr _ t return exprT vars (typeD t) with
  | Var _ m => hlist_get m
  | Proj _ r e' f =>
    let eD := @exprD vars (Tuple r) e' in
    let fD := tuple_get typeD f in
    fun vs => fD (eD vs)
  | Eq T l r =>
    let lD := exprD l in
    let rD := exprD r in
    let eqD := @val_dec T in
    fun vs => if eqD (lD vs) (rD vs) then true else false
  end.

Fixpoint member_lift {T} {t : T} (vs vs' : list T) (m : member t vs')
: member t (vs ++ vs') :=
  match vs as vs return member t (vs ++ vs') with
  | nil => m
  | v :: vs => MN _ (member_lift _ m)
  end.

Fixpoint expr_lift {T} vs vs' (e : expr vs' T) {struct e}
: expr (vs ++ vs') T :=
  match e in expr _ T return expr (vs ++ vs') T with
  | Var _ m => Var (member_lift _ m)
  | Proj _ _ a b => Proj (expr_lift _ a) b
  | Eq T a b => Eq (expr_lift _ a) (expr_lift _ b)
  end.

Fixpoint member_weaken_app {T} {t : T} (vs vs' : list T) (m : member t vs')
  : member t (vs' ++ vs) :=
  match m in member _ vs' return member t (vs' ++ vs) with
  | MZ _ => MZ _ _
  | MN _ _ m => MN _ (member_weaken_app _ m)
  end.

Fixpoint expr_weaken_app {T} vs vs' (e : expr vs' T) {struct e}
  : expr (vs' ++ vs) T :=
  match e in expr _ T return expr (vs' ++ vs) T with
  | Var _ a => Var (member_weaken_app _ a)
  | Proj _ _ a b => Proj (expr_weaken_app _ a) b
  | Eq T a b => Eq (expr_weaken_app _ a) (expr_weaken_app _ b)
  end.

Section _subst.
  Context {vars vars' : list type}.
  Variable (f :forall {x}, member x vars -> member x vars').

  Fixpoint expr_subst  {T}
           (e : expr vars T) {struct e} : expr vars' T :=
    match e in expr _ T return expr vars' T with
    | Var _ v => Var (f v)
    | Proj _ _ v c => Proj (expr_subst v) c
    | Eq T a b => Eq (expr_subst a) (expr_subst b)
    end.
End _subst.