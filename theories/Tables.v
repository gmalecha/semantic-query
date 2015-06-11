Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.DataModel.

Set Implicit Arguments.
Set Strict Implicit.

Section with_model.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Definition row_type : Type := list type.

  Definition row (r : row_type) : Type := typeD (Tuple r).

  Definition table (r : row_type) := M (row r).

  Definition DB (ls : list type) := hlist (fun x => M (typeD x)) ls.

End with_model.

Export ExtLib.Data.HList.
Export ExtLib.Data.Member.
