Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.Tables.
Require Import SemanticQuery.Parsing.

Set Implicit Arguments.
Set Strict Implicit.

Definition tt_names : row_type := Nat :: String :: nil.
Definition tt_manager : row_type := Nat :: Nat :: nil.

Definition Row (r : row_type) : tuple typeD r -> row r := fun x => x.

Definition tbl_names : table tt_names :=
  (Row tt_names (0, ("Ryan"%string, tt))) ::
  (Row tt_names (1, ("Gregory"%string, tt))) ::
  nil.

Definition tbl_manager : table tt_manager :=
  (Row tt_manager (1, (0, tt))) :: nil.

(** Example **)
Let scheme_demo :=
  List.map Tuple (
  tt_names ::
  tt_manager ::
  nil).

Goal True.
  pose (QUERY scheme_demo
        USING ("x" <- 0 ;;
               assert (Proj (Var "x") 0) == (Proj (Var "x") 0) ;;
               Ret)).
  unfold compile_q in t. simpl in t.
  exact I.
Defined.
