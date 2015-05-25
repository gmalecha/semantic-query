Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.Tables.
Require Import SemanticQuery.RecordTableaux.
Require Import SemanticQuery.Entailer.
Require Import SemanticQuery.Chase.
Require Import SemanticQuery.Minimize.
Require Import SemanticQuery.Parsing.

Set Implicit Arguments.
Set Strict Implicit.

Definition Row (r : row_type) : tuple typeD r -> row r := fun x => x.

Local Notation "#0" := (@MZ _ _ _).
Local Notation "#1" := (@MN _ _ _ _ #0).
Local Notation "#2" := (@MN _ _ _ _ #1).

Module Movies.
  Local Open Scope string_scope.

  Definition tt_movies : row_type :=
    (* title    : *) String ::
    (* director : *) String ::
    (* actor    : *) String :: nil.

  Definition tbl_movies : table tt_movies :=
    (Row tt_movies ("Star Trek: Into Darkness", ("JJ Abrams", ("Benedict Cumberbatch", tt)))) ::
    (Row tt_movies ("Star Trek: Into Darkness", ("JJ Abrams", ("Chris Pine", tt)))) ::
    (Row tt_movies ("Stardust", ("Matthew Vaughn", ("Claire Danes", tt)))) ::
    (Row tt_movies ("Stardust", ("Matthew Vaughn", ("Robert Di Niro", tt)))) ::
    (Row tt_movies ("Stardust", ("Matthew Vaughn", ("Charlie Cox", tt)))) :: nil.

  Definition scheme := List.map Tuple (tt_movies :: nil).

  Definition movies_db : DB scheme.
    eapply Hcons.
    eapply tbl_movies.
    eapply Hnil.
  Defined.

  (** TODO: I need notation for this **)
  Definition title_implies_director : embedded_dependency scheme :=
    @Build_embedded_dependency scheme
                               (Tuple tt_movies :: Tuple tt_movies :: nil)
                               (Hcons #0 (Hcons #0 Hnil))
                               (Expr.Eq (Expr.Proj (Expr.Var #0) #0) (Expr.Proj (Expr.Var #1) #0) :: nil)
                               nil
                               Hnil
                               (Expr.Eq (Expr.Proj (Expr.Var #0) #1) (Expr.Proj (Expr.Var #1) #1) :: nil).
(*
  {| front_types := Tuple tt_movies :: Tuple tt_movies :: nil
   ; front_binds := Hcons MZ (Hcons MZ Hnil)
   ; front_filter := nil
   ; back_types := nil
   ; back_binds := Hnil
   ; back_filter := nil
   |}.
*)

  Theorem title_implies_director_sound
  : embedded_dependencyD title_implies_director movies_db.
  Proof.
    red. simpl.
  Admitted.

  Example ex1 : query scheme (String :: String :: nil).
  refine
    (@Build_query scheme (String :: String :: nil)
                      (QUERY scheme
                       USING ("m1" <- 0 ;;
                              ("m2" <- 0 ;;
                              assert (Proj (Var "m1") 0) == (Proj (Var "m2") 0) ;;
                              Ret)))
                  (Hcons (Expr.Proj (Expr.Var #0) #1)
                   (Hcons (Expr.Proj (Expr.Var #1) #2) Hnil))).
  Defined.

  Example universal_ex1 : query scheme (String :: String :: nil) :=
    Eval vm_compute
    in get_status (chase (@check_entails) 2 (title_implies_director :: nil) ex1).

  Example minimized_ex1 : query scheme (String :: String :: nil) :=
    Eval vm_compute
    in minimize (@check_entails) universal_ex1.

End Movies.

Module Indexing.
  Local Open Scope string_scope.

  Definition tt_people : row_type :=
    (* name : *) String ::
    (* age  : *) Nat :: nil.

  Definition tt_children : row_type :=
    (* name : *) String ::
    (* age  : *) Nat :: nil.

  Definition scheme := List.map Tuple (tt_people :: tt_children :: nil).

  Definition children_lt_21_person : embedded_dependency scheme.
  refine
    (@Build_embedded_dependency scheme
                               (Tuple tt_people :: nil)
                               (Hcons #0 Hnil)
                               (Expr.Lt (Expr.Proj (Expr.Var #0) #1) (Expr.Const _ Nat 21) :: nil)
                               (Tuple tt_children :: nil)
                               (Hcons #1 Hnil)
                               (Expr.Eq (Expr.Proj (Expr.Var #0) #0) (Expr.Proj (Expr.Var #1) #0) ::
                                Expr.Eq (Expr.Proj (Expr.Var #0) #1) (Expr.Proj (Expr.Var #1) #1) :: nil)).
  Defined.

  Definition children_are_people : embedded_dependency scheme.
  refine
    (@Build_embedded_dependency scheme
                               (Tuple tt_children :: nil)
                               (Hcons #0 Hnil)
                               nil
                               (Tuple tt_people :: nil)
                               (Hcons #1 Hnil)
                               (Expr.Eq (Expr.Proj (Expr.Var #0) #0) (Expr.Proj (Expr.Var #1) #0) ::
                                Expr.Eq (Expr.Proj (Expr.Var #0) #1) (Expr.Proj (Expr.Var #1) #1) :: nil)).
  Defined.

  Example ex1 : query scheme (String :: nil).
  refine
    (@Build_query scheme (String :: nil)
                      {| types := Tuple tt_people :: nil
                       ; binds := Hcons #0 Hnil
                       ; filter := Expr.Lt (Expr.Const _ Nat 16)
                                           (Expr.Proj (Expr.Var #0) #1) ::
                                   Expr.Lt (Expr.Proj (Expr.Var #0) #1)
                                           (Expr.Const _ Nat 18) :: nil
                       |}
                  (Hcons (Expr.Proj (Expr.Var #0) #0) Hnil)).
  Defined.

End Indexing.

Module Simple.

  Definition tt_names : row_type := Nat :: String :: nil.
  Definition tt_manager : row_type := Nat :: Nat :: nil.

  Definition tbl_names : table tt_names :=
    (Row tt_names (0, ("Ryan"%string, tt))) ::
    (Row tt_names (1, ("Gregory"%string, tt))) ::
    nil.

  Definition tbl_manager : table tt_manager :=
    (Row tt_manager (1, (0, tt))) :: nil.

  (** Example **)
  Let scheme :=
    List.map Tuple (
    tt_names ::
    tt_manager ::
    nil).

  Example ex1 : tableaux scheme :=
    (QUERY scheme
     USING ("x" <- 0 ;;
            assert (Proj (Var "x") 0) == (Proj (Var "x") 0) ;;
            Ret)).

End Simple.