Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import ExtLib.Data.String.
Require Import ExtLib.Core.RelDec.
Require Import SemanticQuery.DataModel.
Require Import SemanticQuery.LtacChase.

Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Set Strict Implicit.

Section Index.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Local Open Scope string_scope.

  Record person : Type := Person
  { name : string
  ; age  : nat }.

  Section over_db.
    Variable People : M person.
    Variable Children : M person.

    Definition under_21_is_child : Prop :=
      embedded_dependency
        (People)
        (fun x => x.(age) ?[ lt ] 21)
        (Children)
        (fun x y => x.(age) ?[ eq ] y.(age) && x.(name) ?[ eq ] y.(name)).

    Definition children_are_people : Prop :=
      embedded_dependency
        Children
        (fun _ => true)
        People
        (fun x y => x.(age) ?[ eq ] y.(age) && x.(name) ?[ eq ] y.(name)).

    (** Query normalization **)
    (*************************)

    Example ex1 : M (string)
    := Mbind People (fun p =>
       Mguard (p.(age) ?[ gt ] 16 && p.(age) ?[ lt ] 18)
              (Mret (p.(name)))).

    Example normalized_ex1' : { x : M _ | Meq x ex1 }.
    execute0 normalize.
    Defined.

    Example normalized_ex1 :=
      Eval cbv beta iota zeta delta [ proj1_sig normalized_ex1' ]
      in (proj1_sig normalized_ex1').
    Print normalized_ex1.

    (** Chasing **)
    (*************)

    Ltac solver :=
      intros;
      repeat match goal with
             | H : andb ?X ?Y = true |- _ =>
               apply Bool.andb_true_iff in H ; destruct H
             | |- andb _ _ = true =>
               apply Bool.andb_true_iff ; split
             end ;
      eauto using rel_dec_eq_true with typeclass_instances.

    Ltac solver' :=
      intros;
      repeat match goal with
             | H : andb ?X ?Y = true |- _ =>
               apply Bool.andb_true_iff in H ; destruct H
             | |- andb _ _ = true =>
               apply Bool.andb_true_iff ; split
             | H : _ ?[ _ ] _ = true |- _ => eapply rel_dec_true_eq in H; eauto with typeclass_instances
             end ;
      repeat first [ solve [ eauto using rel_dec_eq_true with typeclass_instances ]
                   | f_equal ].

    Example universal_ex1'
    : { x : M _
      | EdsSound (under_21_is_child :: children_are_people :: nil) -> Meq x normalized_ex1 }.
    execute1 chase solver. (** TODO: Figure out what is wrong here **)
    Defined.

    Definition universal_ex1 :=
      Eval cbv beta zeta delta [ universal_ex1' proj1_sig conditional_transitive conditional_simpl ]
      in (proj1_sig universal_ex1').

    Eval unfold universal_ex1 in universal_ex1.

    (** Minimization **)
    (******************)

    Example minimized_ex1' : { x : _ | Meq x universal_ex1 }.
    execute1 minimize solver'.
    Defined.

    Definition minimized_ex1 :=
      Eval cbv beta iota zeta delta [ Mmap minimized_ex1' proj1_sig unconditional_transitive unconditional_simpl query ]
      in (proj1_sig minimized_ex1').
    Print minimized_ex1.

    (** Finishing **)
    (***************)

    Definition finished_ex1 : { m : _ | Meq m minimized_ex1 }.
    execute0 simplifier.
    Defined.

    Eval cbv beta iota zeta delta [ Mmap finished_ex1 proj1_sig unconditional_transitive unconditional_simpl query ]
      in (proj1_sig finished_ex1).

    (** TODO: This is incomplete **)
    Ltac continue tac :=
      (first [ refine (@refine_transitive _ _ _ _ _ _ _ _)
             | refine (@refine_transitive_under _ _ _ _ _ _ _ _ _) ];
       [ shelve | | ]); [ once  tac.. | ].
    Ltac optimize solver :=
      prep ;
      lazymatch goal with
      | |- Meq _ _ =>
        continue normalize ;
        continue ltac:(idtac; minimize solver) ;
        simplifier
      | |- _ -> Meq _ _ =>
        continue normalize ;
        continue ltac:(idtac; chase solver) ;
        continue ltac:(idtac; minimize solver) ;
        simplifier
      end.

    Definition optimized
    : { m : _ | EdsSound (under_21_is_child :: children_are_people :: nil) -> Meq m ex1 }.
    optimize solver'.
    Defined.

    Eval cbv beta iota zeta delta [ Mmap finished_ex1 proj1_sig optimized ]
      in (proj1_sig optimized).

    Definition tbl_children : M person := makeM
      (Person "A toddler" 3 ::
       Person "A teen" 17 :: nil).

    Definition tbl_people : M person := makeM
      (Person "A toddler" 3 ::
       Person "An adult" 25 ::
       Person "A teen" 17 :: nil).

  End over_db.

End Index.

Require Import SemanticQuery.ListModel.

Time Eval vm_compute in (@ex1 list _ (@tbl_people list _)).
Time Eval vm_compute in (proj1_sig (@finished_ex1 list _ (@tbl_people list _))).