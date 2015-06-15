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
    Time execute0 normalize.
    Defined.

    Example normalized_ex1 :=
      Eval cbv beta iota zeta delta [ proj1_sig normalized_ex1' ]
      in (proj1_sig normalized_ex1').

    (** Chasing **)
    (*************)

    Lemma pair_inj : forall {T U} (a b : T) (c d : U),
        a = b -> c = d ->
        (a,c) = (b,d).
    Proof. congruence. Qed.

    Ltac solver :=
      intros;
      repeat match goal with
             | H : andb ?X ?Y = true |- _ =>
               apply Bool.andb_true_iff in H ; destruct H
             | |- andb _ _ = true =>
               apply Bool.andb_true_iff ; split
             | H : _ ?[ _ ] _ = true |- _ => eapply rel_dec_true_eq in H; eauto with typeclass_instances
             | |- andb _ _ = true =>
               eapply Bool.andb_true_iff ; split
             | |- _ ?[ _ ] _ = true =>
               eapply rel_dec_eq_true
             | |- (_,_) = (_,_) => eapply pair_inj
             end ;
      repeat first [ solve [ eauto using rel_dec_eq_true with typeclass_instances ]
                   | f_equal ].

    Example universal_ex1'
    : { x : M _
      | EdsSound (under_21_is_child :: children_are_people :: nil) -> Meq x normalized_ex1 }.
    Time execute1 chase solver.
    Defined.

    Definition universal_ex1 :=
      Eval cbv beta iota zeta delta [ universal_ex1' proj1_sig conditional_transitive conditional_simpl reflexivity ]
      in (proj1_sig universal_ex1').

    (** Minimization **)
    (******************)

    Example minimized_ex1' : { x : _ | EdsSound (under_21_is_child :: children_are_people :: nil) -> Meq x universal_ex1 }.
    Time execute1 minimize solver.
    Defined.

    Definition minimized_ex1 :=
      Eval cbv beta iota zeta delta [ Mmap minimized_ex1' proj1_sig unconditional_transitive unconditional_simpl query ]
      in (proj1_sig minimized_ex1').
    Print minimized_ex1.

    (** Finishing **)
    (***************)

    Definition finished_ex1 : { m : _ | Meq m minimized_ex1 }.
    Time execute0 simplifier.
    Defined.

(*
    Eval cbv beta iota zeta delta [ Mmap finished_ex1 proj1_sig unconditional_transitive unconditional_simpl query ]
      in (proj1_sig finished_ex1).
*)

    Definition optimized
    : { m : _ | EdsSound (under_21_is_child :: children_are_people :: nil) -> Meq m ex1 }.
    Time optimize solver.
    Defined.

(*
    Eval cbv beta iota zeta delta [ Mmap finished_ex1 proj1_sig optimized ]
      in (proj1_sig optimized).
*)

    Definition tbl_children : M person := makeM
      (Person "A toddler" 3 ::
       Person "A teen" 17 :: nil).

    Definition tbl_people : M person := makeM
      (Person "A toddler" 3 ::
       Person "An adult" 25 ::
       Person "A teen" 17 :: nil).

  End over_db.

End Index.

(*
Require Import SemanticQuery.ListModel.

Time Eval vm_compute in (@ex1 list _ (@tbl_people list _)).
Time Eval vm_compute in (proj1_sig (@finished_ex1 list _ (@tbl_people list _))).
*)