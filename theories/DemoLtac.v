Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ExtLib.Data.String.
Require Import ExtLib.Core.RelDec.
Require Import SemanticQuery.DataModel.
Require Import SemanticQuery.LtacChase.

Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Set Strict Implicit.

Section Movies.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Local Open Scope string_scope.

  Record movie : Type := Movie
  { title : string
  ; director : string
  ; actor : string }.

  Section over_db.
    Variable db : M movie.

    Definition title_implies_director : Prop :=
      embedded_dependency
        (Mplus db db)
        (fun xy => (fst xy).(title) ?[ eq ] (snd xy).(title))
        (Mret tt)
        (fun xy _ => (fst xy).(director) ?[ eq ] (snd xy).(director)).

    (** Query normalization **)
    (*************************)

    Example ex1 : M (string * string)
    := Mbind db (fun x =>
       Mbind db (fun y =>
       Mguard (x.(title) ?[ eq ] y.(title)) (Mret (x.(director),y.(actor))))).

    Example normalized_ex1' : { x : M (string * string) | Meq x ex1 }.
    normalize.
    Defined.

    Example normalized_ex1 :=
      Eval cbv beta iota zeta delta [ proj1_sig normalized_ex1' normalize_function ]
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
    : { x : M (string * string)
      | EdsSound (title_implies_director :: nil) -> Meq x normalized_ex1 }.
    chase solver.
    Defined.

    Definition universal_ex1 :=
      Eval cbv beta zeta delta [ universal_ex1' proj1_sig conditional_transitive conditional_simpl ]
      in (proj1_sig universal_ex1').

    Eval unfold universal_ex1 in universal_ex1.

    (** Minimization **)
    (******************)

    Example minimized_ex1' : { x : _ | Meq x universal_ex1 }.
    minimize solver'.
    Defined.

    Definition minimized_ex1 :=
      Eval cbv beta iota zeta delta [ Mmap minimized_ex1' proj1_sig unconditional_transitive unconditional_simpl query Mguard ]
      in (proj1_sig minimized_ex1').

    Eval cbv beta iota zeta delta [ Mmap minimized_ex1' proj1_sig unconditional_transitive unconditional_simpl query Mguard ]
      in (proj1_sig minimized_ex1').
    Print minimized_ex1.

    (** Finishing **)
    (***************)

    Definition finished_ex1 : { m : _ | Meq m minimized_ex1 }.
    finisher.
    Defined.

    Eval cbv beta iota zeta delta [ Mmap finished_ex1 proj1_sig unconditional_transitive unconditional_simpl query Mguard ]
      in (proj1_sig finished_ex1).

    (** TODO: This is incomplete **)
    Ltac optimize solver :=
      lazymatch goal with
      | |- { x : _ | Meq x ?X } =>
        normalize ;
        minimize solver ;
        finisher
      | |- { x : _ | _ -> Meq x ?X } =>
        normalize ;
        chase solver ;
        minimize solver ;
        finisher
      end.

    Definition optimized : { m : _ | EdsSound (title_implies_director :: nil) -> Meq m ex1 }.
    Abort.

    Definition tbl_movies : M movie := makeM
      (Movie "Star Trek: Into Darkness" "JJ Abrams" "Benedict Cumberbatch" ::
       Movie "Star Trek: Into Darkness" "JJ Abrams" "Chris Pine" ::
       Movie "Stardust" "Matthew Vaughn" "Claire Danes" ::
       Movie "Stardust" "Matthew Vaughn" "Robert Di Niro" ::
       Movie "Stardust" "Matthew Vaughn" "Charlie Cox" :: nil).

  End over_db.

End Movies.

Require Import SemanticQuery.ListModel.

Time Eval vm_compute in (@ex1 list _ (@tbl_movies list _)).
Time Eval vm_compute in (proj1_sig (@finished_ex1 list _ (@tbl_movies list _))).