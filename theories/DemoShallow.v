Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ExtLib.Data.String.
Require Import ExtLib.Core.RelDec.
Require Import SemanticQuery.Shallow.
(* Require Import SemanticQuery.ChaseShallow. *)

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
    embedded_dependency (Mbind db (fun x => Mbind db (fun y => Mret (x,y))))
                        (fun xy => (fst xy).(title) ?[ eq ] (snd xy).(title))
                        (Mret tt)
                        (fun xy _ => (fst xy).(director) ?[ eq ] (snd xy).(director)).

  Variable title_implies_director_sound : title_implies_director.

  Example ex1 : M (string * string)
  := Mbind db (fun x =>
     Mbind db (fun y =>
     Mguard (x.(title) ?[ eq ] y.(title)) (Mret (x.(director),y.(actor))))).

  Theorem prep_for_normal
  : forall {T} (q : M T),
      Meq (Mbind (query (Mret tt) (fun _ => true) (fun x => x))
                 (fun _ => q)) q.
  Proof. Admitted.
  Lemma normal_pull_bind_plus
  : forall {T U V W : Type} (qb : M T) qg (qr : T -> U) x (y : _ -> _ -> M V),
      Meq (Mbind (query qb qg qr)
                 (fun val : U => Mbind x (y val)))
          (Mbind (query (Mplus qb x) (fun x => qg (fst x)) (fun x => (qr (fst x), snd x)))
                 (fun val : U * W => y (fst val) (snd val))).
  Proof. Admitted.
  Lemma normal_pull_guard_plus
  : forall {T U V : Type} (qb : M T) qg (qr : T -> U) f (y : _ -> M V),
      Meq (Mbind (query qb qg qr)
                 (fun val : U => Mguard (f val) (y val)))
          (Mbind (query qb (fun x => qg x && f (qr x))%bool qr)
                 (fun val : U => y val)).
  Proof. Admitted.
  Lemma normal_pull_ret
  : forall {T U V : Type} (qb : M T) qg (qr : T -> U) (y : _ -> V),
      Meq (Mbind (query qb qg qr)
                 (fun val : U => Mret (y val)))
          (query qb qg (fun x => y (qr x))).
  Proof. Admitted.
  Lemma Mplus_Mret_tt : forall {U T} (qb : M T) qg (qr : _ -> U),
      Meq (query (Mplus (Mret tt) qb) qg qr)
          (query qb (fun x => qg (tt,x)) (fun x => qr (tt,x))).
  Proof. Admitted.


  Ltac normalize m :=
    match goal with
    | |- ?X =>
      let H := fresh in
      evar (H : X) ;
      assert (Meq (Mbind (query (Mret tt) (fun _ => true) (fun x => x))
                         (fun _ => m)) H);
      [ subst H ; try unfold m ;
        repeat first [ setoid_rewrite Mplus_Mret_tt
                     | setoid_rewrite normal_pull_bind_plus
                     | setoid_rewrite normal_pull_guard_plus
                     | eapply normal_pull_ret ]
      | exact H ]
    end.


  Example normalized_ex1' : M (string * string).
  normalize ex1.
  Defined.

  Example normalized_ex1 :=
    Eval cbv beta zeta delta [ normalized_ex1' ] in normalized_ex1'.

  Lemma split_bind_map {T T' U U'} (x : M T) (y : M U) f g
         (Z : M (T' * U'))
  : Mimpl (Mmap g Z) y ->
    Mimpl (Mmap f Z) x ->
    Mimpl (Mmap (fun xy => (f xy, g xy)) Z)
          (Mplus x y).
  Admitted.
  Lemma pick_first {T U'} (x : M T) (k' : M U')
  : Mimpl (Mmap (fun x => snd x) (Mplus k' x))
          x.
  Admitted.
  Lemma pick_skip {T' U' V} (f' : _ -> V) (x : M V) (y : M T') (k' : M U')
  : Mimpl (Mmap f' k') x ->
    Mimpl (Mmap (fun x => f' (fst x)) (Mplus k' y))
          x.
  Admitted.

  Require Import SemanticQuery.ChaseShallow.

  Ltac chase eds m :=
    match eds with
    | (?ed1,?ed2) =>
      first [ chase ed1 m | chase ed2 m ]
    | ?ed =>
      match goal with
      | |- ?X =>
        let H := fresh in
        evar (H : X) ;
          assert (Meq m H);
          [ subst H ; try unfold m ;
            eapply (@chase_sound_general _ _ _ _ _ _ _ _ _ _ _ _ _ ed)
          | exact H ]
      end
    end.

  Example universal_ex1' : M (string * string).
  chase title_implies_director_sound normalized_ex1.
  { eapply split_bind_map.
    { eapply pick_first. }
    { eapply pick_skip. eapply pick_first. } }
  { simpl. intros. eauto. }
  Defined.

  Definition universal_ex1 :=
    Eval cbv beta zeta delta [ universal_ex1' ] in universal_ex1'.

  Example minimized_ex1 : query scheme (String :: String :: nil) :=
    Eval vm_compute
    in minimize (@check_entails) universal_ex1.

(*
  Definition mkTable {T} (l : list T) : M T :=
    fun x => List.In x l.

  Definition tbl_movies : M movie := mkTable
    (Movie "Star Trek: Into Darkness" "JJ Abrams" "Benedict Cumberbatch" ::
     Movie "Star Trek: Into Darkness" "JJ Abrams" "Chris Pine" ::
     Movie "Stardust" "Matthew Vaughn" "Claire Danes" ::
     Movie "Stardust" "Matthew Vaughn" "Robert Di Niro" ::
     Movie "Stardust" "Matthew Vaughn" "Charlie Cox" :: nil).
*)


End Movies.
v