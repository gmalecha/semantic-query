Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ExtLib.Data.String.
Require Import ExtLib.Core.RelDec.
Require Import SemanticQuery.Shallow.
Require Import SemanticQuery.ChaseShallow.

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
    Lemma normal_pull_plus_tt
    : forall {U V W : Type} qg (qr : unit -> U) x (y : _ -> _ -> M V),
        Meq (Mbind (query (Mret tt) qg qr)
                   (fun val : U => Mbind x (y val)))
            (Mbind (query x (fun x => qg tt) (fun x => (qr tt, x)))
                   (fun val : U * W => y (fst val) (snd val))).
    Proof. Admitted.
    Lemma normal_pull_plus
    : forall {T U V W : Type} (qb : M T) qg (qr : T -> U) x (y : _ -> _ -> M V),
        Meq (Mbind (query qb qg qr)
                   (fun val : U => Mbind x (y val)))
            (Mbind (query (Mplus qb x) (fun x => qg (fst x)) (fun x => (qr (fst x), snd x)))
                   (fun val : U * W => y (fst val) (snd val))).
    Proof. Admitted.
    Lemma normal_pull_guard_const
    : forall {T U V : Type} (qb : M T) qg (qr : T -> U) f (y : _ -> M V),
        Meq (Mbind (query qb qg qr)
                   (fun val : U => Mguard f (y val)))
            (Mbind (query qb (fun x => f && qg x)%bool qr)
                   (fun val : U => y val)).
    Proof. Admitted.
    Lemma normal_pull_guard
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

    Ltac normalize m :=
      match goal with
      | |- ?X =>
        let H := fresh in
        evar (H : X) ;
          assert (Meq (Mbind (query (Mret tt) (fun _ => true) (fun x => x))
                             (fun _ => m)) H);
          [ subst H ; try unfold m ;
            repeat first [ setoid_rewrite normal_pull_plus_tt
                         | setoid_rewrite normal_pull_plus
                         | setoid_rewrite normal_pull_guard_const
                         | setoid_rewrite normal_pull_guard
                         | eapply normal_pull_ret ]
          | let res := eval unfold H in H in
                                         let res := eval simpl in res in
                                                                   exact res ]
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
    Lemma pick_left {T' U' V} (f' : _ -> V) (x : M V) (y : M T') (k' : M U')
    : Mimpl (Mmap f' k') x ->
      Mimpl (Mmap (fun x => f' (fst x)) (Mplus k' y))
            x.
    Admitted.
    Lemma pick_right {T' U' V} (f' : _ -> V) (x : M V) (y : M T') (k' : M U')
    : Mimpl (Mmap f' k') x ->
      Mimpl (Mmap (fun x => f' (snd x)) (Mplus y k'))
            x.
    Admitted.
    Lemma pick_here {T} (x : M T)
    : Mimpl (Mmap (fun x => x) x) x.
    Admitted.

    Lemma split_bind_map_search C {T T' U U'} (x : M T) (y : M U) f g
          (Z : M (T' * U'))
    : Mimpl (Mmap g Z) y /\ (Mimpl (Mmap f Z) x /\ C) ->
      Mimpl (Mmap (fun xy => (f xy, g xy)) Z)
            (Mplus x y) /\ C.
    Admitted.
    Lemma pick_left_search C {T' U' V} (f' : _ -> V) (x : M V) (y : M T') (k' : M U')
    : Mimpl (Mmap f' k') x /\ C ->
      Mimpl (Mmap (fun x => f' (fst x)) (Mplus k' y))
            x /\ C.
    Admitted.
    Lemma pick_right_search C {T' U' V} (f' : _ -> V) (x : M V) (y : M T') (k' : M U')
    : Mimpl (Mmap f' k') x /\ C ->
      Mimpl (Mmap (fun x => f' (snd x)) (Mplus y k'))
            x /\ C.
    Admitted.
    Lemma pick_here_search {T} (x : M T) (C : Prop)
    : C ->
      Mimpl (Mmap (fun x => x) x) x /\ C.
    Admitted.

    Lemma chase_sound_apply
    : forall (S S' T U : Type) (P : M S) (C : S -> bool)
             (E : S -> T) (F : M S') (Gf : S' -> bool)
             (B : M U) (Gb : S' -> U -> bool),
        embedded_dependency F Gf B Gb ->
        forall h : S -> S',
          (Mimpl (Mmap h P) F /\ forall x : S, C x = true -> Gf (h x) = true) ->
          Meq (query P C E)
              (query (Mplus P B)
                     (fun ab : S * U => (C (fst ab) && Gb (h (fst ab)) (snd ab))%bool)
                     (fun ab : S * U => E (fst ab))).
    Proof. intros. destruct H0.
           eapply chase_sound_general; eauto.
    Qed.

    Instance Reflexive_pointwise_refl {T U} (R : U -> U -> Prop)
             {Refl_R : Reflexive R}
    : Reflexive (Morphisms.pointwise_relation T R).
    Proof.
      red. intros. red. reflexivity.
    Qed.

  Lemma chase_sound_apply_ed_tt
  : forall (S S' T : Type) (P : M S) (C : S -> bool)
           (E : S -> T) (F : M S') (Gf : S' -> bool)
           (Gb : S' -> unit -> bool),
      embedded_dependency F Gf (Mret tt) Gb ->
      forall h : S -> S',
        (Mimpl (Mmap h P) F /\ forall x : S, C x = true -> Gf (h x) = true) ->
        Meq (query P C E)
            (query P
                   (fun ab : S => (C ab && Gb (h ab) tt)%bool)
                   (fun ab : S => E ab)).
  Proof. intros. destruct H0.
         etransitivity.
         { eapply chase_sound_general; eauto. }
         { unfold Mplus. unfold query.
           repeat setoid_rewrite Mbind_assoc.
           eapply Proper_Mbind. reflexivity.
           red. intros.
           repeat setoid_rewrite Mbind_Mret.
           reflexivity. }
  Qed.

  Lemma check_trivial {T} (P Q : T -> Prop) :
    (forall x, Q x) ->
    False ->
    (forall x : T, P x -> Q x).
  Proof.
    clear. firstorder.
  Qed.

  (** TODO: The problem with chase is that it is too trivial **)
  Ltac chase_step solver eds m :=
    let rec discharge :=
      match goal with
      | |- forall x, _ -> _ =>
        solve [ first [ eapply check_trivial ;
                        [ solve [ intros; simpl; solver ]
                        | fail 1 ]
                      | simpl; solver ] ]
      | |- _ /\ _ =>
        first [ match goal with
                | |- Mimpl _ (Mplus _ _) /\ _ =>
                  eapply split_bind_map_search ; discharge
                end
              | simple eapply pick_here_search ; discharge
              | simple eapply pick_left_search ; discharge
              | simple eapply pick_right_search ; discharge ]
      end
    in
    match eds with
    | (?ed1,?ed2) =>
      first [ chase_step solver ed1 m | chase_step solver ed2 m ]
    | ?ed =>
      match goal with
      | |- ?X =>
        let H := fresh in
        evar (H : X) ;
          assert (Meq m H);
          [ subst H ; try unfold m ;
            first [ eapply (@chase_sound_apply_ed_tt _ _ _ _ _ _ _ _ _ ed)
                  | eapply (@chase_sound_apply _ _ _ _ _ _ _ _ _ _ _ ed) ] ;
            discharge
          | let res := eval unfold H in H in
            let res := eval simpl in res in
            exact res ]
      end
    end.

  Ltac chase solver eds m :=
    repeat (chase_step solver eds m).

  Example universal_ex1' : M (string * string).
  chase ltac:(eauto using rel_dec_eq_true with typeclass_instances)
        title_implies_director_sound normalized_ex1.
  Defined.

  Definition universal_ex1 :=
    Eval cbv beta zeta delta [ universal_ex1' ] in universal_ex1'.

  Eval unfold universal_ex1 in universal_ex1.

(*
  Example minimized_ex1 : query scheme (String :: String :: nil) :=
    Eval vm_compute
    in minimize (@check_entails) universal_ex1.
*)

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

  End over_db.

End Movies.