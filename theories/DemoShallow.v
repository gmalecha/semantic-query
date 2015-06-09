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

(*
    Variable title_implies_director_sound : title_implies_director.
*)

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

    Definition normalize_function {T} (m m' m'' : M T)
    : Meq (Mbind (query (Mret tt) (fun _ => true) (fun x => x)) (fun _ => m))
          m' ->
      m' = m'' ->
      { x : M T | Meq x m }.
    Proof.
      intros.
      exists m''.
      subst.
      unfold query in *.
      repeat first [ setoid_rewrite Mbind_assoc in H
                   | setoid_rewrite Mbind_Mret in H
                   | setoid_rewrite Mret_Mbind in H ].
      symmetry. assumption.
    Defined.

    Ltac normalize :=
      match goal with
      | |- { x : ?X | Meq x ?m } =>
        eapply normalize_function ;
        [ try unfold m ;
          repeat first [ setoid_rewrite normal_pull_plus_tt
                       | setoid_rewrite normal_pull_plus
                       | setoid_rewrite normal_pull_guard_const
                       | setoid_rewrite normal_pull_guard
                       | eapply normal_pull_ret ]
        | match goal with
          | |- ?result = _ =>
            let res := eval simpl in result in
            exact (@eq_refl _ res)
          end ]
      end.

    Example normalized_ex1' : { x : M (string * string) | Meq x ex1 }.
    normalize.
    Defined.

    Example normalized_ex1 :=
      Eval cbv beta iota zeta delta [ proj1_sig normalized_ex1' normalize_function ]
      in (proj1_sig normalized_ex1').

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

    Require Import Coq.Classes.Morphisms.
    Global Instance Reflexive_pointwise {A B : Type} (R : B -> B -> Prop) (ReflR : Reflexive R)
      : Reflexive (pointwise_relation A R).
    Proof.
      clear - ReflR. red. red. intros. reflexivity.
    Qed.
    Theorem Mmap_Mbind : forall {A B C} (f : A -> B) (c : M A) (k : _ -> M C),
        Meq (Mbind (Mmap f c) k)
            (Mbind c (fun x => k (f x))).
    Proof. clear.
           intros. unfold Mmap.
           rewrite Mbind_assoc. setoid_rewrite Mbind_Mret. reflexivity.
    Qed.
    Axiom Mimpl_Mzero : forall {T} (c : M T),
        Mimpl Mzero c.
    Lemma Proper_Mguard_impl {A}
      : Proper (Bool.leb ==> Mimpl ==> Mimpl) (@Mguard M _ A).
    Proof.
      do 3 red. intros.
      red in H. destruct x; subst; simpl; auto.
      eapply Mimpl_Mzero.
    Qed.

    Lemma check_query_morphism_apply
    : forall (S S' T : Type)
             (P : M S) (C : S -> bool) (E : S -> T)
             (P' : M S') (C' : S' -> bool) (E' : S' -> T),
        forall h : S -> S',
          (Mimpl (Mmap h P) P' /\ (forall x : S, C x = true -> C' (h x) = true) /\ (forall x, E x = E' (h x))) ->
          Mimpl (query P C E) (query P' C' E').
    Proof.
      clear. unfold query. intros.
      destruct H.
      setoid_rewrite <- H.
      rewrite Mmap_Mbind.
      destruct H0.
      eapply Proper_Mbind_impl; try reflexivity.
      red. intros.
      rewrite <- H1.
      eapply Proper_Mguard_impl; try reflexivity.
      red. specialize (H0 a).
      destruct (C a); auto.
    Qed.

    Lemma chase_sound_apply
    : forall (S S' T U : Type) (P : M S) (C : S -> bool)
             (E : S -> T) (F : M S') (Gf : S' -> bool)
             (B : M U) (Gb : S' -> U -> bool),
        forall h : S -> S',
          (Mimpl (Mmap h P) F /\ forall x : S, C x = true -> Gf (h x) = true) ->
          embedded_dependency F Gf B Gb ->
          Meq (query P C E)
              (query (Mplus P B)
                     (fun ab : S * U => (C (fst ab) && Gb (h (fst ab)) (snd ab))%bool)
                     (fun ab : S * U => E (fst ab))).
    Proof.
      intros. destruct H.
      eapply chase_sound_general; eauto.
    Qed.

    Lemma chase_sound_apply_ed_tt
    : forall (S S' T : Type) (P : M S) (C : S -> bool)
               (E : S -> T) (F : M S') (Gf : S' -> bool)
               (Gb : S' -> unit -> bool),
        forall h : S -> S',
          (Mimpl (Mmap h P) F /\ forall x : S, C x = true -> Gf (h x) = true) ->
          embedded_dependency F Gf (Mret tt) Gb ->
          Meq (query P C E)
              (query P
                     (fun ab : S => (C ab && Gb (h ab) tt)%bool)
                     (fun ab : S => E ab)).
    Proof.
      intros. destruct H.
      etransitivity.
      { eapply chase_sound_general; eauto. }
      { unfold Mplus. unfold query.
        repeat setoid_rewrite Mbind_assoc.
        eapply Proper_Mbind_eq. reflexivity.
        red. intros.
        repeat setoid_rewrite Mbind_Mret.
        reflexivity. }
    Qed.

    Ltac find_bind_morphism continue :=
      match goal with
      | |- Mimpl _ (Mplus _ _) /\ _ =>
        first [ eapply split_bind_map_search ; find_bind_morphism continue
              | fail 2 ]
      | |- Mimpl _ _ /\ _ =>
        (** Here I should have somethign that is atomic **)
        first [ simple eapply pick_here_search ; find_bind_morphism continue
              | simple eapply pick_left_search ; find_bind_morphism continue
              | simple eapply pick_right_search ; find_bind_morphism continue
              | fail 2 ]
      | |- _ => continue
      end.

    Ltac pg :=
      match goal with
      | |- ?X => idtac X
      end.

    Ltac check_query_morphism solver from to :=
      assert (Mimpl from to);
      [ instantiate ;
        try unfold from ; try unfold to ;
        instantiate ;
        eapply check_query_morphism_apply ;
        find_bind_morphism ltac:(simpl; split; solve [ solver ])
      | ].

    Fixpoint EdsSound (ls : list Prop) : Prop :=
      match ls with
      | nil => True
      | l :: ls => l /\ EdsSound ls
      end.

    Lemma EdsSound_hd : forall (p : Prop) (ps : list Prop) (P : Prop),
        (p -> P) ->
        (EdsSound (p :: ps) -> P).
    Proof.
      simpl. tauto.
    Defined.

    Lemma EdsSound_tl : forall (p : Prop) (ps : list Prop) (P : Prop),
        (EdsSound ps -> P) ->
        (EdsSound (p :: ps) -> P).
    Proof.
      simpl. tauto.
    Defined.

    Lemma EdsSound_app : forall (ps ps' : list Prop),
        EdsSound (ps ++ ps') <-> (EdsSound ps /\ EdsSound ps').
    Proof.
    Admitted.

    Lemma EdsSound_start : forall (ps ps' : list Prop) (P : Prop),
        (EdsSound ps -> P) ->
        (EdsSound (ps ++ ps') -> P).
    Proof.
      simpl. intros. eapply EdsSound_app in H0. tauto.
    Defined.

    Lemma EdsSound_end : forall (ps ps' : list Prop) (P : Prop),
        (EdsSound ps' -> P) ->
        (EdsSound (ps ++ ps') -> P).
    Proof.
      simpl. intros. eapply EdsSound_app in H0. tauto.
    Defined.

    Ltac chase_ed solver m :=
      try unfold m ;
      match goal with
      | |- _ -> Meq ?pre ?post =>
        first [ refine (@chase_sound_apply_ed_tt _ _ _ _ _ _ _ _ _ _ _)
              | eapply (@chase_sound_apply _ _ _ _ _ _ _ _ _ _ _ _ _) ] ;
          find_bind_morphism
            ltac:(first [ check_query_morphism solver pre post ;
                          check_query_morphism solver post pre ;
                          fail 1
                        | simpl; solve [ solver ] ] )
      end.

    Ltac ed_search kontinue :=
      first [ simple apply EdsSound_hd ; kontinue
            | simple apply EdsSound_tl ; ed_search kontinue
            | simple apply EdsSound_start ; ed_search kontinue
            | simple apply EdsSound_end ; ed_search kontinue
            | kontinue ].

  Definition transitive_with_eds {T} (P : Prop) (m1 m2 : M T)
  : (P -> Meq m2 m1) ->
    {x : M T | P -> Meq x m1 } ->
    {x : M T | P -> Meq x m2 }.
  Proof.
    intros. destruct X.
    exists x.
    { intro. rewrite H; auto. }
  Defined.

  Definition reflexive_with_eds {T} (P : Prop) (m1 : M T)
  : { x : _ | P -> Meq x m1 }.
  Proof.
    exists m1. intro. reflexivity.
  Defined.

  Ltac chase solver :=
    repeat match goal with
           | |- { x : _ | EdsSound _ -> Meq x ?m } =>
             first [ eapply transitive_with_eds ;
                     [ solve [ ed_search ltac:(chase_ed solver m) ]
                     | idtac "chased" ]
                   | eapply reflexive_with_eds ]
           end.

  Ltac solver :=
    intros;
    repeat match goal with
           | H : andb ?X ?Y = true |- _ =>
             apply Bool.andb_true_iff in H ; destruct H
           | |- andb _ _ = true =>
             apply Bool.andb_true_iff ; split
           end ;
    eauto using rel_dec_eq_true with typeclass_instances.

  Example universal_ex1'
  : { x : M (string * string)
    | EdsSound (title_implies_director :: nil) -> Meq x normalized_ex1 }.
  chase solver.
  Defined.

  Definition universal_ex1 :=
    Eval cbv beta zeta delta [ universal_ex1' proj1_sig transitive_with_eds reflexive_with_eds ]
    in (proj1_sig universal_ex1').

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