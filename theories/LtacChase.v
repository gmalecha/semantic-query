Require Import Coq.Lists.List.
Require Import SemanticQuery.DataModel.
Require Import SemanticQuery.ChaseShallow.

Set Implicit Arguments.
Set Strict Implicit.

Require Import ExtLib.Core.RelDec.
(* Automation *)
Lemma rel_dec_true_eq : forall {T} {R : T -> T -> Prop} (RD : RelDec R) (ROk : RelDec_Correct RD) a b,
    a ?[ R ] b = true -> R a b.
Proof.
  intros. rewrite rel_dec_correct in H. assumption.
Qed.

(** Refinement lemmas **)
Section refinement_lemmas.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Definition conditional_transitive {T} (P : Prop) (m1 m2 : M T)
    : (P -> Meq m2 m1) ->
      {x : M T | P -> Meq x m1 } ->
      {x : M T | P -> Meq x m2 }.
  Proof.
    intros. destruct X.
    exists x.
    { intro. rewrite H; auto. }
  Defined.

  Definition conditional_reflexive {T} (P : Prop) (m1 : M T)
    : { x : _ | P -> Meq x m1 }.
  Proof.
    exists m1. intro. reflexivity.
  Defined.

  Definition unconditional_transitive {T} (m1 m2 : M T)
  : Meq m2 m1 ->
    {x : M T | Meq x m1 } ->
    {x : M T | Meq x m2 }.
  Proof.
    intros. destruct X.
    exists x.
    { rewrite H; auto. }
  Defined.

  Definition unconditional_reflexive {T} (m1 : M T)
  : { x : _ | Meq x m1 }.
  Proof.
    exists m1. reflexivity.
  Defined.

  Definition conditional_simpl {T} (m1 m2 : M T) (P : Prop)
  : (P -> m1 = m2) ->
    { x : _ | P -> Meq x m1 }.
  Proof.
    exists m2. intros. specialize (H H0). subst. reflexivity.
  Defined.

  Definition unconditional_simpl {T} (m1 m2 : M T)
  : m1 = m2 ->
    { x : _ | Meq x m1 }.
  Proof.
    exists m2. subst. reflexivity.
  Defined.

End refinement_lemmas.

Section normalize_proofs.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Theorem prep_for_normal
    : forall {T} (q : M T),
      Meq (Mbind (query (Mret tt) (fun _ => true) (fun x => x))
                 (fun _ => q)) q.
  Proof. unfold query. intros. rw_M. reflexivity. Qed.

  Lemma normal_pull_plus_tt
    : forall {U V W : Type} qg (qr : unit -> U) x (y : _ -> _ -> M V),
      Meq (Mbind (query (Mret tt) qg qr)
                 (fun val : U => Mbind x (y val)))
          (Mbind (query x (fun x => qg tt) (fun x => (qr tt, x)))
                 (fun val : U * W => y (fst val) (snd val))).
  Proof.
    unfold query; intros. rw_M.
    simpl.
    destruct (qg tt); simpl; rw_M; reflexivity.
  Qed.

  Lemma normal_pull_plus
    : forall {T U V W : Type} (qb : M T) qg (qr : T -> U) x (y : _ -> _ -> M V),
      Meq (Mbind (query qb qg qr)
                 (fun val : U => Mbind x (y val)))
          (Mbind (query (Mplus qb x) (fun x => qg (fst x)) (fun x => (qr (fst x), snd x)))
                 (fun val : U * W => y (fst val) (snd val))).
  Proof.
    unfold query, Mplus; intros. rw_M.
    eapply Proper_Mbind_eq; try reflexivity.
    red. intros. simpl.
    destruct (qg a); simpl; rw_M; try reflexivity.
  Qed.

  Lemma normal_pull_dplus_ret_id
    : forall {T U V W : Type} (qb : M T) qg x (y : _ -> _ -> M V),
      Meq (Mbind (query qb qg (fun x => x))
                 (fun val : T => Mbind (x val) (y val)))
          (Mbind (query (Mdplus qb x) (fun x => qg (fst x)) (fun x => (fst x, snd x)))
                 (fun val : T * W => y (fst val) (snd val))).
  Proof.
    unfold query, Mplus; intros. rw_M.
    eapply Proper_Mbind_eq; try reflexivity.
    red. intros. simpl.
    destruct (qg a); simpl; rw_M; try reflexivity.
  Qed.

  Lemma normal_pull_dplus
    : forall {T U V W : Type} (qb : M T) qg (qr : T -> U) x (y : _ -> _ -> M V),
      Meq (Mbind (query qb qg qr)
                 (fun val : U => Mbind (x val) (y val)))
          (Mbind (query (Mdplus qb (fun y => x (qr y))) (fun x => qg (fst x)) (fun x => (qr (fst x), snd x)))
                 (fun val : U * W => y (fst val) (snd val))).
  Proof.
    unfold query, Mplus; intros. rw_M.
    eapply Proper_Mbind_eq; try reflexivity.
    red. intros. simpl.
    destruct (qg a); simpl; rw_M; try reflexivity.
  Qed.


  Lemma normal_pull_guard_const
    : forall {T U V : Type} (qb : M T) qg (qr : T -> U) f (y : _ -> M V),
      Meq (Mbind (query qb qg qr)
                 (fun val : U => Mguard f (y val)))
          (Mbind (query qb (fun x => f && qg x)%bool qr)
                 (fun val : U => y val)).
  Proof.
    unfold query; intros; rw_M.
    eapply Proper_Mbind_eq; try reflexivity.
    red; intros.
    repeat setoid_rewrite Mbind_Mguard. rw_M.
    rewrite Mguard_perm. rewrite Mguard_and.
    reflexivity.
  Qed.

  Lemma normal_pull_guard
    : forall {T U V : Type} (qb : M T) qg (qr : T -> U) f (y : _ -> M V),
      Meq (Mbind (query qb qg qr)
                 (fun val : U => Mguard (f val) (y val)))
          (Mbind (query qb (fun x => qg x && f (qr x))%bool qr)
                 (fun val : U => y val)).
  Proof.
    unfold query; intros; rw_M.
    eapply Proper_Mbind_eq; try reflexivity.
    red. intros.
    setoid_rewrite Mguard_and.
    reflexivity.
  Qed.

  Lemma normal_pull_ret
    : forall {T U V : Type} (qb : M T) qg (qr : T -> U) (y : _ -> V),
      Meq (Mbind (query qb qg qr)
                 (fun val : U => Mret (y val)))
          (query qb qg (fun x => y (qr x))).
  Proof.
    unfold query. simpl; intros; rw_M. reflexivity.
  Qed.

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
    revert H.
    rw_M.
    symmetry. assumption.
  Defined.

  Definition normalize_function_ed {T} (m m' m'' : M T) (P : Prop)
  : Meq (Mbind (query (Mret tt) (fun _ => true) (fun x => x)) (fun _ => m))
        m' ->
    m' = m'' ->
    { x : M T | P -> Meq x m }.
  Proof.
    intros.
    exists m''.
    subst.
    unfold query in *.
    revert H.
    rw_M.
    symmetry. assumption.
  Defined.


End normalize_proofs.

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
  | |- { x : ?X | _ -> Meq x ?m } =>
    eapply normalize_function_ed ;
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

Section chase_proofs.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Lemma split_bind_map {T T' U U'} (x : M T) (y : M U) f g
        (Z : M (T' * U'))
  : Mimpl (Mmap g Z) y ->
    Mimpl (Mmap f Z) x ->
    Mimpl (Mmap (fun xy => (f xy, g xy)) Z)
          (Mplus x y).
  Proof.
    intros. rewrite <- H; clear H. rewrite <- H0; clear H0.
    rewrite Mplus_Mmap_L. rewrite Mplus_Mmap_R.
    rewrite Mmap_compose. simpl.
    unfold Mmap, Mplus.
    rw_M.
    generalize (@Mbind_dup M _ _ _ Z (fun xy => Mret (f (fst xy), g (snd xy)))). simpl.
    intros. eapply H.
  Qed.

  Lemma pick_left {T' U' V} (f' : _ -> V) (x : M V) (y : M T') (k' : M U')
  : Mimpl (Mmap f' k') x ->
    Mimpl (Mmap (fun x => f' (fst x)) (Mplus k' y))
          x.
  Proof.
    intros. rewrite <- H; clear H.
    rw_M. simpl. setoid_rewrite Mbind_ignore.
    reflexivity.
  Qed.

  Lemma pick_right {T' U' V} (f' : _ -> V) (x : M V) (y : M T') (k' : M U')
    : Mimpl (Mmap f' k') x ->
      Mimpl (Mmap (fun x => f' (snd x)) (Mplus y k'))
            x.
  Proof.
    intros. rewrite <- H; clear H.
    rw_M. simpl. rewrite Mbind_ignore. reflexivity.
  Qed.

  Lemma pick_here {T} (x : M T)
    : Mimpl (Mmap (fun x => x) x) x.
  Proof. rewrite Mmap_id. reflexivity. Qed.

  Lemma check_query_morphism_apply
  : forall (S S' T : Type)
           (P : M S) (C : S -> bool) (E : S -> T)
           (P' : M S') (C' : S' -> bool) (E' : S' -> T),
      forall h : S -> S',
        Mimpl (Mmap h P) P' ->
        (forall x, C x = true -> E x = E' (h x)) ->
        (forall x : S, C x = true -> C' (h x) = true) ->
        Mimpl (query P C E) (query P' C' E').
  Proof.
    clear. unfold query. intros.
    setoid_rewrite <- H.
    rewrite Mmap_Mbind.
    eapply Proper_Mbind_impl; try reflexivity.
    red. intros.
    specialize (H0 a). specialize (H1 a).
    destruct (C a); auto.
    { rewrite H0; auto. rewrite H1; auto. reflexivity. }
    { simpl. eapply Mimpl_Mzero. }
  Qed.

  Lemma chase_sound_apply
    : forall (S S' T U : Type) (P : M S) (C : S -> bool)
             (E : S -> T) (F : M S') (Gf : S' -> bool)
             (B : M U) (Gb : S' -> U -> bool),
      forall h : S -> S',
        Mimpl (Mmap h P) F ->
        (forall x : S, C x = true -> Gf (h x) = true) ->
        embedded_dependency F Gf B Gb ->
        Meq (query P C E)
            (query (Mplus P B)
                   (fun ab : S * U => (C (fst ab) && Gb (h (fst ab)) (snd ab))%bool)
                   (fun ab : S * U => E (fst ab))).
  Proof.
    intros.
    eapply chase_sound_general; eauto.
  Qed.

  Lemma chase_sound_apply_ed_tt
    : forall (S S' T : Type) (P : M S) (C : S -> bool)
             (E : S -> T) (F : M S') (Gf : S' -> bool)
             (Gb : S' -> unit -> bool),
      forall h : S -> S',
        Mimpl (Mmap h P) F ->
        (forall x : S, C x = true -> Gf (h x) = true) ->
        embedded_dependency F Gf (Mret tt) Gb ->
        Meq (query P C E)
            (query P
                   (fun ab : S => (C ab && Gb (h ab) tt)%bool)
                   (fun ab : S => E ab)).
  Proof.
    intros.
    etransitivity.
    { eapply chase_sound_general; eauto. }
    { unfold Mplus. unfold query.
      repeat setoid_rewrite Mbind_assoc.
      eapply Proper_Mbind_eq. reflexivity.
      red. intros.
      repeat setoid_rewrite Mbind_Mret.
      reflexivity. }
  Qed.

  Definition pick_dup
    : forall {T U U' : Type} (m : M T) (u : M U) (u' : M U') f g,
      Mimpl (Mmap f m) u ->
      Mimpl (Mmap g m) u' ->
      Mimpl (Mmap (fun x => (f x, g x)) m) (Mplus u u').
  Proof.
    unfold Mmap, Mplus; intros.
    rewrite <- H; clear H.
    rw_M.
    rewrite Mbind_perm.
    rewrite <- H0.
    rw_M.
    generalize (Mbind_dup m (fun xy => Mret (f (snd xy), g (fst xy)))).
    simpl. intro. rewrite <- H. reflexivity.
  Qed.

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
    induction ps; simpl.
    { tauto. }
    { intros. rewrite IHps. tauto. }
  Qed.

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

End chase_proofs.

Ltac find_bind_morphism :=
  lazymatch goal with
  | |- Mimpl (Mmap _ ?D) (Mplus ?A ?B) =>
      (eapply split_bind_map ; find_bind_morphism)
    + (match A with
       | context [ D ] =>
         match B with
         | context [ D ] =>
           eapply pick_dup ; find_bind_morphism
         end
       end)
  | |- Mimpl _ _  =>
    (** Here I should have something that is atomic **)
      (simple eapply pick_here ; find_bind_morphism)
    + (simple eapply pick_left ; find_bind_morphism)
    + (simple eapply pick_right ; find_bind_morphism)
  end.

(** DEBUGGING **)
Ltac pg :=
  match goal with
  | |- ?X => idtac X
  end.

Ltac prove_query_morphism solver :=
  instantiate ;
  eapply check_query_morphism_apply ;
  [ find_bind_morphism
  | simpl ; solve [ solver ]
  | simpl ; solve [ solver ] ].

Ltac prove_query_isomorphism solver :=
  match goal with
  | |- Meq ?A ?B =>
    try unfold A ; try unfold B ;
    split; prove_query_morphism solver
  end.

Ltac chase_ed solver m :=
  try unfold m ;
  match goal with
  | |- _ -> Meq ?pre ?post =>
    first [ refine (@chase_sound_apply_ed_tt _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          | refine (@chase_sound_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ] ;
      [ shelve
      | solve [ find_bind_morphism ]
      | first [ let forget := constr:( $( solve [ prove_query_isomorphism solver ] )$ : Meq pre post) in
                fail 1
              | simpl; solve [ solver ] ] ]
  end.

Ltac ed_search :=
    (simple apply EdsSound_hd)
  + (simple apply EdsSound_tl ; ed_search)
  + (simple apply EdsSound_start ; ed_search)
  + (simple apply EdsSound_end ; ed_search).


Ltac chase solver :=
  lazymatch goal with
  | |- { x : _ | _ -> Meq x ?m } =>
    repeat first [ eapply conditional_transitive ;
                   [ solve [ ed_search ; chase_ed solver m ]
                   | idtac "chased" ]
                 | eapply conditional_reflexive ]
  | |- { x : _ | Meq x ?m } =>
    eapply unconditional_reflexive (** there are no eds **)
  end.

Section minimize_lemmas.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Lemma query_assoc_Mplus
  : forall {T U V W : Type} (qb : M T) (qb' : M U) (qb'' : M V) qg (qr : _ -> W),
      Meq (query (Mplus (Mplus qb qb') qb'') qg qr)
          (query (Mplus qb (Mplus qb' qb''))
                 (fun xyz => qg (fst xyz, fst (snd xyz), snd (snd xyz)))
                 (fun xyz => qr (fst xyz, fst (snd xyz), snd (snd xyz)))).
  Proof.
    intros; unfold query, Mplus; rw_M. reflexivity.
  Qed.

  Lemma query_assoc_Mplus'
  : forall {T U V W : Type} (qb : M T) (qb' : M U) (qb'' : M V) qg (qr : _ -> W),
      Meq (query (Mplus qb (Mplus qb' qb'')) qg qr)
          (query (Mplus (Mplus qb qb') qb'')
                 (fun xyz => qg (fst (fst xyz), (snd (fst xyz), snd xyz)))
                 (fun xyz => qr (fst (fst xyz), (snd (fst xyz), snd xyz)))).
  Proof.
    intros; unfold query, Mplus; rw_M. reflexivity.
  Qed.

  Lemma minimize_drop
  : forall {T T' V : Type} (qb : M T) (qb' : M T') qg (qr : _ -> V) f (qb'' : M T') qg'',
      (Mimpl (Mmap f qb') qb /\
       Meq (query (Mplus qb qb') qg qr)
           (query qb' (fun y => qg (f y,y)) (fun y => qr (f y,y)))) ->
      Meq (query qb' (fun y => qg (f y,y)) (fun y => qr (f y,y)))
          (query qb'' (fun y => qg'' (f y,y)) (fun y => qr (f y,y))) ->
      Meq (query (Mplus qb qb') qg qr)
          (query (Mmap (fun x => (f x, x)) qb'') qg'' qr).
  Proof.
    unfold query, Mplus. intros.
    destruct H. clear H.
    rewrite <- H1 in H0; clear H1.
    rewrite H0; clear H0.
    unfold Mmap. rw_M.
    reflexivity.
  Qed.

  Lemma minimize_keep
  : forall {T T' V : Type} (qb : M T) (qb' : M T') qg (qr : _ -> V) (qb'' : M T') qg'',
      (forall x,
          Meq (query qb' (fun y => qg (x,y)) (fun y => qr (x,y)))
              (query qb'' (fun y => qg'' (x,y)) (fun y => qr (x,y)))) ->
      Meq (query (Mplus qb qb') qg qr)
          (query (Mplus qb qb'') qg'' qr).
  Proof.
    unfold query. intros.
    rw_M. eapply Proper_Mbind_eq; try reflexivity. eauto.
  Qed.

  Lemma minimize_const
  : forall {T T' V : Type} (qb' : M T') qg (qr : _ -> V) (qb'' : M T') qg'' (v : T),
      Meq (query qb' (fun y => qg (v,y)) (fun y => qr (v,y)))
          (query qb'' (fun y => qg'' (v,y)) (fun y => qr (v,y))) ->
      Meq (query (Mplus (Mret v) qb') qg qr)
          (query qb'' (fun y => qg'' (v,y)) (fun y => qr (v,y))).
  Proof.
    intros. rewrite <- H; clear H.
    unfold query. rw_M. reflexivity.
  Qed.

  Lemma minimize_last
  : forall {T V : Type} (qb : M T) qg (qr : _ -> V) qg',
      (forall x, qg x = qg' x) ->
      Meq (query qb qg qr) (query qb qg' qr).
  Proof.
    unfold query. intros.
    eapply Proper_Mbind_eq. reflexivity.
    intro.
    rewrite H. reflexivity.
  Qed.
End minimize_lemmas.

Ltac drop_dup solver :=
  let rec search :=
        (simple eapply pick_here)
      + (simple eapply pick_left ; simple eapply pick_here)
      + (simple eapply pick_right ; search)
  in
  match goal with
  | |- Meq _ _ =>
    repeat first [ simple eapply minimize_const
                 | eapply minimize_drop ;
                   [ solve [ split ; [ search | prove_query_isomorphism solver ] ]
                   | ]
                 | simple eapply minimize_keep
                 | simple eapply minimize_last ;
                   [ simpl; intros ;
                     repeat (rewrite rel_dec_eq_true by eauto with typeclass_instances) ]
                 ]
  end.

Ltac solve_conclusion :=
  try reflexivity ;
  match goal with
  | |- ?X = _ (@pair ?T ?U ?x ?y) =>
    let X' := eval pattern x in X in
    match X' with
    | ?F _ =>
      let F' := eval pattern y in F in
      match F' with
      | ?F' _ =>
        let F' := eval cbv beta in (fun xy : T * U => F' (fst xy) (snd xy)) in
        change X with (F' (x,y))
      end
    end
  end ;
  match goal with
  | |- ?X ?Y = ?Z ?Y =>
    let x := constr:(@eq_refl _ X : X = Z) in
    reflexivity
  end.

Ltac minimize solver :=
  (** TODO: This is sub-optimal **)
  let kont :=
      (repeat rewrite query_assoc_Mplus) ;
      drop_dup solver
  in
  lazymatch goal with
  | |- { x : _ | Meq x ?m } =>
    eapply unconditional_transitive ;
      [ try unfold m ; kont ; solve [ solve_conclusion ]
      | eapply unconditional_simpl; simpl; reflexivity ]
  | |- { x : _ | _ -> Meq x ?m } =>
    eapply conditional_transitive ;
      [ intro ; try unfold m ; kont ; solve [ solve_conclusion ]
      | eapply conditional_simpl; intro ; simpl; reflexivity ]
  end.

Ltac finisher :=
  lazymatch goal with
  | |- { x : _ | Meq x ?X } =>
    eexists ; symmetry ; try unfold X ;
    unfold query, Mmap ; rw_M ; simpl ; reflexivity
  | |- { x : _ | _ -> Meq x ?X } =>
    eexists ; intro; symmetry ; try unfold X ;
    unfold query, Mmap ; rw_M ; simpl ; reflexivity
  end.
