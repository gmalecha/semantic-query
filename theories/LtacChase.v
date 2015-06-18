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

Ltac prep :=
  match goal with
  | |- Meq ?x ?m =>
    first [ is_evar x ; try unfold m
          | is_evar m ; symmetry ; try unfold x ]
  | |- _ -> Meq ?x ?m =>
    first [ is_evar x ; try unfold m
          | is_evar m ; let y := fresh in intro y ; symmetry ; revert y ; try unfold x ]
  | |- { x : _ | _ -> Meq _ _ } => eexists ; prep
  | |- { x : _ | Meq _ _ } => eexists ; prep
  end.

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

  Lemma refine_transitive : forall {T} (a b c : M T),
      Meq b c ->
      Meq a b ->
      Meq a c.
  Proof. intros. etransitivity; eassumption. Qed.

  Lemma refine_transitive_under : forall {T} (a b c : M T) (P : Prop),
      (P -> Meq b c) ->
      (P -> Meq a b) ->
      (P -> Meq a c).
  Proof. intros. etransitivity; eauto. Qed.

  Lemma refine_transitive_under_flip : forall {T} (a b c : M T) (P : Prop),
      (P -> Meq a b) ->
      (P -> Meq b c) ->
      (P -> Meq c a).
  Proof. intros. symmetry; etransitivity; eauto. Qed.

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
          (Mbind (query (Mprod qb x) (fun x => qg (fst x)) (fun x => (qr (fst x), snd x)))
                 (fun val : U * W => y (fst val) (snd val))).
  Proof.
    unfold query, Mprod; intros. rw_M.
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
    unfold query, Mprod; intros. rw_M.
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
    unfold query, Mprod; intros. rw_M.
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

  Definition normalize_function {T} (m : M T)
  : Meq m (Mbind (query (Mret tt) (fun _ => true) (fun x => x)) (fun _ => m)).
  Proof.
    unfold query in *.
    rw_M. reflexivity.
  Qed.

End normalize_proofs.

Ltac normalize :=
  intros;
  match goal with
  | |- Meq ?x ?m =>
    first [ is_evar x ; rewrite (@normalize_function _ _ _ m) ; try unfold m
          | is_evar m ; rewrite (@normalize_function _ _ _ x) ; try unfold x ]
  end ;
  repeat first [ setoid_rewrite normal_pull_plus_tt
               | setoid_rewrite normal_pull_plus
               | setoid_rewrite normal_pull_guard_const
               | setoid_rewrite normal_pull_guard
               | setoid_rewrite normal_pull_ret ] ;
  simpl ; reflexivity.

Section chase_proofs.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Definition pick_split
    : forall {T U U' : Type} (m : M T) (u : M U) (u' : M U') f g,
      Mimpl (Mmap f m) u ->
      Mimpl (Mmap g m) u' ->
      Mimpl (Mmap (fun x => (f x, g x)) m) (Mprod u u').
  Proof.
    unfold Mmap, Mprod; intros.
    rewrite <- H; clear H.
    rw_M.
    rewrite Mbind_perm.
    rewrite <- H0.
    rw_M.
    generalize (Mbind_dup m (fun xy => Mret (f (snd xy), g (fst xy)))).
    simpl. intro. rewrite <- H. reflexivity.
  Qed.

  Lemma pick_left {T' U' V} (f' : _ -> V) (x : M V) (y : M T') (k' : M U')
  : Mimpl (Mmap f' k') x ->
    Mimpl (Mmap (fun x => f' (fst x)) (Mprod k' y))
          x.
  Proof.
    intros. rewrite <- H; clear H.
    rw_M. simpl. setoid_rewrite Mbind_ignore.
    reflexivity.
  Qed.

  Lemma pick_right {T' U' V} (f' : _ -> V) (x : M V) (y : M T') (k' : M U')
    : Mimpl (Mmap f' k') x ->
      Mimpl (Mmap (fun x => f' (snd x)) (Mprod y k'))
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
            (query (Mprod P B)
                   (fun ab : S * U => (C (fst ab) && Gb (h (fst ab)) (snd ab))%bool)
                   (fun ab : S * U => E (fst ab))).
  Proof.
    eauto using chaseable.
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
    { eauto using chaseable. }
    { unfold Mprod. unfold query.
      repeat setoid_rewrite Mbind_assoc.
      eapply Proper_Mbind_eq. reflexivity.
      red. intros.
      repeat setoid_rewrite Mbind_Mret.
      reflexivity. }
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
  | |- Mimpl (Mmap _ ?D) (Mprod ?A ?B) =>
      (eapply pick_split ; find_bind_morphism)
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
  once (instantiate ;
        eapply check_query_morphism_apply ;
        [ find_bind_morphism
        | simpl ; solve [ solver ]
        | simpl ; solve [ solver ] ]).

Ltac prove_query_homomorphic_equivalent solver :=
  match goal with
  | |- Meq ?A ?B =>
    try unfold A ; try unfold B ;
    split; prove_query_morphism solver
  end.

Ltac chase_ed solver :=
  match goal with
  | |- _ -> Meq ?pre ?post =>
    try unfold post ;
    first [ refine (@chase_sound_apply_ed_tt _ _ _ _ _ _ _ _ _ _ _ _ _ _)
          | refine (@chase_sound_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ] ;
      [ shelve
      | solve [ find_bind_morphism ]
      | first [ let forget := constr:( $( solve [ prove_query_homomorphic_equivalent solver ] )$ : Meq pre post) in
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
  | |- ?Z -> Meq ?x ?m =>
    try (has_evar Z ; fail 10000 "premises contains evar") ;
    first [ is_evar x
          | is_evar m ; let y := fresh in intro y ; symmetry ; revert y ] ;
    repeat first [ refine (@refine_transitive_under_flip _ _ _ _ _ _ _ _ _) ;
                   [ shelve
                   | once solve [ ed_search ; chase_ed solver m ]
                   | ]
                 | simpl ; reflexivity ]
  | |- Meq ?x ?m => simpl ; reflexivity
  end.

Definition Find {T} (n : T) : Prop := True.

Section minimize_lemmas.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Lemma query_assoc_Mprod
  : forall {T U V W : Type} (qb : M T) (qb' : M U) (qb'' : M V) qg (qr : _ -> W),
      Meq (query (Mprod (Mprod qb qb') qb'') qg qr)
          (query (Mprod qb (Mprod qb' qb''))
                 (fun xyz => qg (fst xyz, fst (snd xyz), snd (snd xyz)))
                 (fun xyz => qr (fst xyz, fst (snd xyz), snd (snd xyz)))).
  Proof.
    intros; unfold query, Mprod; rw_M. reflexivity.
  Qed.

  Lemma query_assoc_Mprod'
  : forall {T U V W : Type} (qb : M T) (qb' : M U) (qb'' : M V) qg (qr : _ -> W),
      Meq (query (Mprod qb (Mprod qb' qb'')) qg qr)
          (query (Mprod (Mprod qb qb') qb'')
                 (fun xyz => qg (fst (fst xyz), (snd (fst xyz), snd xyz)))
                 (fun xyz => qr (fst (fst xyz), (snd (fst xyz), snd xyz)))).
  Proof.
    intros; unfold query, Mprod; rw_M. reflexivity.
  Qed.

  Lemma minimize_drop
  : forall {T T' V : Type} (qb : M T) (qb' : M T') qg (qr : _ -> V) f (qb'' : M T') qg'',
      forall Hignore : Find f,
      Meq (query (Mprod qb qb') qg qr)
          (query qb' (fun y => qg (f y,y)) (fun y => qr (f y,y))) ->
      Meq (query qb' (fun y => qg (f y,y)) (fun y => qr (f y,y)))
          (query qb'' (fun y => qg'' (f y,y)) (fun y => qr (f y,y))) ->
      Meq (query (Mprod qb qb') qg qr)
          (query (Mmap (fun x => (f x, x)) qb'') qg'' qr).
  Proof.
    unfold query, Mprod. intros.
    rewrite <- H in H0; clear H.
    rewrite H0; clear H0.
    unfold Mmap. rw_M.
    reflexivity.
  Qed.

  Lemma minimize_keep
  : forall {T T' V : Type} (qb : M T) (qb' : M T') qg (qr : _ -> V) (qb'' : M T') qg'',
      (forall x,
          Meq (query qb' (fun y => qg (x,y)) (fun y => qr (x,y)))
              (query qb'' (fun y => qg'' (x,y)) (fun y => qr (x,y)))) ->
      Meq (query (Mprod qb qb') qg qr)
          (query (Mprod qb qb'') qg'' qr).
  Proof.
    unfold query. intros.
    rw_M. eapply Proper_Mbind_eq; try reflexivity. eauto.
  Qed.

  Lemma minimize_const
  : forall {T T' V : Type} (qb' : M T') qg (qr : _ -> V) (qb'' : M T') qg'' (v : T),
      Meq (query qb' (fun y => qg (v,y)) (fun y => qr (v,y)))
          (query qb'' (fun y => qg'' (v,y)) (fun y => qr (v,y))) ->
      Meq (query (Mprod (Mret v) qb') qg qr)
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

  Lemma minimize_drop_under
  : forall M (DM : DataModel M) {T T' V : Type} (qb : M T) (qb' : M T') qg (qr : _ -> V) (qb'' : M T') qg'' f P,
      forall Hignore : Find f,
      (P -> Meq (query (Mprod qb qb') qg qr)
                (query qb' (fun y => qg (f y,y)) (fun y => qr (f y,y)))) ->
      (P -> Meq (query qb' (fun y => qg (f y,y)) (fun y => qr (f y,y)))
                (query qb'' (fun y => qg'' (f y,y)) (fun y => qr (f y,y)))) ->
      (P -> Meq (query (Mprod qb qb') qg qr)
                (query (Mmap (fun x => (f x, x)) qb'') qg'' qr)).
  Proof.
    unfold query, Mprod. intros.
    setoid_rewrite <- H in H0; clear H. 2: assumption.
    rewrite H0; clear H0.
    unfold Mmap. rw_M.
    reflexivity. assumption.
  Qed.

  Lemma minimize_keep_under
  : forall (T T' V : Type) (qb : M T) (qb' : M T') (qg : T * T' -> bool)
           (qr : T * T' -> V) (qb'' : M T') (qg'' : T * T' -> bool) P,
      (forall x : T,
          P -> Meq (query qb' (fun y : T' => qg (x, y)) (fun y : T' => qr (x, y)))
                   (query qb'' (fun y : T' => qg'' (x, y)) (fun y : T' => qr (x, y)))) ->
      (P -> Meq (query (Mprod qb qb') qg qr) (query (Mprod qb qb'') qg'' qr)).
  Proof.
    intros. eapply minimize_keep; eauto.
  Qed.

  Lemma chase_rhs : forall {T} (m1 m2 m3 : M T) P,
      (P -> Meq m3 m2) ->
      (P -> Meq m1 m3) ->
      (P -> Meq m1 m2).
  Proof. intros. etransitivity; eauto. Qed.

  Lemma find_id : forall T, @Find (T -> T) (fun x => x).
  Proof. constructor. Defined.
  Lemma find_left : forall T U V f,
      @Find (T -> V) f ->
      @Find (T * U -> V) (fun x => f (fst x)).
  Proof. constructor. Defined.
  Lemma find_right : forall T U V f,
      @Find (U -> V) f ->
      @Find (T * U -> V) (fun x => f (snd x)).
  Proof. constructor. Defined.


End minimize_lemmas.

Ltac drop_dup solver :=
  let rec search :=
    lazymatch goal with
    | |- @Find (?T -> ?T) _ => eapply find_id
    | |- _ =>
      (eapply find_left + eapply find_right) ; search
    end
  in
  lazymatch goal with
  | |- Meq ?x ?m =>
    first [ is_evar x ; symmetry
          | is_evar m ] ;
    repeat first [ simple eapply minimize_const
                 | once (eapply minimize_drop ;
                         [ search
                         | solve [ prove_query_homomorphic_equivalent solver ]
                         | ])
                 | simple eapply minimize_keep ; intro
                 ] ;
    simple eapply minimize_last
  | |- _ -> Meq ?x ?m =>
    first [ is_evar x ; let h := fresh in intro h ; symmetry ; revert h
          | is_evar m ] ;
    (repeat first [ simple eapply minimize_const
                  | once (refine (@minimize_drop_under _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ;
                          [ shelve
                          | shelve
                          | shelve
                          | search
                          | solve [ eapply chase_rhs ;
                                    [ once solve [ chase solver ]
                                    | intro ; prove_query_homomorphic_equivalent solver ] ]
                          | ])
                  | simple eapply minimize_keep_under ; intro
                  ]) ;
    intro ; simple eapply minimize_last
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
      (repeat rewrite query_assoc_Mprod) ;
      drop_dup solver
  in
  lazymatch goal with
  | |- _ -> Meq _ _ => eapply refine_transitive_under
  | |- Meq _ _ => eapply refine_transitive
  end ;
  [ (once kont) ;
    once (simpl; intros ;
          repeat (rewrite rel_dec_eq_true by eauto with typeclass_instances) ;
          solve [ solve_conclusion ])
  | simpl ; reflexivity ].

Ltac simplifier :=
  lazymatch goal with
  | |- _ -> Meq _ _ =>
    intro
  | |- Meq _ _ => idtac
  end ; rw_M ; simpl ; reflexivity.

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


Ltac execute0 tac :=
  prep ; tac.
Ltac execute1 tac arg :=
  prep ; tac arg.
Ltac execute2 tac arg1 arg2 :=
  prep ; tac arg1 arg2.
