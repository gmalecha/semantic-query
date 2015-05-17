Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.Tables.
Require Import SemanticQuery.RecordTableaux.

Section with_scheme.
  Variable scheme : list type.

  (** TODO: these should move **)
  Definition filter_lift vs vs'
  : filter_type vs' -> filter_type (vs ++ vs') :=
    List.map (@expr_lift _ vs vs').

  Definition filter_weaken_app vs vs'
  : filter_type vs' -> filter_type (vs' ++ vs) :=
    List.map (@expr_weaken_app _ vs vs').

  Definition filter_subst {vs vs'} (f : expr vs Bool -> expr vs' Bool)
  : filter_type vs -> filter_type vs' :=
    List.map f.

  Fixpoint member_app_case {T: Type} (t : T) xs xs'
    : member t (xs ++ xs') -> member t xs + member t xs' :=
    match xs as xs
          return member t (xs ++ xs') -> member t xs + member t xs'
    with
    | nil => fun m => inr m
    | x :: xs => fun (m : member t ((x :: xs) ++ xs')) =>
                   match m in member _ X
                         return X = x :: xs ++ xs' ->
                                match X return Type with
                                | nil => Empty_set
                                | _x :: _xs =>
                                  member t (_x :: xs) + member t xs'
                                end
                   with
                   | MZ _ => fun pf => inl (MZ _ _)
                   | MN _ ls m' => fun pf =>
                     let m' := match pf in _ = X
                                     return match X return Type with
                                            | nil => Empty_set
                                            | _ :: xs => member t xs
                                            end
                               with
                               | eq_refl => m'
                               end
                     in
                     match @member_app_case T t xs xs' m' with
                     | inl x => inl (MN _ x)
                     | inr x => inr x
                     end
                   end eq_refl
    end%type.

  Definition member_map_app {T: Type} {xs xs' ys ys'}
           (mx : forall t, member t xs -> member t ys)
           (mx' : forall t, member t xs' -> member t ys')
           (t : T) (m : member t (xs ++ xs'))
    : member t (ys ++ ys') :=
    match member_app_case _ _ _ m with
    | inl m => member_weaken_app _ (mx _ m)
    | inr m => member_lift _ (mx' _ m)
    end.

  Definition chase_step {t}
             (q : query scheme t)
             (c : embedded_dependency scheme)
             (h : tableaux_homomorphism (ed_front c)
                                        q.(tabl))
  : query scheme t :=
    let map_expr :=
        expr_subst (member_map_app h.(vars_mor) (fun _ x => x))
    in
    {| tabl := {| types := q.(tabl).(types) ++ c.(back_types)
                ; binds := hlist_app q.(tabl).(binds)
                                     c.(back_binds)
                ; filter := filter_weaken_app _ _ q.(tabl).(filter) ++
                            filter_subst map_expr c.(back_filter)
                |}
     ; ret := hlist_map (fun t e => expr_weaken_app _ e) q.(ret)
     |}.

  Lemma cross_app : forall {A B C} (ab : A -> B -> C) b c a,
      cross ab (a ++ b) c = cross ab a c ++ cross ab b c.
  Proof.
    induction a; simpl; auto.
    rewrite IHa. rewrite app_assoc. reflexivity.
  Qed.

  Lemma map_cross
    : forall {A B C D E F} (ab : A -> B -> D)
             (dc : D -> C -> E)
             (bc : B -> C -> F)
             (af : A -> F -> E),
      (forall a b c, dc (ab a b) c = af a (bc b c)) ->
      forall (a : A) (c : list C) (b : list B),
        cross dc (map (ab a) b) c = map (af a) (cross bc b c).
  Proof.
    induction b; simpl; intros; auto.
    { rewrite IHb.
      repeat rewrite map_app.
      rewrite map_map. f_equal.
      eapply map_ext. eauto. }
  Qed.

  Lemma cross_assoc
    : forall {A B C D E F} (ab : A -> B -> D)
             (dc : D -> C -> E)
             (bc : B -> C -> F)
             (af : A -> F -> E),
      (forall a b c, dc (ab a b) c = af a (bc b c)) ->
      forall (a : list A) (b : list B) (c : list C),
        cross dc (cross ab a b) c =
        cross af a (cross bc b c).
  Proof.
    induction a; simpl; intros; auto.
    rewrite cross_app. rewrite IHa.
    f_equal.
    eapply map_cross; eauto.
  Qed.

  Lemma bindD_app
    : forall B (b : hlist _ B) A (a : hlist _ A),
      forall db,
        bindD (scheme:=scheme) (hlist_app a b) db =
        cross (@hlist_app _ _ _ _) (bindD a db) (bindD b db).
  Proof.
    induction a; simpl.
    { intros. rewrite app_nil_r.
      rewrite map_id. reflexivity. }
    { intros. rewrite IHa.
      erewrite cross_assoc; reflexivity. }
  Qed.


  Lemma filterD_app
    : forall ts a b,
      (eq ==> eq)%signature (filterD (ts:=ts) (a ++ b)) (fun x => filterD a x && filterD b x).
  Proof.
    red. intros. subst.
    induction a; simpl; intros; auto.
    rewrite IHa.
    destruct (exprD a y); reflexivity.
  Qed.

  Instance Proper_map {T U : Type} :
    Proper ((eq ==> eq) ==> eq ==> eq) (@map T U).
  Proof.
    repeat red. intros.
    subst. eapply map_ext. eauto.
  Qed.

  Instance Proper_filter {T : Type} :
    Proper ((eq ==> eq) ==> eq ==> eq) (@List.filter T).
  Proof.
    repeat red. intros.
    subst. induction y0; simpl; auto.
    rewrite IHy0. erewrite H; reflexivity.
  Qed.

  Lemma list_set_subset_nil : forall {T} (c : list T),
      list_set_subset nil c <-> True.
  Proof.
    unfold list_set_subset; split; auto.
    inversion 2.
  Qed.

  Lemma list_set_subset_cons : forall {T} a b (c : list T),
      list_set_subset (a :: b) c <-> In a c /\ list_set_subset b c.
  Proof.
    unfold list_set_subset. simpl; intros.
    split.
    { intros. split; intros; apply H; eauto. }
    { intros. destruct H0. subst. tauto. firstorder. }
  Qed.

  Lemma list_set_subset_app : forall {T} (b c a : list T),
      list_set_subset (a ++ b) c <->
      list_set_subset a c /\ list_set_subset b c.
  Proof.
    induction a; simpl; intros.
    { rewrite list_set_subset_nil.
      tauto. }
    { repeat rewrite list_set_subset_cons. rewrite IHa.
      tauto. }
  Qed.

  Instance Transitive_list_set_subst {T}
    : Transitive (@list_set_subset T).
  Proof.
    red. unfold list_set_subset. firstorder.
  Qed.

  Instance Reflexive_list_set_subst {T}
    : Reflexive (@list_set_subset T).
  Proof.
    red. unfold list_set_subset. firstorder.
  Qed.

  Instance Proper_cross {T U V : Type} :
    Proper ((eq ==> eq ==> eq) ==> list_set_subset ==> list_set_subset ==> list_set_subset)
           (@cross T U V).
  Proof.
    do 4 red. intros.
    revert H0. revert y0. revert x0.
    induction x0; simpl.
    { unfold list_set_subset. simpl. tauto. }
    { intros.
      rewrite list_set_subset_cons in H0.
      rewrite list_set_subset_app.
      split.
      { red.
        setoid_rewrite in_map_iff.
        intros.
        destruct H2 as [ ? [ ? ? ] ].
        subst.
        eapply In_cross.
        destruct H0.
        do 2 eexists; split; eauto.
        split; eauto. eapply H; reflexivity. }
      { eapply IHx0. tauto. } }
  Qed.

  Lemma filter_and : forall {T} (f g : T -> bool) ls,
      List.filter (fun x => f x && g x) ls =
      List.filter f (List.filter g ls).
  Proof.
    induction ls; simpl; auto.
    rewrite IHls; clear IHls.
    destruct (g a); simpl.
    { rewrite andb_true_r. reflexivity. }
    { rewrite andb_false_r. reflexivity. }
  Qed.

  Lemma hlist_get_member_weaken_app
    : forall {T} F (X Y : list T) t (m : member t Y) y,
      hlist_get (F:=F) (member_weaken_app X m) y =
      hlist_get m (fst (hlist_split _ _ y)).
  Proof.
    induction m; simpl; intros.
    { match goal with
      | |- context [ match ?X with _ => _ end ] =>
        destruct X
      end; reflexivity. }
    { rewrite IHm.
      match goal with
      | |- hlist_get _ (fst ?Y) = hlist_get _ (hlist_tl (fst match ?X with _ => _ end)) =>
        change Y with X ; destruct X
      end. reflexivity. }
  Qed.

  Lemma expr_weaken_app : forall T X Y (a : expr Y T),
      (eq ==> eq)%signature
                 (exprD (expr_weaken_app X a))
                 (fun x => exprD a (fst (hlist_split _ _ x))).
  Proof.
    red. intros; subst.
    induction a; simpl; intros.
    { simpl.
      eapply hlist_get_member_weaken_app. }
    { rewrite IHa. reflexivity. }
    { rewrite IHa1. rewrite IHa2. reflexivity. }
  Qed.

  Lemma filterD_weaken_app : forall {X Y} f,
      (eq ==> eq)%signature
                 (filterD (filter_weaken_app X Y f))
                 (fun x => filterD f (fst (hlist_split _ _ x))).
  Proof.
    red.
    intros; subst.
    induction f; simpl; auto.
    rewrite IHf.
    erewrite expr_weaken_app; reflexivity.
  Qed.

  Lemma filter_perm : forall {T} (f g : T -> bool) ls,
      List.filter f (List.filter g ls) = List.filter g (List.filter f ls).
  Proof.
    induction ls; simpl; intros; eauto.
    destruct (g a) eqn:Hga; destruct (f a) eqn:Hfa; simpl;
    try rewrite Hga; try rewrite Hfa; rewrite IHls; reflexivity.
  Qed.

  Lemma filter_app : forall {T} (f : T -> bool) ls' ls,
      List.filter f (ls ++ ls') = List.filter f ls ++ List.filter f ls'.
  Proof.
    induction ls; simpl; intros; eauto.
    destruct (f a); rewrite IHls; reflexivity.
  Qed.

  Lemma filter_cross_distr
    : forall {T U V} (join : T -> U -> V) f f' g',
      (forall a b, f (join a b) = f' a && g' b) ->
      forall a b,
        List.filter f (cross join a b) =
        cross join (List.filter f' a) (List.filter g' b).
  Proof.
    induction a; simpl; intros; auto.
    rewrite filter_app.
    rewrite IHa; clear IHa.
    destruct (f' a) eqn:Hf'a.
    { simpl. f_equal.
      induction b; simpl; auto.
      rewrite H. rewrite Hf'a. simpl.
      rewrite IHb.
      destruct (g' a1) eqn:Hg'a1; simpl.
      { reflexivity. }
      { auto. } }
    { rewrite <- app_nil_l.
      f_equal.
      induction b; simpl; auto.
      rewrite H. rewrite Hf'a. simpl. auto. }
  Qed.
  Arguments filter_cross_distr {T U V} join f f' g' _ a b.

  Lemma filter_true : forall {T} (f : T -> bool),
      (forall x, f x = true) ->
      forall ls, List.filter f ls = ls.
  Proof.
    induction ls; simpl; intros; auto.
    rewrite IHls. rewrite H. reflexivity.
  Qed.

  Lemma filter_cross_distr_1
    : forall {T U V} (join : T -> U -> V) f f',
      (forall a b, f (join a b) = f' a) ->
      forall a b,
        List.filter f (cross join a b) =
        cross join (List.filter f' a) b.
  Proof.
    intros.
    rewrite (filter_cross_distr join f f' (fun _ => true)).
    { rewrite (filter_true (fun _ => true)) by reflexivity.
      auto. }
    { intros. rewrite H. rewrite andb_true_r. auto. }
  Qed.

  Lemma filter_cross_distr_2
    : forall {T U V} (join : T -> U -> V) f g',
      (forall a b, f (join a b) = g' b) ->
      forall a b,
        List.filter f (cross join a b) =
        cross join a (List.filter g' b).
  Proof.
    intros.
    rewrite (filter_cross_distr join f (fun _ => true) g').
    { rewrite (filter_true (fun _ => true)) by reflexivity.
      auto. }
    { intros. rewrite H. auto. }
  Qed.

  (** TODO: Move **)
  Definition types_homomorphism_rest {a b c} (x : types_homomorphism (a :: b) c)
    : types_homomorphism b c :=
    fun t m => x t (MN _ m).

  Definition binds_homomorphism_rest {a b c d e f}
             (bh : @binds_homomorphism scheme (a :: b) c d e f)
    : @binds_homomorphism scheme b c (types_homomorphism_rest d) (hlist_tl e) f :=
    fun t m => bh t (MN _ m).

  Definition filter_homomorphism_rest {a b c d e f}
             (bh : @filter_homomorphism a b c (d :: e) f)
    : @filter_homomorphism a b c e f :=
    fun x pf =>
      match exprD (expr_subst c d) x as X
            return (if X then _ else false) = true ->
                   _ = true
      with
      | true => fun pf => pf
      | false => fun pf => match pf in _ = X
                                 return match X with
                                        | true => _
                                        | false => True
                                        end
                           with
                           | eq_refl => I
                           end
      end (bh _ pf).

  Fixpoint follow_types_homomorphism {vs vs'} {struct vs}
    : forall (vm : types_homomorphism vs vs'),
      Env vs' -> Env vs :=
    match vs as vs
          return forall {vm : types_homomorphism vs vs'},
        Env vs' -> Env vs
    with
    | nil => fun _ _ => Hnil
    | l :: ls => fun vm g =>
                   Hcons (hlist_get (vm _ (MZ _ _)) g)
                         (follow_types_homomorphism (types_homomorphism_rest vm) g)
    end.

  Lemma In_follow_types_homomorphism
    : forall vs vs' (vm : types_homomorphism vs vs') to from
             (bh : binds_homomorphism (scheme:=scheme) vm to from),
      forall db,
      forall x, In x (bindD from db) ->
                In (follow_types_homomorphism vm x) (bindD to db).
  Proof.
    induction to; simpl.
    { auto. }
    { intros.
      eapply In_cross.
      generalize (bh _ (MZ _ _)). simpl; intros; subst.
      do 2 eexists; split; [ | split ]; eauto using In_bindD_hlist_get.
      eapply (IHto _ _ (binds_homomorphism_rest bh) db _ H). }
  Qed.

  Lemma related_follow_types_homomorphism
    : forall a b (vm : types_homomorphism a b),
      forall x,
        related vm (follow_types_homomorphism vm x) x.
  Proof.
    induction a; simpl.
    { red. inversion m. }
    { red. intros.
      destruct (member_case m).
      { destruct H. subst. reflexivity. }
      { destruct H; subst.
        simpl. red in IHa.
        rewrite IHa.
        reflexivity. } }
  Qed.

  Lemma hlist_map_compose {T} (A B C:T->Type)
        (f : forall x, A x -> B x)
        (g : forall x, B x -> C x) ls (hs : hlist A ls)  :
    hlist_map g (hlist_map f hs) = hlist_map (fun t x => g t (f t x)) hs.
  Proof.
    induction hs; simpl; auto.
    rewrite IHhs. reflexivity.
  Qed.

  Lemma hlist_map_ext {T} (A B:T->Type)
        (f g : forall x, A x -> B x) :
    (forall a b, f a b = g a b) ->
    forall ls (hs : hlist A ls),
      hlist_map f hs = hlist_map g hs.
  Proof.
    induction hs; simpl; intros; auto.
    f_equal; auto.
  Qed.

  Lemma filterD_is_forallb : forall vars f env,
      filterD f env = forallb (fun e : expr vars Bool => exprD e env) f.
  Proof.
    intros.
    induction f; simpl; auto.
    rewrite IHf.
    destruct (exprD a env); auto.
  Qed.

  Lemma forallb_map : forall {T U} (P : U -> bool) (F : T -> U) ls,
      forallb P (map F ls) = forallb (fun x => P (F x)) ls.
  Proof.
    induction ls; simpl; eauto.
    rewrite IHls. reflexivity.
  Qed.

  Instance Proper_forallb {T}
    : Proper ((eq ==> eq) ==> eq ==> eq) (@forallb T).
  Proof.
    red. red. red. intros; subst.
    induction y0; simpl; auto.
    rewrite IHy0. erewrite H; reflexivity.
  Qed.

  Lemma hlist_get_hlist_app {T} {F:T->Type} ls ls' t
        (m : member t (ls ++ ls')) (hs : hlist F ls) (hs' : hlist F ls') :
    hlist_get m (hlist_app hs hs') =
    match @member_app_case T t ls ls' m with
    | inl m => hlist_get m hs
    | inr m => hlist_get m hs'
    end.
  Proof.
    induction ls; simpl.
    { rewrite (hlist_eta hs). reflexivity. }
    { destruct (member_case m).
      { destruct H. subst. simpl.
        rewrite (hlist_eta hs). reflexivity. }
      { destruct H; subst.
        rewrite (hlist_eta hs). simpl.
        rewrite IHls.
        destruct (member_app_case t ls ls' x); reflexivity. } }
  Qed.

  Lemma member_app_case_member_weaken_app
    : forall {T} (t : T) ls ls' (m : member t ls),
      member_app_case t ls ls' (member_weaken_app ls' m) = inl m.
  Proof. clear.
         induction m; simpl; auto.
         rewrite IHm. reflexivity.
  Qed.

  Lemma member_app_case_member_lift
    : forall {T} (t : T) ls ls' (m : member t ls'),
      member_app_case t ls ls' (member_lift ls m) = inr m.
  Proof. clear.
         induction ls; simpl; intros; auto.
         rewrite IHls. reflexivity.
  Qed.

  Lemma member_app_case_member_map_app
    : forall {T} (t : T) xs xs' ys ys'
             (f : forall t, member t xs -> member t xs')
             (g : forall t, member t ys -> member t ys')
             (m : member t (xs ++ ys)),
      member_app_case t _ _ (member_map_app f g t m) =
      match member_app_case t _ _ m with
      | inl m => inl (f _ m)
      | inr m => inr (g _ m)
      end.
  Proof.
    unfold member_map_app.
    intros.
    destruct (member_app_case t _ _ m).
    { rewrite member_app_case_member_weaken_app. reflexivity. }
    { rewrite member_app_case_member_lift. reflexivity. }
  Qed.

  Theorem chase_step_sound
  : forall (t : list type)
           (q : query scheme t)
           (c : embedded_dependency scheme)
           (h : tableaux_homomorphism (ed_front c) q.(tabl))
           (db : DB scheme),
      embedded_dependencyD c db ->
      list_set_equiv (queryD q db) (queryD (@chase_step t q c h) db).
  Proof.
    destruct q; destruct c.
    unfold ed_front. simpl. unfold chase_step. simpl.
    unfold embedded_dependencyD, queryD, tableauxD; simpl.
    intros.
    rewrite bindD_app.
    rewrite filterD_app.
    rewrite filter_and.
    rewrite filterD_weaken_app.
    rewrite filter_perm.
    rewrite filter_cross_distr_1
       with (f':=filterD tabl.(filter))
         by (intros; rewrite hlist_split_hlist_app; reflexivity).
    (** TODO: is it possible to use homomorphism_subset here? *)
    (** equational reasoning seems to no longer be possible? **)
    { split.
      { red. revert H.
        repeat first [ setoid_rewrite in_map_iff
                     | setoid_rewrite filter_In
                     | setoid_rewrite In_cross ].
        intros; forward_reason.
        destruct h. simpl in *.
        specialize (H (follow_types_homomorphism vars_mor x0)).
        destruct H.
        { split; eauto using In_follow_types_homomorphism.
          erewrite related_filterD_subst_test.
          2: instantiate (1:=x0). 2: instantiate (1:=vars_mor).
          eapply filterOk. assumption.
          eapply related_follow_types_homomorphism. }
        forward_reason.
        exists (hlist_app x0 x2). subst.
        split.
        { unfold retD. rewrite hlist_map_compose.
          eapply hlist_map_ext. intros.
          erewrite expr_weaken_app; [ | reflexivity ].
          rewrite hlist_split_hlist_app. reflexivity. }
        split.
        { do 2 eexists; split; split; eauto. }
        { red in filterOk.
          unfold filter_subst.
          rewrite filterD_is_forallb.
          rewrite forallb_map.
          rewrite filterD_is_forallb in H3.
          erewrite Proper_forallb; try eauto.
          red. clear. intros; subst.
          erewrite related_exprD_subst_expr; eauto.
          { (** this should be a lemma *)
            unfold related.
            intros. do 2 rewrite hlist_get_hlist_app.
            rewrite member_app_case_member_map_app.
            destruct (member_app_case t front_types back_types m); auto.
            eapply related_follow_types_homomorphism. } } }
      { red. revert H.
        repeat first [ setoid_rewrite in_map_iff
                     | setoid_rewrite filter_In
                     | setoid_rewrite In_cross ].
        intros; forward_reason.
        subst.
        destruct h; simpl in *.
        exists x1. split; auto.
        unfold retD.
        rewrite hlist_map_compose.
        eapply hlist_map_ext.
        intros. erewrite expr_weaken_app; [ | reflexivity ].
        rewrite hlist_split_hlist_app. reflexivity. } }
  Qed.

End with_scheme.