Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Bool.Bool.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.DataModel.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.Tables.
Require Import SemanticQuery.RecordTableaux.
Require Import SemanticQuery.HomomorphismSearch.

Set Implicit Arguments.
Set Strict Implicit.

Section with_scheme.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.
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
                   | MZ _ _ => fun pf => inl (MZ _ _)
                   | MN ls m' => fun pf =>
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
    match member_app_case _ _ m with
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
                ; filter := filter_weaken_app _ q.(tabl).(filter) ++
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
        Meq (bindD (scheme:=scheme) (hlist_app a b) db)
            (Mmap (fun xy => @hlist_app _ _ _ _ (fst xy) (snd xy))
                  (Mprod (bindD a db) (bindD b db))).
  Proof.
    induction a; simpl.
    { intros. unfold Mprod.
      rw_M. reflexivity. }
    { intros. rewrite IHa; clear IHa.
      rw_M. reflexivity. }
  Qed.

  Lemma filterD_app
    : forall ts a b,
      (eq ==> eq)%signature
                 (filterD (ts:=ts) (a ++ b))
                 (fun x => filterD a x && filterD b x).
  Proof.
    red. intros. subst.
    induction a; simpl; intros; auto.
    rewrite IHa.
    destruct (exprD a y); reflexivity.
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
    { rewrite IHa1. rewrite IHa2. reflexivity. }
    { reflexivity. }
  Qed.

  Lemma filterD_weaken_app : forall {X Y} f,
      (eq ==> eq)%signature
                 (filterD (@filter_weaken_app X Y f))
                 (fun x => filterD f (fst (hlist_split _ _ x))).
  Proof.
    red.
    intros; subst.
    induction f; simpl; auto.
    rewrite IHf.
    erewrite expr_weaken_app; reflexivity.
  Qed.

  (** TODO: duplicated! **)
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
        destruct (member_app_case ls ls' x); reflexivity. } }
  Qed.

  Lemma member_app_case_member_weaken_app
    : forall {T} (t : T) ls ls' (m : member t ls),
      member_app_case ls ls' (member_weaken_app ls' m) = inl m.
  Proof. clear.
         induction m; simpl; auto.
         rewrite IHm. reflexivity.
  Qed.

  Lemma member_app_case_member_lift
    : forall {T} (t : T) ls ls' (m : member t ls'),
      member_app_case ls ls' (member_lift ls m) = inr m.
  Proof. clear.
         induction ls; simpl; intros; auto.
         rewrite IHls. reflexivity.
  Qed.

  Lemma member_app_case_member_map_app
    : forall {T} (t : T) xs xs' ys ys'
             (f : forall t, member t xs -> member t xs')
             (g : forall t, member t ys -> member t ys')
             (m : member t (xs ++ ys)),
      member_app_case _ _ (member_map_app f g m) =
      match member_app_case _ _ m with
      | inl m => inl (f _ m)
      | inr m => inr (g _ m)
      end.
  Proof.
    unfold member_map_app.
    intros.
    destruct (member_app_case _ _ m).
    { rewrite member_app_case_member_weaken_app. reflexivity. }
    { rewrite member_app_case_member_lift. reflexivity. }
  Qed.

  Theorem chase_step_sound
  : forall (t : list type)
           (q : query scheme t)
           (c : embedded_dependency scheme)
           (h : tableaux_homomorphism (ed_front c) q.(tabl))
           (db : DB M scheme),
      embedded_dependencyD c db ->
      Meq (queryD q db) (queryD (@chase_step t q c h) db).
  Proof.
    intros.
    destruct c.
    assert (@DataModel.embedded_dependency _ DM _ _
                                               (bindD front_binds db) (filterD front_filter)
              (bindD back_binds db)
              (fun x y => filterD back_filter (hlist_app x y))).
    { clear - H. red in H; simpl in *.
      unfold ed_front, ed_back, tableauxD in H. simpl in H.
      red. unfold DataModel.query.
      etransitivity; [ eassumption | ].
      rewrite bindD_app. rw_M.
      repeat (eapply Proper_Mbind_eq; [ reflexivity | red; intros ]).
      simpl.
      rewrite hlist_split_hlist_app. simpl.
      erewrite filterD_app by reflexivity.
      eapply Proper_Mguard_eq; try reflexivity.
      f_equal.
      erewrite <- related_filterD_subst_test.
      reflexivity.
      red.
      clear.
      induction m.
      { simpl. rewrite (hlist_eta a). reflexivity. }
      { simpl. rewrite IHm.
        f_equal.
        rewrite (hlist_eta a). reflexivity. } }
    clear H.
    unfold ed_front in h. simpl in h.
    destruct h; simpl in *.
    unfold queryD, tableauxD, Mmap. rw_M.
    etransitivity.
    { eapply chaseable. eassumption.
      instantiate (1:= follow_types_homomorphism vars_mor).
      eapply bindD_subset; eauto.
      intros.
      red in filterOk.
      eapply filterOk in H.
      rewrite <- H.
      eapply related_filterD_subst_test.
      eapply related_follow_types_homomorphism. }
    { simpl. unfold DataModel.query.
      rewrite bindD_app.
      rw_M.
      repeat (eapply Proper_Mbind_eq; [ reflexivity | red; intros ]).
      simpl.
      eapply Proper_Mguard.
      { erewrite filterD_app; try reflexivity.
        erewrite filterD_weaken_app; [ | reflexivity ].
        rewrite hlist_split_hlist_app. simpl.
        f_equal.
        unfold filter_subst.
        eapply related_filterD_subst_test.
        clear. induction front_types.
        { simpl in *.
          unfold member_map_app. simpl.
          red. clear. induction a.
          { simpl. auto. }
          { simpl. eauto. } }
        { red.
          specialize (IHfront_types (types_homomorphism_rest vars_mor)).
          red in IHfront_types.
          simpl.
          intros.
          destruct (member_case m).
          { destruct H. subst. simpl.
            unfold member_map_app. simpl.
            rewrite hlist_get_member_weaken_app.
            rewrite hlist_split_hlist_app. reflexivity. }
          { destruct H. subst. simpl.
            rewrite IHfront_types.
            unfold member_map_app. simpl.
            destruct (member_app_case front_types back_types x); auto. } } }
      { eapply Proper_Mret_eq.
        induction (ret q); simpl; auto.
        { f_equal.
          { erewrite expr_weaken_app by reflexivity.
            rewrite hlist_split_hlist_app. reflexivity. }
          { eauto. } } } }
  Qed.

  Variable check_entailment
  : forall (ts : list type) (ps : filter_type ts) (g : guard_type ts),
      option (forall vs : Env ts, filterD ps vs = true -> exprD g vs = true).

  Definition query_equiv {t} (q1 q2 : query scheme t) : bool :=
    match find_query_homomorphisms check_entailment q1 q2 with
    | nil => false
    | _ :: _ =>
      match find_query_homomorphisms check_entailment q2 q1 with
      | nil => false
      | _ :: _ => true
      end
    end.

  Fixpoint chaseK (eds : list (embedded_dependency scheme))
             {t} (q : query scheme t)
             {T} (k : query scheme t -> T)
             (done : query scheme t -> T) {struct eds}
  : T :=
    match eds with
    | nil => done q
    | ed :: eds =>
      let front := ed_front ed in
      let hs := find_homomorphisms check_entailment front q.(tabl) in
      (fix try_each hs : T :=
         match hs with
         | nil => @chaseK eds _ q _ k done
         | h :: hs =>
           let result := chase_step q h in
           if query_equiv q result then
             try_each hs
           else
             k result
         end) hs
    end.

  Inductive Status (T : Type) : Type :=
  | Complete : T -> Status T
  | Incomplete : T -> Status T.

  Fixpoint get_status {T} (s : Status T) : T :=
    match s with
    | Complete s => s
    | Incomplete s => s
    end.

  (** NOTE: It would be nice to use co-induction here *)
  Fixpoint chase (fuel : nat) (eds : list (embedded_dependency scheme))
             {t} (q : query scheme t) {struct fuel}
  : Status (query scheme t) :=
    match fuel with
    | 0 => Incomplete q
    | S fuel =>
      chaseK eds q (fun q => chase fuel eds q) (@Complete _)
    end.

(*
  Instance Reflexive_list_set_equiv {T} : Reflexive (@list_set_equiv T).
  Proof. split; reflexivity. Qed.

  Instance Transitive_list_set_equiv {T} : Transitive (@list_set_equiv T).
  Proof.
    red. destruct 1. destruct 1.
    split; etransitivity; eauto.
  Qed.
*)

  Lemma chaseK_sound
  : forall (t : list type)
           (T : Type) (P : T -> Prop)
           (k d : query scheme t -> T)
           (q : query scheme t)
           (eds : list (embedded_dependency scheme))
           (R : query scheme t -> query scheme t -> Prop),
      Transitive R ->
      Reflexive R ->
      (forall a ed th, In ed eds -> R a (chase_step a (c:=ed) th)) ->
      (forall q', R q q' -> P (k q')) ->
      (forall q', R q q' -> P (d q')) ->
      P (chaseK eds q k d).
  Proof.
    intros. induction eds; simpl.
    { eapply H3. eauto. }
    { induction (find_homomorphisms check_entailment (ed_front a) (tabl q)).
      { eapply IHeds. clear - H1.
        intros. eapply H1. right. auto. }
      { destruct (query_equiv q (chase_step q a0)); eauto.
        eapply H2.
        eapply H1. left. reflexivity. } }
  Qed.

  Theorem chase_sound
  : forall (t : list type)
           (eds : list (embedded_dependency scheme))
           (db : DB M scheme),
      Forall (fun c => embedded_dependencyD c db) eds ->
      forall fuel (q : query scheme t),
        Meq (queryD q db)
            (queryD (get_status (@chase fuel eds _ q)) db).
  Proof.
    induction fuel; simpl.
    { reflexivity. }
    { intros.
      eapply chaseK_sound
        with (R := fun q1 q2 => Meq (queryD q1 db) (queryD q2 db)).
      { red. etransitivity; eauto. }
      { red. reflexivity. }
      { intros. eapply chase_step_sound.
        eapply Forall_forall in H0; eauto. eauto. }
      { intros. etransitivity. eapply H0. eauto. }
      { intros. eauto. } }
  Qed.

End with_scheme.
