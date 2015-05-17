Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.Tables.

Set Implicit Arguments.
Set Strict Implicit.

Section with_tables.
  Variable scheme : list type. (** A bit odd **)

  Definition binds_type : list type -> Type :=
    hlist (fun x => member x scheme).

  Definition guard_type (vars : list type) : Type :=
    expr vars Bool.

  Definition filter_type (vars : list type) : Type :=
    list (guard_type vars).

  Definition ret_type (vars : list type) (result : list type) : Type :=
    hlist (expr vars) result.

  Record tableaux :=
  { types : list type
  ; binds : binds_type types
  ; filter : filter_type types
  }.

  Record query (t : list type) : Type :=
  { tabl : tableaux
  ; ret  : ret_type tabl.(types) t
  }.

  Fixpoint bindD {ts : list type} (names : binds_type ts)
  : DB scheme -> list (hlist typeD ts) :=
    match names in hlist _ ts return DB scheme -> list (hlist typeD ts) with
    | Hnil => fun _ => Hnil :: nil
    | Hcons _ _ n names => fun tbls =>
                             cross (fun a b => Hcons a b) (hlist_get n tbls) (bindD names tbls)
    end.

  Fixpoint filterD {ts : list type} (f : filter_type ts)
  : exprT ts bool :=
    match f with
    | nil => fun _ => true
    | f :: fs =>
      let fD := exprD f in
      let rD := filterD fs in
      fun rows => if fD rows then rD rows else false
    end.

  (** The return type here is a bit odd. I'm just gluing the rows together as an hlist.
   ** Queries seem more natural.
   **)
  Definition tableauxD (t : tableaux)
  : DB scheme -> list (hlist typeD t.(types)) :=
    let all := bindD t.(binds) in
    let keep := filterD t.(filter) in
    fun tbls => List.filter keep (all tbls).

  Section hlist_build2.
    Context {T V : Type} {U : T -> Type}.
    Context (f : forall t, V -> U t).

    Fixpoint hlist_build2 (ts : list T) (vs : list V) : option (hlist U ts) :=
      match ts , vs with
      | t :: ts , v :: vs =>
        match hlist_build2 ts vs with
        | None => None
        | Some hs => Some (Hcons (f t v) hs)
        end
      | nil , nil => Some Hnil
      | _ , _ => None
      end.
  End hlist_build2.

  Definition retD {ts ts'} (rt : ret_type ts ts')
  : exprT ts (Env ts') :=
    fun vars => hlist_map (fun t e => exprD e vars) rt.

  Definition queryD ts (q : query ts)
  : DB scheme -> list (hlist typeD ts) :=
    fun tbls => List.map (retD q.(ret)) (tableauxD q.(tabl) tbls).

  (** TODO: Move these **)
  Definition list_set_subset {T} (a b : list T) : Prop :=
    forall x, In x a -> In x b.

  Definition list_set_equiv {T} (a b : list T) : Prop :=
    list_set_subset a b /\ list_set_subset b a.


  (*
    A homomorphism h : t1 -> t2 maps the for-bound variables of t1 to the for-bound variables of t2 such that
    1) x in X in t1 implies h(x) in X in t2
    2) t1 |- p = q in t1 implies t2 |- h(p) = h(q)
    3) return E in t1 and return E' in t2 implies t2 |- h(E) = E'
   *)
  Definition types_homomorphism (ts1 ts2 : list type) : Type :=
    forall x : type, member x ts1 -> member x ts2.
  Definition binds_homomorphism {ts1 ts2 : list type}
             (h : types_homomorphism ts1 ts2)
             (b1 : hlist (fun x => member x scheme) ts1)
             (b2 : hlist (fun x => member x scheme) ts2) : Type :=
    forall t (x : member t _), hlist_get x b1 = hlist_get (h _ x) b2.
  Definition filter_homomorphism {ts1 ts2 : list type}
             (h : types_homomorphism ts1 ts2)
             (f1 : list (guard_type ts1))
             (f2 : list (guard_type ts2)) : Type :=
    forall x, filterD f2 x = true ->
              filterD (map (expr_subst h) f1) x = true.

  Record tableaux_homomorphism (t1 t2 : tableaux) : Type :=
  { vars_mor : types_homomorphism t1.(types) t2.(types)
  ; bindsOk  : binds_homomorphism vars_mor t1.(binds) t2.(binds) (** 1 **)
  ; filterOk : filter_homomorphism vars_mor t1.(filter) t2.(filter) (** 2 **)
  }.

  Record query_homomorphism ts (q1 q2 : query ts) : Type :=
  { th : tableaux_homomorphism q1.(tabl) q2.(tabl)
  ; retOk : forall r, filterD (map (expr_subst th.(vars_mor)) q1.(tabl).(filter)) r = true ->
              retD (hlist_map (fun T (x : expr q1.(tabl).(types) T) =>
                                 expr_subst th.(vars_mor) x) q1.(ret)) r =
              retD q2.(ret) r
  }.

  Definition related {T} {F} {ts1 ts2 : list T}
             (h : forall x : T, member x ts1 -> member x ts2)
             (b1 : hlist F ts1)
             (b2 : hlist F ts2) : Prop :=
    forall t (m : member t ts1),
      hlist_get m b1 = hlist_get (h _ m) b2.

  Lemma In_bindD_hlist_get
    : forall (l : type) (ts2 : list type) (tbl_data : DB scheme)
             (b2 : hlist (fun x : type => member x scheme) ts2)
             (x : Env ts2)
             (m : member l ts2),
      In x (bindD b2 tbl_data) ->
      In (hlist_get m x) (hlist_get (hlist_get m b2) tbl_data).
  Proof.
    induction b2.
    { simpl. intros. inversion m. }
    { simpl. intros.
      eapply In_cross in H. forward_reason.
      subst.
      destruct (member_case m); forward_reason.
      { subst. simpl. auto. }
      { subst. simpl. eauto. } }
  Qed.

  Lemma bindD_subset
    : forall ts1 (b1 : hlist (fun x => member x scheme) ts1)
             ts2 (b2 : hlist (fun x => member x scheme) ts2),
      forall tbl_data x,
        In x (bindD b2 tbl_data) ->
        forall (h : types_homomorphism ts1 ts2),
          binds_homomorphism h b1 b2 ->
          exists y,
            related h y x /\
            In y (bindD b1 tbl_data).
  Proof.
    induction b1.
    { intros. exists Hnil.
      simpl. split; eauto.
      red. clear. intros. inversion m. }
    { simpl. intros.
      setoid_rewrite In_cross.
      specialize (IHb1 _ _ _ _ H (fun t m => h t (MN _ m))).
      match goal with
      | H : ?X -> _ |- _ =>
        cut X;
          [ let H' := fresh in
            intro H' ; specialize (H H') | ]
      end.
      { forward_reason.
        exists (Hcons (hlist_get (h _ (MZ _ _)) x) x0).
        split.
        { red. intros.
          destruct (member_case m).
          { destruct H3. subst. simpl. reflexivity. }
          { forward_reason. subst. simpl. eauto. } }
        { do 2 eexists; split; eauto.
          red in X. red in H0.
          specialize (X l (MZ l ls)).
          simpl in X. subst.
          eauto using In_bindD_hlist_get. } }
      { revert X. clear. unfold binds_homomorphism.
        intros. eapply (X t (MN _ x)). } }
  Qed.

  (** TODO: Move **)
  Lemma related_exprD_subst_expr
  : forall (types0 types1 : list type)
           (vars_mor0 : types_homomorphism types1 types0)
           (x0 : Env types0) (x : Env types1),
      related vars_mor0 x x0 ->
      forall x1 (e : expr types1 x1),
        exprD (expr_subst vars_mor0 e) x0 = exprD e x.
  Proof.
    induction e.
    { simpl. red in H. symmetry. eapply H. }
    { simpl. rewrite IHe. reflexivity. }
    { simpl. rewrite IHe1. rewrite IHe2. reflexivity. }
  Qed.

  Lemma related_filterD_subst_test
    : forall (ts ts' : list type)
             (vars_mor0 : types_homomorphism ts' ts)
             (x0 : Env ts) (x : Env ts'),
      related vars_mor0 x x0 ->
      forall l : filter_type ts',
        filterD l x = filterD (map (expr_subst vars_mor0) l) x0.
  Proof.
    induction l; simpl; auto.
    { erewrite related_exprD_subst_expr by eauto.
      rewrite <- IHl.
      reflexivity. }
  Qed.

  Lemma retD_related
    : forall (types1 types0 : list type)
             (x0 : Env types1) (x : Env types0)
             (vars_mor0 : types_homomorphism types0 types1),
      related vars_mor0 x x0 ->
      forall (ts : list type)
             (ret0 : hlist (expr types0) ts),
        retD ret0 x =
        retD
          (hlist_map
             (fun T (x1 : expr types0 T) => expr_subst vars_mor0 x1)
             ret0) x0.
  Proof.
    induction ret0; simpl; auto.
    f_equal.
    { erewrite related_exprD_subst_expr; eauto. }
    { eassumption. }
  Qed.

  Lemma homomorphism_subset ts
    : forall q1 q2,
      @query_homomorphism ts q2 q1 ->
      forall tbls,
        list_set_subset (queryD q1 tbls) (queryD q2 tbls).
  Proof.
    unfold queryD, tableauxD.
    destruct 1. red.
    intros.
    eapply List.in_map_iff in H.
    eapply List.in_map_iff.
    forward_reason.
    eapply List.filter_In in H0.
    setoid_rewrite List.filter_In.
    forward_reason.
    eapply bindD_subset in H0.
    2: eapply bindsOk.
    revert H0; instantiate (4 := th0); intro H0.
    subst. forward_reason.
    destruct th0; simpl in *.
    exists x. split; [ | split ].
    { rewrite <- retOk0 by eauto.
      { destruct q2. simpl in *. clear - H.
        destruct q1. simpl in *. clear - H.
        destruct tabl0; destruct tabl1. simpl in *.
        eauto using retD_related. } }
    { assumption. }
    { red in filterOk0. clear retOk0 bindsOk0.
      eapply filterOk0 in H1.
      rewrite <- H1.
      destruct q2. simpl in *.
      eapply related_filterD_subst_test; eauto. }
  Qed.

  Theorem bihomomorphism_equal ts
    : forall q1 q2,
      @query_homomorphism ts q1 q2 ->
      @query_homomorphism ts q2 q1 ->
      forall tbls,
        list_set_equiv (queryD q1 tbls) (queryD q2 tbls).
  Proof.
    unfold list_set_equiv. intros; eauto using homomorphism_subset.
  Qed.

  (** Embedded Dependencies **)
  (***************************)
  Record embedded_dependency :=
  { front_types : list type
  ; front_binds : binds_type front_types
  ; front_filter : filter_type front_types
  ; back_types : list type
  ; back_binds : binds_type back_types
  ; back_filter : filter_type (front_types ++ back_types)
  }.

  (** TODO(gmalecha): I should make sure that I am being consistent about
   ** the order of binders
   **)
  Definition embedded_dependencyD (ed : embedded_dependency)
  : DB scheme -> Prop :=
    let front :=
        tableauxD {| types := ed.(front_types)
                   ; binds := ed.(front_binds)
                   ; filter := ed.(front_filter)
                   |}
    in
    let back :=
        let all := bindD ed.(back_binds) in
        let keep := filterD ed.(back_filter) in
        fun tbls base => List.filter keep (List.map (fun x => hlist_app base x) (all tbls))
    in
    fun tbls =>
      forall res,
        In res (front tbls) ->
        exists val,
          In val (back tbls res).

  Definition ed_front (ed : embedded_dependency) : tableaux :=
  {| types := ed.(front_types)
   ; binds := ed.(front_binds)
   ; filter := ed.(front_filter)
   |}.

  Fixpoint member_weaken {T} {ls : list T} {x} ls' (m : member x ls)
  : member x (ls ++ ls') :=
    match m in member _ ls return member x (ls ++ ls') with
    | MZ _ => MZ _ _
    | MN _ _ m' => MN _ (member_weaken ls' m')
    end.

  Fixpoint filter_weaken vars rt
  : filter_type vars -> filter_type (rt :: vars) :=
    List.map (fun x => expr_lift (rt::nil) x).

  Definition ed_back (ed : embedded_dependency) : tableaux :=
  {| types := ed.(front_types) ++ ed.(back_types)
   ; binds := hlist_app ed.(front_binds) ed.(back_binds)
   ; filter := List.map (expr_subst (fun t x => member_weaken ed.(back_types) x)) ed.(front_filter) ++ ed.(back_filter)
   |}.

End with_tables.