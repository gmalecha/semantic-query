Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Tables.

Set Implicit Arguments.
Set Strict Implicit.

Section with_tables.
  Variable tbls : list row_type.

  Record tableaux :=
  { types : list row_type
  ; binds : hlist (fun x => member x tbls) types
  ; filter : list { T : dec_type & expr T types & expr T types }
  }.

  Record query (t : list dec_type) : Type :=
  { tabl : tableaux
  ; ret  : hlist (fun t => expr t tabl.(types)) t
  }.

  Fixpoint join {T U V : Type} (f : T -> U -> V) (ts : list T) (us : list U) : list V :=
    match ts , us with
    | nil , _ => nil
    | _ , nil => nil
    | t :: ts , u :: us => f t u :: join f ts us
    end.

  Fixpoint cross {T U V : Type} (f : T -> U -> V) (ts : list T) (us : list U) : list V :=
    match ts with
    | nil => nil
    | t :: ts => List.map (f t) us ++ cross f ts us
    end.


  Lemma In_cross : forall {T U V} (f : T -> U -> V) us ts,
      forall x,
        In x (cross f ts us) <->
        exists t u,
          In t ts /\ In u us /\ x = f t u.
  Proof.
    induction ts; simpl; intros.
    { split.
      { inversion 1. }
      { intros.
        forward_reason. assumption. } }
    { rewrite List.in_app_iff.
      rewrite IHts; clear IHts.
      rewrite in_map_iff.
      split; intros; forward_reason.
      { destruct H; forward_reason.
        { subst. do 2 eexists; eauto. }
        { do 2 eexists; eauto. } }
      { destruct H; subst.
        { left; eauto. }
        { right. eauto. } } }
  Qed.

  Fixpoint bindD {ts : list row_type} (names : hlist (fun x => member x tbls) ts)
    : hlist table tbls -> list (hlist row ts) :=
    match names in hlist _ ts return hlist table tbls -> list (hlist row ts) with
    | Hnil => fun _ => Hnil :: nil
    | Hcons _ _ n names => fun tbls =>
                             cross (fun a b => Hcons a b) (hlist_get n tbls) (bindD names tbls)
    end.

  Fixpoint exprD {T} {ls} (e : expr T ls) {struct e} : hlist row ls -> type T :=
    match e in expr _ _ return hlist row ls -> type T with
    | Proj _ v c => fun vars => hlist_get c (hlist_get v vars)
    end.

  Fixpoint filterD {ts : list row_type} (f : list { T : dec_type & expr T ts & expr T ts })
    : hlist row ts -> bool :=
    match f with
    | nil => fun _ => true
    | (existT2 t f1 f2) :: fs => fun rows =>
                                   match t.(eq_dec) (exprD f1 rows) (exprD f2 rows) with
                                   | left _ => filterD fs rows
                                   | right _ => false
                                   end
    end.

  (** The return type here is a bit odd. I'm just gluing the rows together as an hlist.
   ** Queries seem more natural.
   **)
  Definition tableauxD (t : tableaux) : hlist table tbls -> list (hlist row t.(types)) :=
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

  Definition retD {ts ts'} (rt : hlist (fun t => expr t ts) ts') : hlist row ts -> row ts' :=
    fun vars => hlist_map (fun t e => exprD e vars) rt.

  Definition queryD ts (q : query ts) : hlist table tbls -> list (hlist type ts) :=
    fun tbls => List.map (retD q.(ret)) (tableauxD q.(tabl) tbls).

  Fixpoint subst_expr {vars vars'} (f :forall {x}, member x vars -> member x vars') (T : _)
           (e : expr T vars) {struct e} : expr T vars' :=
    match e with
    | Proj _ v c => Proj (f v) c
    end.
  Arguments subst_expr {_ _} _ _ _.

  Definition subst_test {vars vars'} (f : forall {T}, expr T vars -> expr T vars')
             (x : { T : dec_type & expr T vars & expr T vars })
    : { T : dec_type & expr T vars' & expr T vars' } :=
    match x with
    | existT2 T x1 x2 =>
      @existT2 _ _ _ T (f x1) (f x2)
    end.

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
  Definition types_homomorphism (ts1 ts2 : list row_type) : Type :=
    forall x : row_type, member x ts1 -> member x ts2.
  Definition binds_homomorphism {ts1 ts2 : list row_type}
             (h : types_homomorphism ts1 ts2)
             (b1 : hlist (fun x => member x tbls) ts1)
             (b2 : hlist (fun x => member x tbls) ts2) : Type :=
    forall t (x : member t _), hlist_get x b1 = hlist_get (h _ x) b2.
  Definition filter_homomorphism {ts1 ts2 : list row_type}
             (h : types_homomorphism ts1 ts2)
             (f1 : list { T : dec_type & expr T ts1 & expr T ts1 })
             (f2 : list { T : dec_type & expr T ts2 & expr T ts2 }) : Type :=
    forall x, filterD (map (subst_test (subst_expr h)) f1) x = filterD f2 x.

  Record tableaux_homomorphism (t1 t2 : tableaux) : Type :=
  { vars_mor : types_homomorphism t1.(types) t2.(types)
  ; bindsOk  : binds_homomorphism vars_mor t1.(binds) t2.(binds) (** 1 **)
  ; filterOk : filter_homomorphism vars_mor t1.(filter) t2.(filter) (** 2 **)
  }.

  Record query_homomorphism ts (q1 q2 : query ts) : Type :=
  { th : tableaux_homomorphism q1.(tabl) q2.(tabl)
  ; retOk : forall r, filterD (map (subst_test (subst_expr th.(vars_mor))) q1.(tabl).(filter)) r = true ->
              retD (hlist_map (fun T (x : expr T (types q1.(tabl))) => subst_expr th.(vars_mor) _ x) q1.(ret)) r =
              retD q2.(ret) r
  }.

  Definition related {ts1 ts2 : list row_type} (h : forall x : row_type, member x ts1 -> member x ts2)
             (b1 : hlist row ts1)
             (b2 : hlist row ts2) : Prop :=
    forall t (m : member t ts1),
      hlist_get m b1 = hlist_get (h _ m) b2.

  Lemma In_bindD_hlist_get
    : forall (l : row_type) (ts2 : list row_type) (tbl_data : hlist table tbls)
             (b2 : hlist (fun x : row_type => member x tbls) ts2)
             (x : hlist row ts2)
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
    : forall ts1 (b1 : hlist (fun x => member x tbls) ts1)
             ts2 (b2 : hlist (fun x => member x tbls) ts2),
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

  Lemma related_exprD_subst_expr
  : forall (types0 types1 : list row_type)
           (vars_mor0 : types_homomorphism types1 types0)
           (x0 : hlist row types0) (x : hlist row types1),
      related vars_mor0 x x0 ->
      forall (x1 : dec_type) (e : expr x1 types1),
        exprD (subst_expr vars_mor0 x1 e) x0 = exprD e x.
  Proof.
    induction e.
    { simpl. red in H.
      f_equal. symmetry. eapply H. }
  Qed.

  Lemma related_filterD_subst_test
    : forall (ts : list dec_type) (q1 : query ts) (tabl0 : tableaux)
             (vars_mor0 : types_homomorphism (types tabl0) (types (tabl q1)))
             (x0 : hlist row (types (tabl q1))) (x : hlist row (types tabl0)),
      related vars_mor0 x x0 ->
      forall
        l : list {T : dec_type & expr T (types tabl0) & expr T (types tabl0)},
        filterD l x = filterD (map (subst_test (subst_expr vars_mor0)) l) x0.
  Proof.
    induction l; simpl; auto.
    { destruct a; simpl.
      rewrite <- IHl.
      do 2 erewrite related_exprD_subst_expr by eauto.
      reflexivity. }
  Qed.

  Lemma retD_related
    : forall (types1 types0 : list row_type)
             (x0 : hlist row types1) (x : hlist row types0)
             (vars_mor0 : types_homomorphism types0 types1),
      related vars_mor0 x x0 ->
      forall (ts : list dec_type)
             (ret0 : hlist (fun t : dec_type => expr t types0) ts),
        retD ret0 x =
        retD
          (hlist_map
             (fun (T : dec_type) (x1 : expr T types0) => subst_expr vars_mor0 T x1)
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
    { rewrite <- retOk0.
      { destruct q2. simpl in *. clear - H.
        destruct q1. simpl in *. clear - H.
        destruct tabl0; destruct tabl1. simpl in *.
        eauto using retD_related. }
      { rewrite <- H1.
        red in filterOk0.
        rewrite <- filterOk0. reflexivity. } }
    { assumption. }
    { red in filterOk0. clear retOk0 bindsOk0.
      rewrite <- filterOk0 in H1.
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

End with_tables.
