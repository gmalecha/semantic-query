Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.Tables.
Require Import SemanticQuery.DataModel.

Set Implicit Arguments.
Set Strict Implicit.

Section with_tables.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.
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
  : DB M scheme -> M (hlist typeD ts) :=
    match names in hlist _ ts return DB M scheme -> M (hlist typeD ts) with
    | Hnil => fun _ => Mret Hnil
    | Hcons n names => fun tbls =>
                             Mmap (fun x => Hcons (fst x) (snd x))
                                  (Mprod (hlist_get n tbls) (bindD names tbls))
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
  : DB M scheme -> M (hlist typeD t.(types)) :=
    let all := bindD t.(binds) in
    let keep := filterD t.(filter) in
    fun tbls => Mbind (all tbls) (fun x => Mguard (keep x) (Mret x)).

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
  : DB M scheme -> M (hlist typeD ts) :=
    fun tbls => Mmap (retD q.(ret)) (tableauxD q.(tabl) tbls).

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
    forall x : Env ts2, filterD f2 x = true ->
                        filterD (map (expr_subst h) f1) x = true.
  Definition ret_homomorphism {T ts1 ts2 : list type}
             (h : types_homomorphism ts1 ts2)
             (f2 : filter_type ts2)
             (r1 : ret_type ts1 T)
             (r2 : ret_type ts2 T) : Type :=
    forall x : Env ts2,
      filterD f2 x = true ->
      retD (hlist_map (fun t e => expr_subst h e) r1) x = retD r2 x.

  Record tableaux_homomorphism (t1 t2 : tableaux) : Type :=
  { vars_mor : types_homomorphism t1.(types) t2.(types)
  ; bindsOk  : binds_homomorphism vars_mor t1.(binds) t2.(binds) (** 1 **)
  ; filterOk : filter_homomorphism vars_mor t1.(filter) t2.(filter) (** 2 **)
  }.

  Record query_homomorphism ts (q1 q2 : query ts) : Type :=
  { th : tableaux_homomorphism q1.(tabl) q2.(tabl)
  ; retOk : ret_homomorphism th.(vars_mor) q2.(tabl).(filter) q1.(ret) q2.(ret)
  }.

  Definition related {T} {F} {ts1 ts2 : list T}
             (h : forall x : T, member x ts1 -> member x ts2)
             (b1 : hlist F ts1)
             (b2 : hlist F ts2) : Prop :=
    forall t (m : member t ts1),
      hlist_get m b1 = hlist_get (h _ m) b2.

  Lemma In_bindD_hlist_get
    : forall (l : type) (ts2 : list type) (tbl_data : DB M scheme)
             (b2 : hlist (fun x : type => member x scheme) ts2)
             (m : member l ts2),
      Mimpl (Mmap (hlist_get m) (bindD b2 tbl_data))
            (hlist_get (hlist_get m b2) tbl_data).
  Proof.
    induction b2.
    { simpl. intros. inversion m. }
    { simpl. intros.
      destruct (member_case m); forward_reason; subst.
      { simpl.
        setoid_rewrite Mmap_compose.
        simpl.
        eapply Proper_Mimpl_Mimpl. red.
        eapply (Mmap_Mprod_L M (hlist_get f tbl_data) (bindD b2 tbl_data) (fun x => x)).
        reflexivity.
        rewrite Mmap_id. reflexivity. }
      { setoid_rewrite Mmap_compose. simpl.
        setoid_rewrite Mmap_Mprod_R. eauto. } }
  Qed.

  Definition types_homomorphism_rest {a b c} (x : types_homomorphism (a :: b) c)
    : types_homomorphism b c :=
    fun t m => x t (MN _ m).

  Definition binds_homomorphism_rest {a b c d e f}
             (bh : @binds_homomorphism (a :: b) c d e f)
    : @binds_homomorphism b c (types_homomorphism_rest d) (hlist_tl e) f :=
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

(*
  Fixpoint apply_types_homomorphism {ts1 ts2} (h : types_homomorphism ts1 ts2)
           (x : hlist typeD ts2) : hlist typeD ts1 :=
    (match ts1 as ts1 return types_homomorphism ts1 ts2 -> hlist typeD ts1 with
     | nil => fun _ => Hnil
     | t1 :: ts1 => fun h => Hcons (hlist_get (h t1 (MZ t1 ts1)) x)
                                   (apply_types_homomorphism (fun x1 m => h x1 (MN t1 m)) x)
     end h).
*)

  Require Import Coq.Classes.Morphisms.
  Instance Proper_Mmap {T U : Type} : Proper ((eq ==> eq) ==> Mimpl ==> Mimpl) (@Mmap M _ T U).
  Proof.
    unfold Mmap.
    do 3 red.
    intros.
    eapply Proper_Mbind_impl. eassumption.
    red. intros.
    eapply Proper_Mret_impl.
    eapply H. reflexivity.
  Qed.
  Lemma Mmap_Mbind : forall {T U V} (m : M T) (f : U -> V) (k : T -> M U),
      Meq (Mmap f (Mbind m k))
          (Mbind m (fun x => Mmap f (k x))).
  Proof.
    intros.
    unfold Mmap.
    rewrite Mbind_assoc.
    reflexivity.
  Qed.
  Lemma Mmap_Mguard : forall {T U} (m : M T) (f : T -> U) p,
      Meq (Mmap f (Mguard p m)) (Mguard p (Mmap f m)).
  Proof.
    intros. unfold Mguard.
    destruct p; try reflexivity.
    unfold Mmap. rewrite Mbind_Mzero. reflexivity.
  Qed.
  Lemma Mmap_Mret : forall {T U} (f : T -> U) x,
      Meq (Mmap f (Mret x)) (Mret (f x)).
  Proof.
    unfold Mmap. intros.
    rewrite Mbind_Mret. reflexivity.
  Qed.

  Lemma hlist_get_hlist_get_Mret_impl_Mbind
    : forall (tbl_data : DB M scheme)
             ts2 (b2 : binds_type ts2) t (m : member t _),
      Mimpl (Mbind (bindD b2 tbl_data)
                   (fun x => (Mret (hlist_get m x))))
            (hlist_get (hlist_get m b2) tbl_data).
  Proof.
    induction m; rewrite (hlist_eta b2); simpl.
    { unfold Mprod. rw_M. simpl.
      rewrite Mbind_perm. rw_M.
      eapply Mbind_ignore. }
    { rewrite <- (IHm (hlist_tl b2)); clear IHm.
      rw_M. simpl.
      rewrite Mbind_perm.
      eapply Proper_Mbind_impl; try reflexivity.
      red. intros.
      eapply Mbind_ignore. }
  Qed.

  Lemma bindD_subset
    : forall ts1 (b1 : hlist (fun x => member x scheme) ts1)
             ts2 (b2 : hlist (fun x => member x scheme) ts2),
      forall tbl_data (h : types_homomorphism ts1 ts2),
          binds_homomorphism h b1 b2 ->
          Mimpl (Mmap (follow_types_homomorphism h) (bindD b2 tbl_data))
                (bindD b1 tbl_data).
  Proof.
    induction b1.
    { simpl. intros.
      rewrite Mmap_ignore. reflexivity. }
    { intros.
      specialize (@IHb1 _ b2 tbl_data (types_homomorphism_rest h)).
      simpl.
      rewrite <- IHb1; clear IHb1.
      { setoid_rewrite Mprod_Mmap_L.
        setoid_rewrite Mmap_compose. simpl.
        unfold Mmap. rw_M.
        red in X.
        rewrite Mbind_perm.
        simpl.
        generalize (X _ (@MZ _ _ _)); simpl; intro.
        subst.
        rewrite (@Mbind_dup M _ _ _ (bindD b2 tbl_data)
                               (fun x : Env ts2 * Env ts2 =>
                                  Mret
                                    (Hcons (hlist_get (h l (MZ l ls)) (snd x))
                                           (follow_types_homomorphism (types_homomorphism_rest h) (fst x))))).
        simpl.
        eapply Proper_Mbind_impl; try reflexivity.
        red. intros.
        rewrite <- hlist_get_hlist_get_Mret_impl_Mbind.
        rw_M. reflexivity. }
      { change b1 with (hlist_tl (Hcons f b1)).
        eapply binds_homomorphism_rest. assumption. } }
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
    { simpl. rewrite IHe1. rewrite IHe2. reflexivity. }
    { reflexivity. }
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

  Lemma related_follow_types_homomorphism
    : forall (types0 types1 : list type)
             (vars_mor0 : types_homomorphism types1 types0)
             (a : Env types0) (t : type) (m : member t types1),
      hlist_get m (follow_types_homomorphism vars_mor0 a) =
      hlist_get (vars_mor0 t m) a.
  Proof.
    induction m; simpl; try reflexivity.
    rewrite IHm. reflexivity.
  Qed.

  Lemma Mguard_impl : forall {T} (a b : bool) (m1 m2 : M T),
      Bool.leb a b ->
      (a = true -> Mimpl m1 m2) ->
      Mimpl (Mguard a m1)
            (Mguard b m2).
  Proof. Admitted.

  Lemma homomorphism_subset ts
    : forall q1 q2,
      @query_homomorphism ts q2 q1 ->
      forall tbls,
        Mimpl (queryD q1 tbls) (queryD q2 tbls).
  Proof.
    unfold queryD, tableauxD.
    destruct 1.
    intros.
    rw_M.
    rewrite <- (@bindD_subset _ (binds (tabl q2)) _ _ tbls _ (bindsOk th0)).
    rw_M.
    eapply Proper_Mbind_impl; try reflexivity.
    red. intros.
    eapply Mguard_impl.
    { destruct th0; simpl in *.
      red. specialize (filterOk0 a).
      destruct (filterD (filter (tabl q1)) a); auto.
      rewrite <- filterOk0; auto.
      eapply related_filterD_subst_test.
      red.
      eapply related_follow_types_homomorphism. }
    { red in retOk0.
      intros. rewrite <- retOk0 by eauto.
      eapply Proper_Mret_impl.
      erewrite <- retD_related; eauto.
      red. eapply related_follow_types_homomorphism. }
  Qed.

  Theorem bihomomorphism_equal ts
    : forall q1 q2,
      @query_homomorphism ts q1 q2 ->
      @query_homomorphism ts q2 q1 ->
      forall tbls,
        Meq (queryD q1 tbls) (queryD q2 tbls).
  Proof.
    red; intros; eauto using homomorphism_subset.
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

  Definition ed_front (ed : embedded_dependency) : tableaux :=
  {| types := ed.(front_types)
   ; binds := ed.(front_binds)
   ; filter := ed.(front_filter)
   |}.

  Fixpoint member_weaken {T} {ls : list T} {x} ls' (m : member x ls)
  : member x (ls ++ ls') :=
    match m in member _ ls return member x (ls ++ ls') with
    | MZ _ _ => MZ _ _
    | MN _ m' => MN _ (member_weaken ls' m')
    end.

  Fixpoint filter_weaken vars rt
  : filter_type vars -> filter_type (rt :: vars) :=
    List.map (fun x => expr_lift (rt::nil) x).

  Definition ed_back (ed : embedded_dependency) : tableaux :=
  {| types := ed.(front_types) ++ ed.(back_types)
   ; binds := hlist_app ed.(front_binds) ed.(back_binds)
   ; filter := List.map (expr_subst (fun t x => member_weaken ed.(back_types) x)) ed.(front_filter) ++ ed.(back_filter)
   |}.

  Definition embedded_dependencyD (ed : embedded_dependency)
  : DB M scheme -> Prop :=
    fun db => Meq (tableauxD (ed_front ed) db)
                  (Mmap (fun x => fst (hlist_split _ _ x))
                        (tableauxD (ed_back ed) db)).

End with_tables.