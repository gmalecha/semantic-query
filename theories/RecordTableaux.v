Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Tables.

Set Implicit Arguments.
Set Strict Implicit.

Section with_tables.
  Variable tbls : list row_type.

  Definition binds_type : list row_type -> Type :=
    hlist (fun x => member x tbls).

  Definition guard_type (vars : list row_type) : Type :=
    {T : dec_type & expr vars T & expr vars T}.

  Definition filter_type (vars : list row_type) : Type :=
    list (guard_type vars).

  Definition ret_type (vars : list row_type) (result : list dec_type) : Type :=
    hlist (expr vars) result.

  Record tableaux :=
  { types : list row_type
  ; binds : binds_type types
  ; filter : filter_type types
  }.

  Record query (t : list dec_type) : Type :=
  { tabl : tableaux
  ; ret  : ret_type tabl.(types) t
  }.

  Fixpoint bindD {ts : list row_type} (names : binds_type ts)
    : hlist table tbls -> list (hlist row ts) :=
    match names in hlist _ ts return hlist table tbls -> list (hlist row ts) with
    | Hnil => fun _ => Hnil :: nil
    | Hcons _ _ n names => fun tbls =>
                             cross (fun a b => Hcons a b) (hlist_get n tbls) (bindD names tbls)
    end.

  Fixpoint exprD {T} {ls} (e : expr ls T) {struct e} : hlist row ls -> type T :=
    match e in expr _ T return hlist row ls -> type T with
    | Proj _ _ v c => fun vars => hlist_get c (hlist_get v vars)
    end.

  Definition guardD {ts : list row_type} (g : guard_type ts)
  : hlist row ts -> bool :=
    let '(existT2 t f1 f2) := g in
    let f1 := exprD f1 in
    let f2 := exprD f2 in
    fun rows =>
      match t.(eq_dec) (f1 rows) (f2 rows) with
      | left _ => true
      | right _ => false
      end.

  Fixpoint filterD {ts : list row_type} (f : filter_type ts)
  : hlist row ts -> bool :=
    match f with
    | nil => fun _ => true
    | f :: fs =>
      let fD := guardD f in
      let rD := filterD fs in
      fun rows => if fD rows then rD rows else false
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

  Definition retD {ts ts'} (rt : ret_type ts ts') : hlist row ts -> row ts' :=
    fun vars => hlist_map (fun t e => exprD e vars) rt.

  Definition queryD ts (q : query ts)
  : hlist table tbls -> list (hlist type ts) :=
    fun tbls => List.map (retD q.(ret)) (tableauxD q.(tabl) tbls).

  Fixpoint expr_subst {vars vars'} (f :forall {x}, member x vars -> member x vars') (T : _)
           (e : expr vars T) {struct e} : expr vars' T :=
    match e in expr _ T return expr vars' T with
    | Proj _ _ v c => Proj (f v) c
    end.
  Arguments expr_subst {_ _} _ _ _.

  Definition guard_subst {vars vars'} (f : forall {T}, expr vars T -> expr vars' T)
             (x : guard_type vars)
    : guard_type vars' :=
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
             (f1 : list (guard_type ts1))
             (f2 : list (guard_type ts2)) : Type :=
    forall x, filterD (map (guard_subst (expr_subst h)) f1) x = filterD f2 x.

  Record tableaux_homomorphism (t1 t2 : tableaux) : Type :=
  { vars_mor : types_homomorphism t1.(types) t2.(types)
  ; bindsOk  : binds_homomorphism vars_mor t1.(binds) t2.(binds) (** 1 **)
  ; filterOk : filter_homomorphism vars_mor t1.(filter) t2.(filter) (** 2 **)
  }.

  Fixpoint member_eq' {T} {a b : T} {ls} (m1 : member a ls) (m2 : member b ls)
  : option { pf : b = a | m1 = match pf in _ = X return member X ls with
                               | eq_refl => m2
                               end } :=
      (match m1 as m1 in member _ ls
             return forall m2 : member b ls,
                    option { pf : b = a | m1 = match pf in _ = X
                                                     return member X ls
                                               with
                                               | eq_refl => m2
                                               end }
       with
       | MZ ls' => fun X : member b (a :: ls') =>
         match X as X in member _ ls
               return match ls as ls return member b ls -> Type with
                      | nil => fun _ => Empty_set
                      | b' :: bs' => fun X : member b (b' :: bs') =>
                        option { pf : b = b' | (@MZ _ _ bs') =
                                              match pf in _ = X
                                                    return member X (b' :: bs')
                                              with
                                              | eq_refl => X
                                              end }
                      end X
         with
         | MZ _ => Some (@exist _ _ eq_refl eq_refl)
         | MN _ _ _ => None
         end
       | MN x xs m1' => fun X : member b (x :: xs) =>
         match X in member _ ls
               return match ls as ls
                            return member b ls -> Type
                      with
                      | nil => fun _ => Empty_set
                      | b' :: bs' => fun (X : member b (b' :: bs')) =>
                                       forall m1' : member a bs',
                        option { pf : b = a | (@MN _ a b' bs' m1') =
                                              match pf in _ = X
                                                    return member X (b' :: bs')
                                              with
                                              | eq_refl => X
                                              end }
                      end X
         with
         | MZ _ => fun _ => None
         | MN l ls m2' => fun m1' =>
           match @member_eq' _ _ _ _ m1' m2' with
           | None => None
           | Some (exist pf pf') =>
             Some (@exist _ _ pf
                          (match pf as pf in _ = X
                                 return forall m1'0 : member X ls,
                               m1'0 =
                               match pf in _ = X0 return member X0 ls with
                               | eq_refl => m2'
                               end ->
                               MN l m1'0 =
                               match pf in _ = X0
                                     return member X0 (l :: ls)
                               with
                               | eq_refl => MN l m2'
                               end
                           with
                           | eq_refl => fun _ pf => f_equal _ pf
                           end m1' pf'))
           end
         end m1'
       end m2).


    Fixpoint find_matching {T} {vs} (t : member T tbls)
             (ts : hlist (fun rt => member rt tbls) vs)
    : list { t' : member _ vs | hlist_get t' ts = t } :=
      match ts in hlist _ vs
            return list { t' : member _ vs | hlist_get t' ts = t }
      with
      | Hnil => nil
      | Hcons l ls m h =>
        match member_eq' t m with
        | None => nil
        | Some (exist pf pf') =>
          @exist _ _ match pf in _ = X return member X (l :: ls) with
                     | eq_refl => MZ _ _
                     end
                 (match pf as pf in _ = X
                        return forall t : member X tbls,
                      t = match pf in (_ = X') return (member X' tbls) with
                          | eq_refl => m
                          end ->
                      hlist_get
                        match pf in (_ = X') return (member X' (l :: ls)) with
                        | eq_refl => MZ l ls
                        end (Hcons m h) = t
                  with
                  | eq_refl => fun _ => @eq_sym _ _ _
                  end t pf') :: nil
        end ++ List.map (fun x : {t' : member T ls | hlist_get t' h = t} =>
                           let '(exist a b) := x in
                           @exist _ (fun x => hlist_get x (Hcons m h) = t)
                                  (MN _ a) b) (@find_matching T ls t h)
      end.

    Definition types_homomorphism_nil ts2 : types_homomorphism nil ts2 :=
      fun _ m =>
        match m in member _ X return match X with
                                     | nil => member _ ts2
                                     | _ :: _ => unit
                                     end
        with
        | MZ _ => tt
        | MN _ _ _ => tt
        end.

    Definition binds_homomorphism_nil ts2 (h : types_homomorphism nil ts2)
               (b1 : hlist (fun x : row_type => member x tbls) nil)
               (b2 : hlist (fun x : row_type => member x tbls) ts2)
    : @binds_homomorphism nil ts2 h b1 b2 :=
      fun t x =>
        match x as y in member _ X
              return match X with
                     | nil => hlist_get x b1 = hlist_get (h t x) b2
                     | _ :: _ => unit
                     end
        with
        | MZ _ => tt
        | MN _ _ _ => tt
        end.

    Section foo.
    Let combine ts2 (b2 : hlist (fun x : row_type => member x tbls) ts2)
        (l : row_type) (ls : list row_type) (m : member l tbls)
        (bs1 : hlist (fun x : row_type => member x tbls) ls)
        (m' : member l ts2) (pf' : hlist_get m' b2 = m)
        (th' : types_homomorphism ls ts2)
        (bh' : binds_homomorphism th' bs1 b2)
    : {h : types_homomorphism (l :: ls) ts2 &
       binds_homomorphism h (Hcons m bs1) b2} :=
      @existT (types_homomorphism (l::ls) ts2)
              (fun h => binds_homomorphism h (Hcons m bs1) b2)
              (fun x (m'' : member x (l :: ls))  =>
                 match m'' in member _ X
                       return match X with
                              | nil => Empty_set
                              | x' :: xs =>
                                member x' ts2 -> (member x xs -> member x ts2) -> member x ts2
                              end
                 with
                 | MZ _ => fun X _ => X
                 | MN _ _ m''' => fun _ X => X m'''
                 end m' (th' _))
              (fun t (x : member t (l :: ls)) =>
                 match x as x in member _ X
                       return match X as X return member t X -> Prop with
                              | nil => fun _ => False
                              | X :: XS => fun x =>
                                forall m' th' m bs1,
                                  hlist_get m' b2 = m ->
                                  binds_homomorphism th' bs1 b2 ->
                                  hlist_get x (Hcons m bs1) =
                                  hlist_get
                                    (match
                                        x in (member _ X)
                                        return
                                        match X with
                                        | nil => Empty_set
                                        | x' :: xs =>
                                          member x' ts2 -> (member t xs -> member t ts2) -> member t ts2
                                        end
                                      with
                                      | MZ ls0 =>
                                        fun (X : member t ts2) (_ : member t ls0 -> member t ts2) => X
                                      | MN l0 ls0 m''' =>
                                        fun (_ : member l0 ts2) (X : member t ls0 -> member t ts2) =>
                                          X m'''
                                      end m' (th' t)) b2
                              end x
                 with
                 | MZ _ => fun _ _ _ _ X _ => @eq_sym _ _ _ X
                 | MN _ _ _ => fun _ _ _ _ _ X => X _ _
                 end m' th' m bs1 pf' bh').


    Fixpoint all_bind_homomorphisms {ts1 ts2}
             (b1 : hlist (fun x : row_type => member x tbls) ts1)
             (b2 : hlist (fun x : row_type => member x tbls) ts2)
    : list { h : types_homomorphism ts1 ts2
           & @binds_homomorphism ts1 ts2 h b1 b2 } :=
      match b1 in hlist _ ts1
            return list { h : types_homomorphism ts1 ts2
                        & @binds_homomorphism ts1 ts2 h b1 b2 }
      with
      | Hnil => (@existT _ _ (types_homomorphism_nil ts2)
                         (@binds_homomorphism_nil ts2 _ Hnil b2)) :: nil
      | Hcons l ls m bs1 =>
        cross (fun (cur : {t' : member l ts2 | hlist_get t' b2 = m})
                   (rest : {h : types_homomorphism ls ts2 & binds_homomorphism h bs1 b2}) =>
                 let '(exist m' pf') := cur in
                 let '(existT th' bh') := rest in
                 combine m' pf' bh')
              (find_matching m b2)
              (all_bind_homomorphisms bs1 b2)
      end.
    End foo.

    Fixpoint expr_eq {vs} {t} (e1 e2 : expr vs t) {struct e1}
    : option (e1 = e2).
    refine
      (match e1 as e1 in expr _ t1 , e2 as e2 in expr _ t2
             return forall pf : t1 = t2, option (match pf in _ = X return expr _ X with
                                                 | eq_refl => e1
                                                 end = e2)
       with
       | Proj _ _ t1 f1 , Proj _ _ t2 f2 => fun pf =>
         _ 
       end eq_refl).
    refine
      (match pf as pf in _ = y
            return forall f2 : member y r0,
           option (match pf in (_ = X) return (expr vs X) with
                   | eq_refl => Proj t1 f1
                   end = Proj t2 f2)
      with
      | eq_refl => fun f2 =>
        match member_eq' t1 t2 with
        | None => None
        | Some (exist pf pf') =>
          match member_eq' f1 match pf in _ = X return member _ X with
                             | eq_refl => f2
                             end
          with
          | None => None
          | Some (exist pf'' pf''') => Some _
          end
        end
      end f2); clear pf.
    destruct pf0. destruct pf'.
    f_equal. subst. clear.
    admit. (** This requires decidable equality on types **)
    Defined.

    Definition check_guard {ts1} (g1 g2 : guard_type ts1)
      : option (forall r, guardD g1 r = guardD g2 r).
      destruct g1. destruct g2; simpl.
    Admitted.

    Definition check_filter {ts} (f1 f2 : filter_type ts)
    : option (forall rows, filterD f1 rows = filterD f2 rows).
    Admitted.

    Fixpoint filter_map {T U} (f : T -> option U) (ls : list T) : list U :=
      match ls with
      | nil => nil
      | l :: ls =>
        match f l with
        | None => filter_map f ls
        | Some x => x :: filter_map f ls
        end
      end.

  Definition find_homomorphisms (t1 t2 : tableaux)
  : list (tableaux_homomorphism t1 t2) :=
    let xs := all_bind_homomorphisms t1.(binds) t2.(binds) in
    filter_map (fun (x : { h : types_homomorphism t1.(types) t2.(types)
                         & binds_homomorphism h t1.(binds) t2.(binds) }) =>
                  let '(existT vm bm) := x in
                  match
                    check_filter (map (guard_subst (expr_subst vm)) t1.(filter))
                                 t2.(filter)
                  with
                  | None => None
                  | Some fh =>
                    Some {| vars_mor := vm
                          ; bindsOk := bm
                          ; filterOk := fh |}
                  end) xs.

  Record query_homomorphism ts (q1 q2 : query ts) : Type :=
  { th : tableaux_homomorphism q1.(tabl) q2.(tabl)
  ; retOk : forall r, filterD (map (guard_subst (expr_subst th.(vars_mor))) q1.(tabl).(filter)) r = true ->
              retD (hlist_map (fun T (x : expr (types q1.(tabl)) T) => expr_subst th.(vars_mor) _ x) q1.(ret)) r =
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
      forall (x1 : dec_type) (e : expr types1 x1),
        exprD (expr_subst vars_mor0 x1 e) x0 = exprD e x.
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
        l : list {T : dec_type & expr (types tabl0) T & expr (types tabl0) T},
        filterD l x = filterD (map (guard_subst (expr_subst vars_mor0)) l) x0.
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
             (ret0 : hlist (expr types0) ts),
        retD ret0 x =
        retD
          (hlist_map
             (fun (T : dec_type) (x1 : expr types0 T) => expr_subst vars_mor0 T x1)
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

  (** Embedded Dependencies **)
  (***************************)
  Record embedded_dependency :=
  { front_types : list row_type
  ; front_binds : binds_type front_types
  ; front_filter : filter_type front_types
  ; back_types : list row_type
  ; back_binds : binds_type back_types
  ; back_filter : filter_type (front_types ++ back_types)
  }.

  (** TODO(gmalecha): I should make sure that I am being consistent about
   ** the order of binders
   **)
  Definition embedded_dependencyD (ed : embedded_dependency)
  : hlist table tbls -> Prop :=
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
    List.map (fun x =>
                let '(existT2 t l r) := x in
                @existT2 _ _ _ t
                         (@expr_weaken vars rt _ l)
                         (@expr_weaken vars rt _ r)).


  Definition ed_back (ed : embedded_dependency) : tableaux :=
  {| types := ed.(front_types) ++ ed.(back_types)
   ; binds := hlist_app ed.(front_binds) ed.(back_binds)
   ; filter := List.map (guard_subst (expr_subst (fun t x => member_weaken ed.(back_types) x))) ed.(front_filter) ++ ed.(back_filter)
  |}.


End with_tables.