Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.Tables.
Require Import SemanticQuery.DataModel.
Require Import SemanticQuery.RecordTableaux.

Set Implicit Arguments.
Set Strict Implicit.

(** Cross-product of lists **)
Fixpoint cross {T U V : Type} (f : T -> U -> V) (ts : list T) (us : list U)
: list V :=
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

Section with_schema.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.
  Variables schema : list type.

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


  Fixpoint find_matching {T} {vs} (t : member T schema)
           (ts : hlist (fun rt => member rt schema) vs)
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
                      return forall t : member X schema,
                    t = match pf in (_ = X') return (member X' schema) with
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
             (b1 : hlist (fun x : type => member x schema) nil)
             (b2 : hlist (fun x : type => member x schema) ts2)
  : binds_homomorphism h b1 b2 :=
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

  Section _combine.
    Let combine ts2 (b2 : hlist (fun x : type => member x schema) ts2)
        (l : type) (ls : list type) (m : member l schema)
        (bs1 : hlist (fun x : type => member x schema) ls)
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
             (b1 : hlist (fun x : type => member x schema) ts1)
             (b2 : hlist (fun x : type => member x schema) ts2)
    : list { h : types_homomorphism ts1 ts2
           & binds_homomorphism h b1 b2 } :=
      match b1 in hlist _ ts1
            return list { h : types_homomorphism ts1 ts2
                     & binds_homomorphism h b1 b2 }
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
  End _combine.

  Variable check_entailment
  : forall {ts} (ps : filter_type ts) (g : guard_type ts),
      option (forall vs, filterD ps vs = true ->
                         exprD g vs = true).

  Fixpoint check_filter {ts} (f1 f2 : filter_type ts)
  : option (forall rows, filterD f2 rows = true -> filterD f1 rows = true) :=
    match f1 as f1
          return option (forall rows, filterD f2 rows = true ->
                                      filterD f1 rows = true)
    with
    | nil => Some (fun _ _ => eq_refl)
    | f1 :: fs1 =>
      match check_entailment f2 f1 with
      | None => None
      | Some pf =>
        match check_filter fs1 f2 with
        | None => None
        | Some pf' => Some (fun vs' pf'' =>
                              match eq_sym (pf vs' pf'') in _ = X
                                  , eq_sym (pf' vs' pf'') in _ = Y
                                    return (if X then Y else false) = true
                              with
                              | eq_refl , eq_refl => eq_refl
                              end)
        end
      end
    end.

  Lemma ret_homomorphism_nil
  : forall {vs1 vs2} {ts} (h : types_homomorphism vs1 vs2)
           (f2 : filter_type vs2)
           (r1 : ret_type vs1 ts)
           (r2 : ret_type vs2 nil), ret_homomorphism h f2 Hnil r2.
  Proof.
    intros. red. intros. simpl. rewrite (hlist_eta (retD r2 x)). reflexivity.
  Defined.

  Lemma ret_homomorphism_cons
  : forall {vs1 vs2} {t} {ts} {h : types_homomorphism vs1 vs2}
           {f2 : filter_type vs2}
           {rt}
           {r1 : ret_type vs1 ts}
           {r2 : ret_type vs2 (t :: ts)},
      (forall vs : Env vs2,
       filterD f2 vs = true ->
       exprD (Eq (expr_subst h rt) (hlist_hd r2)) vs = true) ->
      ret_homomorphism h f2 r1 (hlist_tl r2) ->
      ret_homomorphism h f2 (Hcons rt r1) r2.
  Proof.
    intros. red. simpl.
    intros. specialize (H _ H0).
    rewrite (hlist_eta r2). simpl.
    f_equal.
    { simpl in H.
      destruct (val_dec (exprD (expr_subst h rt) x) (exprD (hlist_hd r2) x));
        try congruence. }
    { eauto. }
  Defined.


  Fixpoint check_return {vs1 vs2} {ts} (h : types_homomorphism vs1 vs2)
           (f2 : filter_type vs2)
           (r1 : ret_type vs1 ts)
  : forall (r2 : ret_type vs2 ts), option (ret_homomorphism h f2 r1 r2) :=
    match r1 as r1 in hlist _ ts
          return forall (r2 : ret_type vs2 ts), option (ret_homomorphism h f2 r1 r2)
    with
    | Hnil => fun X => Some (ret_homomorphism_nil _ _ r1 X)
    | Hcons _ _ rt r1' => fun r2 =>
      match check_entailment f2 (Eq (expr_subst h rt) (hlist_hd r2)) with
      | None => None
      | Some pf =>
        match check_return h f2 r1' (hlist_tl r2) with
        | None => None
        | Some pf' => Some (ret_homomorphism_cons pf pf')
        end
      end
    end.

  Fixpoint filter_map {T U} (f : T -> option U) (ls : list T) : list U :=
    match ls with
    | nil => nil
    | l :: ls =>
      match f l with
      | None => filter_map f ls
      | Some x => x :: filter_map f ls
      end
    end.

  Definition find_homomorphisms (t1 t2 : tableaux schema)
  : list (tableaux_homomorphism t1 t2) :=
    let xs := all_bind_homomorphisms t1.(binds) t2.(binds) in
    filter_map (fun (x : { h : types_homomorphism t1.(types) t2.(types)
                         & binds_homomorphism h t1.(binds) t2.(binds) }) =>
                  let '(existT vm bm) := x in
                  match
                    check_filter (map (expr_subst vm) t1.(filter))
                                 t2.(filter)
                  with
                  | None => None
                  | Some fh =>
                    Some {| vars_mor := vm
                          ; bindsOk := bm
                          ; filterOk := fh |}
                  end) xs.

  Definition find_query_homomorphisms {ts} (q1 q2 : query schema ts)
  : list (query_homomorphism q1 q2) :=
    filter_map (fun th =>
                  match check_return _ q2.(tabl).(filter) q1.(ret) q2.(ret) with
                  | None => None
                  | Some pf => Some {| th := th ; retOk := pf |}
                  end) (find_homomorphisms q1.(tabl) q2.(tabl)).

End with_schema.
