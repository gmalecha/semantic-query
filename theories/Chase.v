Require Import Coq.Lists.List.
Require Import SemanticQuery.Tables.
Require Import SemanticQuery.RecordTableaux.

Section with_scheme.
  Variable scheme : list row_type.

  (** TODO: these should move **)
  Fixpoint member_lift {T} {t : T} (vs vs' : list T) (m : member t vs')
  : member t (vs ++ vs') :=
    match vs as vs return member t (vs ++ vs') with
    | nil => m
    | v :: vs => MN _ (member_lift _ _ m)
    end.

  Fixpoint expr_lift {T} vs vs' (e : expr vs' T) {struct e}
  : expr (vs ++ vs') T :=
    match e in expr _ T return expr (vs ++ vs') T with
    | Proj _ _ a b => Proj (member_lift _ _ a) b
    end.

  Definition filter_lift vs vs'
  : filter_type vs' -> filter_type (vs ++ vs') :=
    List.map (fun a =>
                let '(existT2 a b c) := a in
                @existT2 _ _ _ a (expr_lift vs vs' b) (expr_lift vs vs' c)).

  Fixpoint member_weaken_app {T} {t : T} (vs vs' : list T) (m : member t vs')
  : member t (vs' ++ vs) :=
    match m in member _ vs' return member t (vs' ++ vs) with
    | MZ _ => MZ _ _
    | MN _ _ m => MN _ (member_weaken_app _ _ m)
    end.

  Fixpoint expr_weaken_app {T} vs vs' (e : expr vs' T) {struct e}
  : expr (vs' ++ vs) T :=
    match e in expr _ T return expr (vs' ++ vs) T with
    | Proj _ _ a b => Proj (member_weaken_app _ _ a) b
    end.

  Definition filter_weaken_app vs vs'
  : filter_type vs' -> filter_type (vs' ++ vs) :=
    List.map (fun a =>
                let '(existT2 a b c) := a in
                @existT2 _ _ _ a
                         (expr_weaken_app vs vs' b)
                         (expr_weaken_app vs vs' c)).

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

  Fixpoint member_map_app {T: Type} {xs xs' ys ys'}
           (mx : forall t, member t xs -> member t ys)
           (mx' : forall t, member t xs' -> member t ys')
           (t : T) (m : member t (xs ++ xs'))
    : member t (ys ++ ys') :=
    match member_app_case _ _ _ m with
    | inl m => member_weaken_app _ _ (mx _ m)
    | inr m => member_lift _ _ (mx' _ m)
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
                            List.map (guard_subst map_expr) c.(back_filter)
                |}
     ; ret := hlist_map (fun t e => expr_weaken_app _ _ e) q.(ret)
     |}.
End with_scheme.