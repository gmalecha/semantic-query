Require Import Coq.Lists.List.
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

  Fixpoint member_map_app {T: Type} {xs xs' ys ys'}
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
End with_scheme.