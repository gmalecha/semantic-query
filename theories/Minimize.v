Require Import Coq.Lists.List.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.Tables.
Require Import SemanticQuery.RecordTableaux.
Require Import SemanticQuery.Chase.

Set Implicit Arguments.
Set Strict Implicit.

Section with_schema.
  Variable scheme : list type.

  Variable check_entailment
  : forall (ts : list type) (ps : filter_type ts) (g : guard_type ts),
   option (forall vs : Env ts, filterD ps vs = true -> exprD g vs = true).

  (** this finds all of the variables that I can replace this one with *)
  Fixpoint find_candidates {t} (m : member t scheme) ts (bt : binds_type scheme ts)
  : list (member t ts) :=
    match bt in hlist _ ts return list (member t ts) with
    | Hnil => nil
    | Hcons l ls m' bt' =>
      match HomomorphismSearch.member_eq' m' m with
      | Some (exist pf _) => match eq_sym pf in _ = t return member t (l :: ls) with
                             | eq_refl => @MZ _ l ls
                             end :: nil
      | None => nil
      end ++ List.map (@MN _ _ l ls) (@find_candidates t m _ bt')
    end.

  Fixpoint first_of {T U} (f : T -> option U) (ls : list T) : option U :=
    match ls with
    | nil => None
    | l :: ls => match f l with
                 | None => first_of f ls
                 | Some x => Some x
                 end
    end.

  Fixpoint remove {t} (ts ts' : list type)
           (binds : binds_type scheme ts) (binds' : binds_type scheme ts')
           {struct binds'}
  : filter_type (ts ++ ts') -> ret_type (ts ++ ts') t -> query scheme t.
  refine
    match binds' in hlist _ ts'
          return filter_type (ts ++ ts') -> ret_type (ts ++ ts') t ->
                 query scheme t
    with
    | Hnil => fun fs rt =>
                {| tabl := {| binds := match eq_sym (app_nil_r_trans ts) in _ = X
                                           return binds_type scheme X
                                       with
                                       | eq_refl => binds
                                       end
                            ; filter := fs
                            |}
                 ; ret := rt |}
    | Hcons l ls m binds' => fun fs rt =>
      match
        first_of _ (find_candidates m binds')
      with
      | None => match app_ass_trans ts (l :: nil) ls in _ = X
                      return filter_type X -> ret_type X t -> query scheme t
                with
                | eq_refl => @remove _ (ts ++ l :: nil) ls (hlist_app binds (Hcons m Hnil))
                                     binds'
                end fs rt
      | Some x => _
      end
    end.
  (* replace all occurances of m with m0 **)
  refine
    (fun m0 =>
       let esubst t m := @expr_subst _ _ (member_map_app
                            (fun _ x => x)
                            (fun t (m : member t (l :: ls)) =>
                               match m in member _ x
                                     return match x with
                                            | nil => unit
                                            | a :: b => member a b -> member _ _ 
                                            end
                               with
                               | MZ _ => fun X => X
                               | MN _ _ X => fun _ => X
                               end m0)) t m in
     let fs' := filter_subst (esubst Bool) fs in
     let rt' := hlist_map esubst rt in
     let q  := {| tabl := {| binds := hlist_app binds (Hcons m binds'0)
                           ; filter := fs |}
                ; ret  := rt |} in
     let q' := {| tabl := {| binds := hlist_app binds binds'0
                           ; filter := fs' |}
                ; ret  := rt' |} in
     if query_equiv check_entailment q q' then
       Some (fs', rt')
     else
       None).
  refine (@remove _ ts ls binds binds'0 (fst x) (snd x)).
  Defined.

  Definition minimize {t} (q : query scheme t) : query scheme t :=
    @remove _ nil q.(tabl).(types)
                  Hnil
                  q.(tabl).(binds)
                  q.(tabl).(filter)
                  q.(ret).
End with_schema.