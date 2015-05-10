Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import SemanticQuery.Tables.

Set Implicit Arguments.

Section with_tables.
  Variable tbls : list row_type.

  Definition binds_type : list row_type -> Type :=
    hlist (fun x => member x tbls).

  Definition filter_type (vars : list row_type) : Type :=
    list { T : dec_type & expr T vars & expr T vars }.

  Definition ret_type (vars : list row_type) (result : list dec_type) : Type :=
    hlist (fun t => expr t vars) result.

  Record tableaux :=
  { types : list row_type
  ; binds : binds_type types
  ; filter : filter_type types
  }.
End with_tables.

Inductive expr_ast : Type :=
| Var : nat -> nat -> expr_ast.

Inductive query_ast : Type :=
| Bind  : string -> nat -> query_ast -> query_ast
| Guard : expr_ast -> expr_ast -> query_ast -> query_ast
| Ret : query_ast.

Section tables.
  Variable tbls : list row_type.

  Inductive WT_expr (vars : list row_type) : expr_ast -> dec_type -> Type :=
  | WT_Proj : forall t f T,
      match nth_error vars t with
      | None => None
      | Some fs => nth_error fs f
      end = Some T ->
      WT_expr vars (Var t f) T.

  Inductive WT_query (vars : list row_type) : query_ast -> Type :=
  | WT_Bind : forall v ti rt q',
      nth_error tbls ti = Some rt ->
      WT_query (rt :: vars) q' ->
      WT_query vars (Bind v ti q')
  | WT_Guard : forall l r q' T,
      WT_expr vars l T ->
      WT_expr vars r T ->
      WT_query vars q' ->
      WT_query vars (Guard l r q')
  | WT_Ret : WT_query vars Ret.
End tables.

Let tbls_demo :=
  SemanticQuery.Tables.Demo.tt_names ::
  SemanticQuery.Tables.Demo.tt_manager ::
  nil.

Existing Class WT_query.
Ltac type_check_e e :=
  match e with
  | Var ?t ?f => eapply WT_Proj; [ simpl nth_error ; reflexivity ]
  end.
Ltac type_check_q t :=
  match t with
  | Ret => apply WT_Ret
  | Bind ?l ?r ?q' =>
    eapply WT_Bind; [ simpl nth_error ; reflexivity | type_check_q q' ]
  | Guard ?l ?r ?q' =>
    eapply WT_Guard; [ type_check_e l | type_check_e r | instantiate ; type_check_q q' ]
  end.
Hint Extern 0 (WT_query _ _ ?q) => (type_check_q q) : typeclass_instances.

  Fixpoint weaken_expr vars rt T (e : expr T vars) {struct e}
  : expr T (rt :: vars) :=
    match e in @expr T vars return expr T (rt :: vars) with
    | Proj _ _ _ t f => Proj (Member.MN _ t) f
    end.

  Fixpoint weaken_filter vars rt
  : filter_type vars -> filter_type (rt :: vars) :=
    List.map (fun x =>
                let '(existT2 t l r) := x in
                @existT2 _ _ _ t
                         (@weaken_expr vars rt _ l)
                         (@weaken_expr vars rt _ r)).

  Fixpoint to_member T (ls : list T) (n : nat) (t : T) {struct n}
  : nth_error ls n = Some t -> Member.member t ls :=
    match n as n , ls as ls
          return nth_error ls n = Some t -> Member.member t ls
    with
    | 0 , l :: ls => fun pf : Some l = Some t =>
                       match eq_sym pf in _ = t_
                             return match t_ with
                                    | Some t' =>
                                      Member.member t (t' :: ls)
                                    | None => Empty_set
                                    end
                       with
                       | eq_refl => Member.MZ _ _
                       end
    | S n , _ :: ls => fun pf => Member.MN _ (@to_member _ ls _ _ pf)
    | _ , _ => fun pf : None = Some _ => match pf in _ = t
                                               return match t with
                                                      | Some _ => _
                                                      | None => unit
                                                      end
                                         with
                                         | eq_refl => tt
                                         end
    end.

Fixpoint compile_e (vars : list row_type) T (q : expr_ast)
         (wt : WT_expr vars q T) {struct wt} : expr T vars :=
  match wt with
  | WT_Proj v f T pf =>
    match nth_error vars v as X return match X with
                                       | Some fs => nth_error fs f
                                       | None => None
                                       end = Some T ->
                                       nth_error vars v = X ->
                                       expr T vars
    with
    | None => fun pf => match pf in _ = t return match t with
                                                 | None => unit
                                                 | Some _ => _ -> expr T vars
                                                 end with
                        | eq_refl => tt
                        end
    | Some X => fun pf_f pf_v => @Proj _ T _ (to_member _ _ pf_v) (to_member _ _ pf_f)
    end pf eq_refl
  end.

Fixpoint compile_q' (tbls vars : list row_type) (q : query_ast)
         (bs : binds_type tbls vars) (fs : filter_type vars)
         (wt : WT_query tbls vars q)  : tableaux tbls.
refine
  match wt with
  | WT_Ret => {| types := vars ; binds := bs ; filter := fs |}
  | @WT_Bind x ti t_t q' pf_eq pf_wt =>
    @compile_q' tbls (t_t :: vars) q' (Hcons (to_member _ _ pf_eq) bs) (@weaken_filter vars _ fs) pf_wt
  | @WT_Guard l r q' T wt_l wt_r wt_q =>
    @compile_q' tbls vars q' bs (@existT2 _ _ _ T (compile_e wt_l) (compile_e wt_r) :: fs) wt_q
  end.
Defined.

Definition compile_q tbls q wt : tableaux tbls :=
  Eval unfold compile_q' in
  @compile_q' tbls nil q Hnil nil wt.

Arguments compile_q _ _ {_}.

Delimit Scope query_scope with query.
Notation "'assert' e1 == e2  ;; q" := (@Guard e1 e2 q%query) (at level 20, e1 at next level, e2 at next level, q at level 19) : query_scope.
Notation "x <- e2  ;; q" := (@Bind x e2 q%query) (at level 20, q at level 19) : query_scope.

Notation "'QUERY' tbls 'USING' q" :=
  (@compile_q tbls q%query _) (at level 20, only parsing).

Goal True.
  pose (QUERY tbls_demo USING ("x" <- 0 ;;
                               assert (Var 0 0) == (Var 0 0) ;;
                               Ret)).
  exact I.
Defined.