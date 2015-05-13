Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ExtLib.Core.RelDec.
Require Import SemanticQuery.Tables.
Require Import SemanticQuery.RecordTableaux.

Set Implicit Arguments.

Section syntax.
  (** These are pre-terms, they are not guaranteed to be well typed **)
  Inductive expr_ast : Type :=
  | Var : string -> nat -> expr_ast.

  Inductive query_ast : Type :=
  | Bind  : string -> nat -> query_ast -> query_ast
  | Guard : expr_ast -> expr_ast -> query_ast -> query_ast
  | Ret : query_ast.


  (** This is the typing relation for raw terms **)
  Variable tbls : list row_type.

  Fixpoint find (s : string) (ls : list (string * row_type))
  : option row_type :=
    match ls with
    | nil => None
    | (s',v) :: ls => if s ?[ eq ] s' then Some v else find s ls
    end.

  (* Well-typed expressions *)
  Inductive WT_expr (vars : list (string * row_type)) : expr_ast -> dec_type -> Type :=
  | WT_Proj : forall t f T,
      match find t vars with
      | None => None
      | Some fs => nth_error fs f
      end = Some T ->
      WT_expr vars (Var t f) T.

  (* Well-typed queries *)
  Inductive WT_query (vars : list (string * row_type)) : query_ast -> Type :=
  | WT_Bind : forall v ti rt q',
      nth_error tbls ti = Some rt ->
      WT_query ((v,rt) :: vars) q' ->
      WT_query vars (Bind v ti q')
  | WT_Guard : forall l r q' T,
      WT_expr vars l T ->
      WT_expr vars r T ->
      WT_query vars q' ->
      WT_query vars (Guard l r q')
  | WT_Ret : WT_query vars Ret.


  (** Compiling well-typed queries to RecordTableaux **)

  Fixpoint weaken_expr vars rt T (e : expr vars T) {struct e}
  : expr (rt :: vars) T :=
    match e in @expr _ T return expr (rt :: vars) T with
    | Proj _ _ t f => Proj (Member.MN _ t) f
    end.

  Fixpoint weaken_filter vars rt
  : filter_type vars -> filter_type (rt :: vars) :=
    List.map (fun x =>
                let '(existT2 t l r) := x in
                @existT2 _ _ _ t
                         (@weaken_expr vars rt _ l)
                         (@weaken_expr vars rt _ r)).

  (* Convert natural number indicies to [member] "proofs" *)
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

  (* Convert string indicies to [member] "proofs" *)
  Fixpoint find_to_member (ls : list (string * row_type)) (s : string) val {struct ls}
    : find s ls = Some val -> Member.member val (List.map snd ls) :=
    match ls as ls
          return find s ls = Some val -> Member.member val (List.map snd ls)
    with
    | nil => fun pf : None = Some _ =>
               match pf in _ = t
                     return match t with
                            | Some _ => _
                            | None => unit
                            end
               with
               | eq_refl => tt
               end
    | (s',val') :: ls =>
      match s ?[ eq ] s' as X
            return (if X then Some val' else find s ls) = Some val ->
                   Member.member val (val' :: List.map snd ls)
      with
      | true => fun pf =>
                  match pf in _ = x
                        return match x with
                               | None => Empty_set
                               | Some x => member x (val' :: List.map snd ls)
                               end with
                  | eq_refl => Member.MZ _ _
                  end
      | false => fun pf => Member.MN _ (find_to_member ls s pf)
      end
    end.

  (* Compile expressions *)
  Fixpoint compile_e (vars : list (string * row_type)) T (q : expr_ast)
           (wt : WT_expr vars q T) {struct wt} : expr (List.map snd vars) T :=
    match wt with
    | WT_Proj v f T pf =>
      match find v vars as X return match X with
                                         | Some fs => nth_error fs f
                                         | None => None
                                         end = Some T ->
                                         find v vars = X ->
                                         expr (List.map snd vars) T
      with
      | None => fun pf =>
                  match pf in _ = t
                        return match t with
                               | None => unit
                               | Some _ => _ -> expr (List.map snd vars) T
                               end
                  with
                  | eq_refl => tt
                  end
      | Some X => fun pf_f pf_v =>
                    @Proj _ T _ (find_to_member _ _ pf_v) (to_member _ _ pf_f)
      end pf eq_refl
    end.

  (* Compile queries *)
  Fixpoint compile_q' (vars : list (string * row_type)) (q : query_ast)
           (bs : binds_type tbls (List.map snd vars))
           (fs : filter_type (List.map snd vars))
           (wt : WT_query vars q)  : tableaux tbls :=
    match wt with
    | WT_Ret => {| types := List.map snd vars ; binds := bs ; filter := fs |}
    | @WT_Bind x ti t_t q' pf_eq pf_wt =>
      @compile_q' ((x,t_t) :: vars) q' (Hcons (to_member _ _ pf_eq) bs)
                  (@weaken_filter _ _ fs) pf_wt
    | @WT_Guard l r q' T wt_l wt_r wt_q =>
      @compile_q' vars q' bs
                  (@existT2 _ _ _ T (compile_e wt_l) (compile_e wt_r) :: fs)
                  wt_q
    end.

  (* The top-level compiler for raw terms into tableaux *)
  Definition compile_q q wt : tableaux tbls :=
    Eval unfold compile_q' in
      @compile_q' nil q Hnil nil wt.

  Arguments compile_q _ {_}.

End syntax.

(** Type inference **)
(* Trigger type-class resolution to do type checking *)
Existing Class WT_query.
(* Type check/inference expressions *)
Ltac type_check_e e :=
  match e with
  | Var ?t ?f => eapply WT_Proj; [ simpl nth_error ; reflexivity ]
  end.
(* Type check/inference queries *)
Ltac type_check_q t :=
  match t with
  | Ret => apply WT_Ret
  | Bind ?l ?r ?q' =>
    eapply WT_Bind; [ simpl nth_error ; reflexivity | type_check_q q' ]
  | Guard ?l ?r ?q' =>
    eapply WT_Guard; [ type_check_e l | type_check_e r | instantiate ; type_check_q q' ]
  end.
(* Invoke the type checker to solve [WT_query _ _ _] instances *)
Hint Extern 0 (WT_query _ _ ?q) => (type_check_q q) : typeclass_instances.

(** Notation **)
Delimit Scope query_scope with query.
Notation "'assert' e1 == e2  ;; q" := (@Guard e1 e2 q%query)
   (at level 20, e1 at next level, e2 at next level, q at level 19) : query_scope.
Notation "x <- e2  ;; q" := (@Bind x e2 q%query)
   (at level 20, q at level 19) : query_scope.

(* Invoke the compiler when you see this syntax.
 * NOTE: In Coq 8.5 we can reduce [compile_q] here
 *)
Notation "'QUERY' tbls 'USING' q" :=
  (@compile_q tbls q%query _) (at level 20, only parsing).

(** Example **)
Let tbls_demo :=
  SemanticQuery.Tables.Demo.tt_names ::
  SemanticQuery.Tables.Demo.tt_manager ::
  nil.

Goal True.
  pose (QUERY tbls_demo USING ("x" <- 0 ;;
                               assert (Var "x" 0) == (Var "x" 0) ;;
                               Ret)).
  unfold compile_q in t. simpl in t.
  exact I.
Defined.
