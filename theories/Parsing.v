Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.String.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.Tables.
Require Import SemanticQuery.RecordTableaux.

Set Implicit Arguments.

Section syntax.
  (** These are pre-terms, they are not guaranteed to be well typed **)
  Inductive expr_ast : Type :=
  | Var : string -> expr_ast
  | Proj : expr_ast -> nat -> expr_ast
  | Eq : expr_ast -> expr_ast -> expr_ast.

  Inductive query_ast : Type :=
  | Bind  : string -> nat -> query_ast -> query_ast
  | Guard : expr_ast -> expr_ast -> query_ast -> query_ast
  | Ret : query_ast.


  (** This is the typing relation for raw terms **)
  Variable scheme : list type.

  Fixpoint find {T} (s : string) (ls : list (string * T))
  : option T :=
    match ls with
    | nil => None
    | (s',v) :: ls => if s ?[ eq ] s' then Some v else find s ls
    end.

  (* Well-typed expressions *)
  Inductive WT_expr (vars : list (string * type)) : expr_ast -> type -> Type :=
  | WT_Var : forall t T,
      find t vars = Some T ->
      WT_expr vars (Var t) T
  | WT_Proj : forall e ts f T,
      WT_expr vars e (Tuple ts) ->
      nth_error ts f = Some T ->
      WT_expr vars (Proj e f) T.

  (* Well-typed queries *)
  Inductive WT_query (vars : list (string * type)) : query_ast -> Type :=
  | WT_Bind : forall v ti rt q',
      nth_error scheme ti = Some rt ->
      WT_query ((v,rt) :: vars) q' ->
      WT_query vars (Bind v ti q')
  | WT_Guard : forall l r q' T,
      WT_expr vars l T ->
      WT_expr vars r T ->
      WT_query vars q' ->
      WT_query vars (Guard l r q')
  | WT_Ret : WT_query vars Ret.


  (** Compiling well-typed queries to RecordTableaux **)



  (* Convert natural number indicies to [member] "proofs" *)
  Fixpoint to_member {T} (ls : list T) (n : nat) (t : T) {struct n}
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
  Fixpoint find_to_member {T} (ls : list (string * T)) (s : string) val {struct ls}
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
  Fixpoint compile_e (vars : list (string * type)) T (q : expr_ast)
           (wt : WT_expr vars q T) {struct wt} : expr (List.map snd vars) T :=
    match wt in WT_expr _ q T return expr (List.map snd vars) T with
    | WT_Var v T pf => match find v vars as X
                             return find v vars = X ->
                                    X = Some T ->
                                    expr (List.map snd vars) T
                       with
                       | None => fun _ pf =>
                                   match pf in _ = X return match X with
                                                            | None => unit
                                                            | Some _ => _
                                                            end
                                   with
                                   | eq_refl => tt
                                   end
                       | Some X => fun pf_v pf_t =>
                                     match pf_t in _ = X return match X with
                                                                | None => unit
                                                                | Some X => expr _ X
                                                                end with
                                     | eq_refl => Expr.Var (find_to_member vars v pf_v)
                                     end
                       end eq_refl pf
    | WT_Proj e ts f _ pf_wt pf =>
      Expr.Proj (compile_e pf_wt) (to_member _ _ pf)
    end.

  (* Compile queries *)
  Fixpoint compile_q' (vars : list (string * type)) (q : query_ast)
           (bs : binds_type scheme (List.map snd vars))
           (fs : filter_type (List.map snd vars))
           (wt : WT_query vars q)  : tableaux scheme :=
    match wt with
    | WT_Ret => {| types := List.map snd vars ; binds := bs ; filter := fs |}
    | @WT_Bind x ti t_t q' pf_eq pf_wt =>
      @compile_q' ((x,t_t) :: vars) q' (Hcons (to_member _ _ pf_eq) bs)
                  (@filter_weaken _ _ fs) pf_wt
    | @WT_Guard l r q' T wt_l wt_r wt_q =>
      @compile_q' vars q' bs
                  (Expr.Eq (compile_e wt_l) (compile_e wt_r) :: fs)
                  wt_q
    end.

  (* The top-level compiler for raw terms into tableaux *)
  Definition compile_q q wt : tableaux scheme :=
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
  | Var ?t => eapply WT_Var; [ simpl nth_error ; reflexivity ]
  | Proj ?t ?f => eapply WT_Proj; [ type_check_e t | simpl nth_error ; reflexivity ]
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
   (at level 20, q at next level) : query_scope.

(* Invoke the compiler when you see this syntax.
 * NOTE: In Coq 8.5 we can reduce [compile_q] here
 *)
Notation "'QUERY' scheme 'USING' q" :=
  (@compile_q scheme q%query _) (at level 20, only parsing).
