Require Import Coq.Lists.List.
Require Import SemanticQuery.Types.
Require Import SemanticQuery.Expr.
Require Import SemanticQuery.RecordTableaux.

Set Implicit Arguments.
Set Strict Implicit.

Section find_assumption.
  Context {vs : list type}.
  Variable goal : expr vs Bool.

  Fixpoint find_assumption (ls : list (expr vs Bool)) {struct ls}
  : option (forall vs : Env vs, filterD ls vs = true ->
                                exprD goal vs = true) :=
    match ls as ls
          return option (forall vs : Env vs, filterD ls vs = true ->
                                             exprD goal vs = true)
    with
    | nil => None
    | l :: ls =>
      match expr_eq goal l with
      | left pf =>
        Some (fun vs' =>
                match pf in _ = t
                      return filterD (t :: ls) vs' = true -> _
                with
                | eq_refl =>
                  match exprD goal vs' as X
                        return (if X then filterD ls vs' else false) = true ->
                               X = true
                  with
                  | true => fun _ => eq_refl
                  | false => fun pf => pf
                  end
                end)
      | right _ =>
        match find_assumption ls with
        | None => None
        | Some pf =>
          Some (fun vs' pf_xs =>
                  let pf_rest :=
                      match filterD ls vs' as X
                            return (if exprD l vs' then X else false) = true ->
                                   X = true
                      with
                      | true => fun _ => eq_refl
                      | false => match exprD l vs' as X
                                       return (if X then false else false) = true ->
                                              false = true
                                 with
                                 | true => fun x => x
                                 | false => fun x => x
                                 end
                      end pf_xs
                  in pf vs' pf_rest)
        end
      end
    end.

  Definition check_reflexive
  : option (forall vs : Env vs, exprD goal vs = true) :=
    match goal as goal in expr _ T
          return option (match T as T return expr vs T -> Type with
                         | Bool => fun goal =>
                                     (forall vs0 : Env vs, exprD goal vs0 = true)
                         | _ => fun _ => False
                         end goal)
    with
    | Eq T l r =>
      match expr_eq l r with
      | left pf => Some (fun vs => match pf in _ = T
                                         return exprD (Eq l T) vs = true
                                   with
                                   | eq_refl =>
                                     match val_dec (exprD l vs) (exprD l vs) as X
                                           return (if X then true else false) = true
                                     with
                                     | left _ => eq_refl
                                     | right pf => match pf eq_refl with end
                                     end
                                   end)
      | right _ => None
      end
    | _ => None
    end.

End find_assumption.
