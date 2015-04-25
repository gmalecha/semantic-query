Require Import SemanticQuery.Tables.

Set Implicit Arguments.
Set Strict Implicit.

Inductive tableaux (tbls : list row_type) (res : list row_type) : list row_type -> Type :=
| Bind : forall r vars,
    member r tbls ->
    tableaux tbls res (r :: vars) ->
    tableaux tbls res vars
| Done : tableaux tbls res res.

Fixpoint tableauxD {tbls res vars} (t : tableaux tbls res vars)
  : hlist table tbls -> hlist table vars -> hlist table res :=
  match t in tableaux _ _ vars
        return hlist table tbls -> hlist table vars -> hlist table res
  with
  | Done => fun _ x => x
  | Bind r vars m t => fun tbls tbls_vars =>
                         tableauxD t tbls (Hcons (hlist_get m tbls) tbls_vars)
  end.