Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Data.HList.
Require Import ExtLib.Data.Member.
(* Only for examples *)
Require Import ExtLib.Data.Nat.
Require Import ExtLib.Data.String.

Set Implicit Arguments.
Set Strict Implicit.

Record dec_type :=
{ type : Type
; eq_dec : forall a b : type, {a = b} + {a <> b}
}.

Definition dec_type_from_EqDec (T : Type)
           {ED : RelDec (@eq T)} {EDO : RelDec_Correct ED}
: dec_type :=
{| type := T
 ; eq_dec := fun a b : T =>
               match a ?[ eq ] b as t return a ?[ eq ] b = t -> {a = b} + {a <> b} with
               | true => fun pf =>
                           left (proj1 (@rel_dec_correct _ _ _ EDO a b) pf)
               | false => fun pf =>
                            right (proj2 (@neg_rel_dec_correct _ _ _ EDO a b) pf)
               end eq_refl
 |}.

Arguments dec_type_from_EqDec _ {_ _}.

Definition row_type : Type := list dec_type.

Definition row (r : row_type) : Type := hlist type r.

Definition table (r : row_type) := list (row r).

Section example.
  Definition nat_type : dec_type := dec_type_from_EqDec nat.
  Definition string_type : dec_type := dec_type_from_EqDec string.

  Definition tt_names : row_type := nat_type :: string_type :: nil.
  Definition tt_manager : row_type := nat_type :: nat_type :: nil.

  Fixpoint tuple (r : row_type) : Type :=
    match r with
    | nil => unit
    | r :: rs => type r * tuple rs
    end%type.

  Fixpoint Row (r : row_type) : tuple r -> hlist type r :=
    match r as r return tuple r -> hlist type r with
    | nil => fun _ => Hnil
    | r :: rs => fun v => Hcons (fst v) (Row rs (snd v))
    end.

  Definition tbl_names : table tt_names :=
    (Row tt_names (0, ("Ryan"%string, tt))) ::
    (Row tt_names (1, ("Gregory"%string, tt))) ::
    nil.

  Definition tbl_manager : table tt_manager :=
    (Row tt_manager (1, (0, tt))) :: nil.
End example.

Module shallow.

  Definition tableaux (T : Type) : Type := list T.
  Fixpoint tget {T U} (t : tableaux T) (k : T -> tableaux U) : tableaux U :=
    match t with
    | nil => nil
    | t :: ts => k t ++ tget ts k
    end.
  Definition tret {T} (v : T) : tableaux T := v :: nil.
  Definition tguard {T} (g : bool) (t : tableaux T) : tableaux T :=
    match g with
    | true => t
    | false => nil
    end.

  Definition trial :=
    tget tbl_names (fun n =>
    tget tbl_manager (fun m =>
    tguard (hlist_hd n ?[ eq ] hlist_hd  m) (tret (n,m)))).

End shallow.



Inductive expr (T : dec_type) (ls : list row_type) : Type :=
| Proj : forall r, member r ls -> member T r -> expr T ls.

Module record.
  Section with_tables.
    Variable tbls : list row_type.

    Record tableaux  :=
    { types : list row_type
    ; binds : hlist (fun x => member x tbls) types
    ; filter : list { T : dec_type & expr T types & expr T types }
    }.

    Fixpoint join {T U V : Type} (f : T -> U -> V) (ts : list T) (us : list U) : list V :=
      match ts , us with
      | nil , _ => nil
      | _ , nil => nil
      | t :: ts , u :: us => f t u :: join f ts us
      end.

    Fixpoint bindD {ts : list row_type} (names : hlist (fun x => member x tbls) ts)
      : hlist table tbls -> list (hlist row ts) :=
      match names in hlist _ ts return hlist table tbls -> list (hlist row ts) with
      | Hnil => fun _ => Hnil :: nil
      | Hcons _ _ n names => fun tbls =>
                               join (fun a b => Hcons a b) (hlist_get n tbls) (bindD names tbls)
      end.

    Fixpoint exprD {T} {ls} (e : expr T ls) {struct e} : hlist row ls -> type T :=
      match e in expr _ _ return hlist row ls -> type T with
      | Proj _ v c => fun vars => hlist_get c (hlist_get v vars)
      end.

    Fixpoint filterD {ts : list row_type} (f : list { T : dec_type & expr T ts & expr T ts })
    : hlist row ts -> bool :=
      match f with
      | nil => fun _ => true
      | (existT2 t f1 f2) :: fs => fun rows =>
                                     match t.(eq_dec) (exprD f1 rows) (exprD f2 rows) with
                                     | left _ => filterD fs rows
                                     | right _ => false
                                     end
      end.

    (** The return type here is a bit odd. I'm just gluing the rows together as an hlist.
     ** Queries seem more natural.
     **)
    Definition tableauxD (t : tableaux) : hlist table tbls -> list (hlist row t.(types)) :=
      let all := bindD t.(binds) in
      let keep := filterD t.(filter) in
      fun tbls => List.filter keep (all tbls).

    Fixpoint subst_expr {vars vars'} (f :forall {x}, member x vars -> member x vars') (T : _)
             (e : expr T vars) {struct e} : expr T vars' :=
      match e with
      | Proj _ v c => Proj (f v) c
      end.
    Arguments subst_expr {_ _} _ _ _.

    Definition subst_test {vars vars'} (f : forall {T}, expr T vars -> expr T vars')
               (x : { T : dec_type & expr T vars & expr T vars })
      : { T : dec_type & expr T vars' & expr T vars' } :=
      match x with
      | existT2 T x1 x2 =>
        @existT2 _ _ _ T (f x1) (f x2)
      end.

    (*
    A homomorphism h : q1 -> q2 maps the for-bound variables of q1 to the for-bound variables of q2 such that
    1) x in X in q1 implies h(x) in X in q2
    2) q1 |- p = q in q1 implies q2 |- h(p) = h(q)
    3) return E in q1 and return E' in q2 implies q2 |- h(E) = E'
    *)
    Definition homomorphism (q1 q2 : tableaux) (pf : q1.(types) = q2.(types)) : Type :=
      { h : forall x, member x q1.(types) -> member x q2.(types) (** 1 **)
      & forall x, filterD (map (subst_test (subst_expr h)) q1.(filter)) x = filterD q2.(filter) x (** 2? **)
      }.
    (** TODO(gmalecha): I'm not entirely sure what 2) means.
     ** The basic definition seems to be a statement about substitutions.
     ** Is it the case that you can not change the projection functions?
     **)
    (** TODO(gmalecha): 3) seems meaningless for tableaux. This seems to suggest that a homomorphism only makes
     ** sense for queries?
     **)
  End with_tables.

End record.

Module inductive.
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
End inductive.