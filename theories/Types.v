Require Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ExtLib.Data.Member.

Set Implicit Arguments.
Set Strict Implicit.

Let UU : Type := Type.
Let U : UU := Type.

Inductive type :=
| Nat
| Bool
| String
| Tuple : list type -> type.

Section mp.
  Variable f : type -> U.
  Fixpoint tuple (ls : list type) : U :=
    match ls with
    | nil => unit
    | List.cons l ls => (f l) * (tuple ls)
    end%type.

  Fixpoint tuple_get {ls} {t} (m : member t ls) : tuple ls -> f t :=
    match m in member _ ls return tuple ls -> f t with
    | MZ _ => fst
    | MN _ _ m' =>
      let get := tuple_get m' in
      fun rows => get (snd rows)
    end.
End mp.

Fixpoint typeD (t : type) : U :=
  match t return U with
  | Nat => nat
  | Bool => bool
  | String => String.string
  | Tuple ls => tuple typeD ls
  end.

Fixpoint type_dec (a b : type) : {a = b} + {a <> b}.
refine
  match a as a , b as b return {a = b} + {a <> b} with
  | Nat , Nat => left eq_refl
  | Bool , Bool => left eq_refl
  | String , String => left eq_refl
  | Tuple a , Tuple b =>
    match List.list_eq_dec type_dec a b with
    | left pf => left (f_equal _ pf)
    | right pf => right _
    end
  | _ , _ => right _
  end; congruence.
Defined.

Definition bool_eq_dec (a b : bool) : {a = b} + {a <> b}.
decide equality.
Defined.

Definition unit_eq_dec (a b : unit) : {a = b} + {a <> b}.
decide equality.
Defined.


Definition prod_eq_dec {T U}
            (Teq : forall a b : T, {a = b} + {a <> b})
            (Ueq : forall a b : U, {a = b} + {a <> b})
            (a b : T * U)
: {a = b} + {a <> b}.
refine
  match a as a , b as b return {a = b} + {a <> b} with
  | (l1,l2) , (r1,r2) =>
    match Teq l1 r1 , Ueq l2 r2 with
    | left _ , left _ => left _
    | _ , _ => right _
    end
  end; subst; congruence.
Defined.

Fixpoint val_dec {t : type} {struct t}
: forall (l r : typeD t), {l = r} + {l <> r} :=
  match t as t return forall (l r : typeD t), {l = r} + {l <> r} with
  | Nat => NPeano.Nat.eq_dec
  | Bool => bool_eq_dec
  | String => String.string_dec
  | Tuple ls =>
    (fix eq_dec ls : forall (l r : tuple typeD ls), {l = r} + {l <> r} :=
       match ls with
       | nil => unit_eq_dec
       | l :: ls =>
         let tD := @val_dec l in
         let lD := @eq_dec ls in
         @prod_eq_dec _ _ tD lD
       end) ls
  end.
