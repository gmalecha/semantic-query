Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.


Class DataModel (M : Type -> Type) : Type :=
{ Mret  : forall {T}, T -> M T
; Mbind : forall {T U}, M T -> (T -> M U) -> M U
; Mzero : forall {T}, M T
; Mguard : forall {T}, bool -> M T -> M T
; Mimpl : forall {T}, M T -> M T -> Prop
; makeM : forall {T}, list T -> M T
; Meq : forall {T} (a b : M T), Prop  :=
    fun _ a b => Mimpl a b /\ Mimpl b a
  (** theorems **)
; Reflexive_Mimpl : forall {A}, Reflexive (@Mimpl A)
; Transitive_Mimpl : forall {A}, Transitive (@Mimpl A)
; Proper_Mbind : forall {A B},
    Proper (Meq ==> (pointwise_relation _ Meq) ==> Meq) (@Mbind A B)
; Proper_Mguard : forall {A},
    Proper (eq ==> Meq ==> Meq) (@Mguard A)
; Proper_Mret : forall {A},
    Proper (eq ==> Meq) (@Mret A)

; Mbind_assoc : forall {A B C} (c1 : M A) (c2 : A -> M B) (c3 : B -> M C),
    Meq (Mbind (Mbind c1 c2) c3)
        (Mbind c1 (fun x => Mbind (c2 x) c3))
; Mbind_Mret : forall {A B} (x : A) (c : A -> M B),
    Meq (Mbind (Mret x) c) (c x)
; Mret_Mbind : forall {A} (c : M A),
    Meq (Mbind c Mret) c
; Mbind_Mzero : forall {A B : Type} (x : A -> M B), Meq (Mbind Mzero x) Mzero
}.

Global Existing Instance Reflexive_Mimpl.
Global Existing Instance Transitive_Mimpl.
Global Existing Instance Proper_Mbind.
Global Existing Instance Proper_Mguard.
Global Existing Instance Proper_Mret.

Section extras.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Definition Mmap {T U} (f : T -> U) (x : M T) : M U :=
    Mbind x (fun x => Mret (f x)).

  Definition Mdplus {T U : Type} (x : M T) (y : T -> M U) : M (T * U) :=
    Mbind x (fun x => Mbind (y x) (fun y => Mret (x,y))).

  Definition Mplus {T U : Type} (x : M T) (y : M U) : M (T * U) :=
    Mbind x (fun x => Mbind y (fun y => Mret (x,y))).

  Definition query {S T: Type}
             (P : M S)
             (C : S -> bool)
             (E : S -> T) : M T :=
    Mbind P (fun x => Mguard (C x) (Mret (E x))).

  Definition embedded_dependency {S S'}
             (F : M S) (Gf : S -> bool)
             (B : M S') (Gb : S -> S' -> bool) :=
    Meq (query F Gf (fun x => x))
          (query (Mbind F (fun x => Mbind B (fun y => Mret (x,y))))
                 (fun ab => Gf (fst ab) && Gb (fst ab) (snd ab))
                 (fun x => fst x)).

  Global Instance Reflexive_Meq : forall {T}, Reflexive (@Meq M _ T).
  Proof. Admitted.
  Global Instance Symmetry_Meq : forall {T}, Symmetric (@Meq M _ T).
  Proof. Admitted.
  Global Instance Transitive_Meq : forall {T}, Transitive (@Meq M _ T).
  Proof. Admitted.

End extras.

Arguments Mmap {M DM T U} _ _.
Arguments Mdplus {M DM T U} _ _.
Arguments Mplus {M DM T U} _ _.
Arguments query {M DM S T} _ _ _.
Arguments embedded_dependency {M DM S S'} _ _ _ _.

(*
Module ListModel <: Model with Definition M := list.

  Definition M (T : Type) : Type := list T.
  Definition Mconcat {t} (I : M (M t)) : M t :=
    List.flat_map (fun x => x) I.
  Definition Mmap {a b} (f : a -> b) (X : M a) : M b :=
    List.map f X.
  Definition Mbind {T U : Type} (c1 : M T) (c2 : T -> M U) : M U :=
    Mconcat (Mmap c2 c1).
  Definition Mzero {t} : M t := nil.
  Definition Mguard {T} (P : bool) (ok : M T) : M T :=
    if P then ok else Mzero.
  Definition Mret : forall {T}, T -> M T :=
    fun _ x => @cons _ x nil.

  Definition makeM {T} (x : list T) : M T := x.

  Definition Mimpl {T} (a b : list T) : Prop :=
    forall x, List.In x a -> List.In x b.

  Definition Meq {T} (a b : list T) : Prop :=
    Mimpl a b /\ Mimpl b a.

  Theorem Mmap_Mbind : forall {A B} (f : A -> B) (c : M A),
      Meq (Mmap f c) (Mbind c (fun x => Mret (f x))).
  Proof. Admitted.

  Theorem Mbind_assoc : forall {A B C} (c1 : M A) (c2 : A -> M B) (c3 : B -> M C),
      Meq (Mbind (Mbind c1 c2) c3)
          (Mbind c1 (fun x => Mbind (c2 x) c3)).
  Proof. Admitted.

  Theorem Mbind_Mret : forall {A B} (x : A) (c : A -> M B),
      Meq (Mbind (Mret x) c) (c x).
  Proof. Admitted.

  Theorem Mret_Mbind : forall {A} (c : M A),
      Meq (Mbind c Mret) c.
  Proof. Admitted.

  Definition RelAnd {A} (r P : A -> A -> Prop) : A -> A -> Prop :=
    fun x y => r x y /\ P x y.

  Instance Proper_Mbind : forall {A B},
      Proper (Meq ==> (pointwise_relation _ Meq) ==> Meq) (@Mbind A B).
  Proof. Admitted.

  Instance Proper_Mguard : forall {A},
      Proper (eq ==> Meq ==> Meq) (@Mguard A).
  Proof. Admitted.

  Definition query {S T: Type}
             (P : M S)
             (C : S -> bool)
             (E : S -> T) : M T :=
    Mbind P (fun x => Mguard (C x) (Mret (E x))).

  Definition Mplus {T U} (a : M T) (b : M U) : M (T * U) :=
    (Mbind a (fun x => Mbind b (fun y => Mret (x,y)))).

  Instance Transitive_Meq : forall {T}, Transitive (@Meq T).
  Proof. Admitted.
  Instance Reflexive_Meq : forall {T}, Reflexive (@Meq T).
  Proof. Admitted.
  Instance Symmetry_Meq : forall {T}, Symmetric (@Meq T).
  Proof. Admitted.

  Instance Transitive_Mimpl : forall {T}, Transitive (@Mimpl T).
  Proof. Admitted.
  Instance Reflexive_Mimpl : forall {T}, Reflexive (@Mimpl T).
  Proof. Admitted.

  Lemma Mbind_Mimpl : forall {T V} (P : M T) (Q : M _) (k : _ -> M V),
      Mimpl P Q ->
      Meq (Mbind P k) (Mbind (Mplus P Q) (fun x => k (fst x))).
  Proof. Admitted.

  Lemma Mguard_Mmap : forall {A B C} (f : A -> B) (X : M A) (P : _ -> bool) (k : M C),
      Meq (Mbind X (fun x => Mguard (P (f x)) k))
          (Mbind (Mmap f X) (fun x => Mguard (P x) k)).
  Proof. Admitted.

  Lemma Mguard_andb : forall {A} (P Q : bool) (k : M A),
      Meq (Mguard (P && Q) k) (Mguard P (Mguard Q k)).
  Proof. Admitted.
End ListModel.
*)