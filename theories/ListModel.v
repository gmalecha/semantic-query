Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Shallow.

Set Implicit Arguments.
Set Strict Implicit.

Definition FSet (T : Type) : Type := list T.

Definition FSet_empty {T} : FSet T := nil.
Definition FSet_singleton {T} (v : T) : FSet T := v :: nil.
Fixpoint FSet_cross {T U : Type} (ts : FSet T) (f : T -> FSet U)
: FSet U :=
  match ts with
  | nil => nil
  | t :: ts => f t ++ FSet_cross ts f
  end.

Definition FSet_subset {T} (a b : FSet T) : Prop :=
  forall x, List.In x a -> List.In x b.

Instance DataModel_FSet : DataModel FSet :=
{ Mret := @FSet_singleton
; Mzero := @FSet_empty
; Mbind := @FSet_cross
; Mimpl := @FSet_subset
; makeM := fun _ x => x
}.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
{ intros. red. intros.
  induction x.
  { inversion H. }
  { simpl in H.
    eapply List.in_app_iff in H. destruct H; auto. } }
admit.
admit.
admit.
Defined.

(*
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