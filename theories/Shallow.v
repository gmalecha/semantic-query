Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.


Class DataModel (M : Type -> Type) : Type :=
{ Mret  : forall {T}, T -> M T
; Mbind : forall {T U}, M T -> (T -> M U) -> M U
; Mzero : forall {T}, M T
; Mimpl : forall {T}, M T -> M T -> Prop
; makeM : forall {T}, list T -> M T
; Meq : forall {T} (a b : M T), Prop  :=
    fun _ a b => Mimpl a b /\ Mimpl b a
; Mguard : forall {T}, bool -> M T -> M T :=
    fun _ b x => if b then x else Mzero
  (** theorems **)
; Reflexive_Mimpl : forall {A}, Reflexive (@Mimpl A)
; Transitive_Mimpl : forall {A}, Transitive (@Mimpl A)

; Proper_Mbind_impl : forall {A B},
    Proper (Mimpl ==> (pointwise_relation _ Mimpl) ==> Mimpl) (@Mbind A B)
; Proper_Mret_impl : forall {A},
    Proper (eq ==> Mimpl) (@Mret A)

; Mbind_assoc : forall {A B C} (c1 : M A) (c2 : A -> M B) (c3 : B -> M C),
    Meq (Mbind (Mbind c1 c2) c3)
        (Mbind c1 (fun x => Mbind (c2 x) c3))
; Mbind_Mret : forall {A B} (x : A) (c : A -> M B),
    Meq (Mbind (Mret x) c) (c x)
; Mret_Mbind : forall {A} (c : M A),
    Meq (Mbind c Mret) c
; Mbind_Mzero : forall {A B : Type} (x : A -> M B), Meq (Mbind Mzero x) Mzero
; Mbind_ignore : forall {T U} (x : M T) (y : M U),
              Mimpl (Mbind x (fun _ => y)) y
}.

Global Existing Instance Reflexive_Mimpl.
Global Existing Instance Transitive_Mimpl.
Global Existing Instance Proper_Mbind_impl.
Global Existing Instance Proper_Mret_impl.

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

  Global Instance Proper_Mguard : forall {A},
    Proper (eq ==> Meq ==> Meq) (@Mguard M _ A).
  Proof.
    unfold Mguard. do 3 red.
    intros. subst. destruct y; auto. reflexivity.
  Qed.

  Global Instance Proper_Mbind_eq : forall {A B},
    Proper (Meq ==> (pointwise_relation _ Meq) ==> Meq) (@Mbind M _ A B).
  Proof.
    repeat red.
    intros.
    split; eapply Proper_Mbind_impl; try eapply H.
    { do 2 red in H0. red. intro. eapply H0. }
    { do 2 red in H0. red. intro. eapply H0. }
  Qed.

  Global Instance Proper_Mret_eq : forall {A},
    Proper (eq ==> Meq) (@Mret M _ A).
  Proof.
    repeat red.
    intros.
    split; eapply Proper_Mret_impl; try eapply H.
    auto.
  Qed.

  Lemma Mmap_compose : forall {T U V} (f : V -> T) (g : U -> V) (x : M U),
      Meq (Mmap f (Mmap g x)) (Mmap (fun x => f (g x)) x).
  Proof.
    unfold Mmap. intros.
    repeat setoid_rewrite Mbind_assoc.
    apply Proper_Mbind_eq; try reflexivity.
    red; intros.
    setoid_rewrite Mbind_Mret. reflexivity.
  Qed.

  Global Instance Proper_limpl_lequiv {T}
  : Proper (Meq ==> Meq ==> iff) (@Mimpl M _ T).
  Proof.
    unfold Meq. split; simpl in *.
    { intros. etransitivity.
      - destruct H. eassumption.
      - etransitivity. eassumption. intuition. }
    { intros. etransitivity.
      - destruct H. eassumption.
      - etransitivity. eassumption. intuition. }
  Qed.

  Lemma Mmap_Mplus_L : forall {T U V : Type} (m1 : M T) (m2 : M U) (f : T -> V),
      Mimpl (Mmap (fun x => f (fst x)) (Mplus m1 m2)) (Mmap f m1).
  Proof.
    unfold Mmap, Mplus. intros.
    repeat setoid_rewrite Mbind_assoc.
    repeat setoid_rewrite Mbind_Mret. simpl.
    eapply Proper_Mbind_impl. reflexivity.
    red. intros.
    eapply Mbind_ignore.
  Qed.

  Lemma Mmap_Mplus_R : forall {T U V : Type} (m1 : M T) (m2 : M U) (f : U -> V),
      Mimpl (Mmap (fun x => f (snd x)) (Mplus m1 m2)) (Mmap f m2).
  Proof.
    unfold Mmap, Mplus. intros.
    repeat setoid_rewrite Mbind_assoc.
    repeat setoid_rewrite Mbind_Mret. simpl.
    setoid_rewrite Mbind_ignore. reflexivity.
  Qed.

  Global Instance Proper_Mimpl_Mimpl {T}
  : Proper (Mimpl --> Mimpl ==> Basics.impl) (@Mimpl M _ T).
  Proof.
    do 4 red.
    { intros. etransitivity. eapply H.
      etransitivity. eassumption. intuition. }
  Qed.

  Lemma Mmap_id : forall {T} (m : M T), Meq (Mmap (fun x => x) m) m.
  Proof.
    unfold Mmap. intros.
    rewrite Mret_Mbind. reflexivity.
  Qed.

  Theorem Mmap_ignore : forall {T U : Type} (f : U) (m : M T),
      Mimpl (Mmap (fun _ => f) m)
            (Mret f).
  Proof.
    unfold Mmap. simpl. intros.
    rewrite Mbind_ignore. reflexivity.
  Qed.

  Global Instance Proper_Mplus_impl {T U}
  : Proper (Mimpl ==> Mimpl ==> Mimpl) (@Mplus T U).
  Proof.
    unfold Mplus. do 3 red.
    intros.
    eapply Proper_Mbind_impl. eassumption.
    red; intros.
    eapply Proper_Mbind_impl. eassumption.
    red. reflexivity.
  Qed.

  Global Instance Proper_Mplus_eq {T U}
  : Proper (Meq ==> Meq ==> Mimpl) (@Mplus T U).
  Proof.
    unfold Mplus. do 3 red.
    intros.
    eapply Proper_Mbind_eq. symmetry. eassumption.
    red; intros.
    eapply Proper_Mbind_eq. symmetry. eassumption.
    red. reflexivity.
  Qed.

  Lemma Mplus_Mmap_L : forall {T U U' : Type} (m1 : M T) (m2 : M U) (f : U -> U'),
      Meq (Mplus m1 (Mmap f m2))
          (Mmap (fun xy => (fst xy, f (snd xy))) (Mplus m1 m2)).
  Proof.
    unfold Mplus, Mmap; intros.
    repeat setoid_rewrite Mbind_assoc.
    repeat setoid_rewrite Mbind_Mret. simpl. reflexivity.
  Qed.

  Lemma Mplus_Mmap_R : forall {T T' U : Type} (m1 : M T) (m2 : M U) (f : T -> T'),
      Meq (Mplus (Mmap f m1) m2)
          (Mmap (fun xy => (f (fst xy), snd xy)) (Mplus m1 m2)).
  Proof.
    unfold Mplus, Mmap; intros.
    repeat setoid_rewrite Mbind_assoc.
    repeat setoid_rewrite Mbind_Mret. simpl. reflexivity.
  Qed.

  Global Instance Proper_Mmap_eq {T T'}
    : Proper ((eq ==> eq) ==> Meq ==> Meq) (@Mmap T T').
  Proof.
    unfold Mmap; do 3 red. intros.
    eapply Proper_Mbind_eq; eauto.
    red. intros.
    eapply Proper_Mret_eq. eapply H. reflexivity.
  Qed.

End extras.

Arguments Mmap {M DM T U} _ _.
Arguments Mdplus {M DM T U} _ _.
Arguments Mplus {M DM T U} _ _.
Arguments query {M DM S T} _ _ _.
Arguments embedded_dependency {M DM S S'} _ _ _ _.
