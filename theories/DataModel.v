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
; Mmap : forall {T U} (f : T -> U) (x : M T), M U :=
    fun _ _ f x => Mbind x (fun x => Mret (f x))
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
; Mimpl_Mzero : forall {T} (c : M T),
    Mimpl Mzero c

; Mbind_perm : forall {T U V} (m1 : M T) (m2 : M U) (f : T -> U -> M V),
    Meq (Mbind m1 (fun x => Mbind m2 (f x)))
        (Mbind m2 (fun y => Mbind m1 (fun x => f x y)))
; Mbind_dup : forall {T U} (m : M T) (f : T * T -> M U),
    Mimpl (Mbind m (fun x => f (x,x)))
          (Mbind m (fun x => Mbind m (fun y => f (x,y))))
  (** TODO: This is sub-optimal, it would be much better to extend
   ** the simple set of definitions with the axioms that are necessary
   ** to prove this
   **)
; _chaseable : forall (S S' T U : Type) (P : M S) (C : S -> bool)
     (E : S -> T) (F : M S') (Gf : S' -> bool) (B : M U)
     (Gb : S' -> U -> bool),
   Meq (Mbind F (fun x : S' => Mguard (Gf x) (Mret x)))
     (Mbind (Mbind F (fun x : S' => Mbind B (fun y : U => Mret (x, y))))
        (fun x : S' * U =>
         Mguard (Gf (fst x) && Gb (fst x) (snd x)) (Mret (fst x)))) ->
   forall h : S -> S',
   Mimpl (Mmap h P) F ->
   (forall x : S, C x = true -> Gf (h x) = true) ->
   Meq (Mbind P (fun x : S => Mguard (C x) (Mret (E x))))
     (Mbind (Mbind P (fun x : S => Mbind B (fun y : U => Mret (x, y))))
        (fun x : S * U =>
         Mguard (C (fst x) && Gb (h (fst x)) (snd x)) (Mret (E (fst x)))))
}.

Global Existing Instance Reflexive_Mimpl.
Global Existing Instance Transitive_Mimpl.
Global Existing Instance Proper_Mbind_impl.
Global Existing Instance Proper_Mret_impl.

Global Instance Reflexive_pointwise {A B : Type} (R : B -> B -> Prop) (ReflR : Reflexive R)
  : Reflexive (pointwise_relation A R).
Proof.
  clear - ReflR. red. red. intros. reflexivity.
Qed.


Section extras.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Definition Mdprod {T U : Type} (x : M T) (y : T -> M U) : M (T * U) :=
    Mbind x (fun x => Mbind (y x) (fun y => Mret (x,y))).

  Definition Mprod {T U : Type} (x : M T) (y : M U) : M (T * U) :=
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

  Theorem chaseable : forall (S S' T U : Type) (P : M S) (C : S -> bool)
     (E : S -> T) (F : M S') (Gf : S' -> bool) (B : M U)
     (Gb : S' -> U -> bool)
     (edc : embedded_dependency F Gf B Gb)
     (h : S -> S'),
      Mimpl (Mmap h P) F ->
      (forall x : S, C x = true -> Gf (h x) = true) ->
      Meq (query P C E)
          (query (Mprod P B)
                 (fun xy => C (fst xy) && Gb (h (fst xy)) (snd xy))
                 (fun xy => E (fst xy))).
  Proof.
    unfold embedded_dependency, query.
    eapply _chaseable.
  Qed.

  Global Instance Reflexive_Meq : forall {T}, Reflexive (@Meq M _ T).
  Proof. red. red. split; reflexivity. Qed.
  Global Instance Symmetry_Meq : forall {T}, Symmetric (@Meq M _ T).
  Proof. red. unfold Meq; tauto. Qed.
  Global Instance Transitive_Meq : forall {T}, Transitive (@Meq M _ T).
  Proof. red. unfold Meq. intros. destruct H; destruct H0; split; etransitivity; eauto. Qed.

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

  Lemma Mmap_Mprod_L : forall {T U V : Type} (m1 : M T) (m2 : M U) (f : T -> V),
      Mimpl (Mmap (fun x => f (fst x)) (Mprod m1 m2)) (Mmap f m1).
  Proof.
    unfold Mmap, Mprod. intros.
    repeat setoid_rewrite Mbind_assoc.
    repeat setoid_rewrite Mbind_Mret. simpl.
    eapply Proper_Mbind_impl. reflexivity.
    red. intros.
    eapply Mbind_ignore.
  Qed.

  Lemma Mmap_Mprod_R : forall {T U V : Type} (m1 : M T) (m2 : M U) (f : U -> V),
      Mimpl (Mmap (fun x => f (snd x)) (Mprod m1 m2)) (Mmap f m2).
  Proof.
    unfold Mmap, Mprod. intros.
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

  Global Instance Proper_Mprod_impl {T U}
  : Proper (Mimpl ==> Mimpl ==> Mimpl) (@Mprod T U).
  Proof.
    unfold Mprod. do 3 red.
    intros.
    eapply Proper_Mbind_impl. eassumption.
    red; intros.
    eapply Proper_Mbind_impl. eassumption.
    red. reflexivity.
  Qed.

  Global Instance Proper_Mprod_eq {T U}
  : Proper (Meq ==> Meq ==> Meq) (@Mprod T U).
  Proof.
    unfold Mprod. do 3 red.
    intros.
    eapply Proper_Mbind_eq. eassumption.
    red; intros.
    eapply Proper_Mbind_eq. eassumption.
    red. reflexivity.
  Qed.

  Lemma Mprod_Mmap_L : forall {T U U' : Type} (m1 : M T) (m2 : M U) (f : U -> U'),
      Meq (Mprod m1 (Mmap f m2))
          (Mmap (fun xy => (fst xy, f (snd xy))) (Mprod m1 m2)).
  Proof.
    unfold Mprod, Mmap; intros.
    repeat setoid_rewrite Mbind_assoc.
    repeat setoid_rewrite Mbind_Mret. simpl. reflexivity.
  Qed.

  Lemma Mprod_Mmap_R : forall {T T' U : Type} (m1 : M T) (m2 : M U) (f : T -> T'),
      Meq (Mprod (Mmap f m1) m2)
          (Mmap (fun xy => (f (fst xy), snd xy)) (Mprod m1 m2)).
  Proof.
    unfold Mprod, Mmap; intros.
    repeat setoid_rewrite Mbind_assoc.
    repeat setoid_rewrite Mbind_Mret. simpl. reflexivity.
  Qed.

  Global Instance Proper_Mmap_eq {T T'}
  : Proper ((eq ==> eq) ==> Meq ==> Meq) (@Mmap _ _ T T').
  Proof.
    unfold Mmap; do 3 red. intros.
    eapply Proper_Mbind_eq; eauto.
    red. intros.
    eapply Proper_Mret_eq. eapply H. reflexivity.
  Qed.

  Theorem Mmap_Mbind : forall {A B C} (f : A -> B) (c : M A) (k : _ -> M C),
      Meq (Mbind (Mmap f c) k)
          (Mbind c (fun x => k (f x))).
  Proof. clear.
         intros. unfold Mmap.
         rewrite Mbind_assoc. setoid_rewrite Mbind_Mret. reflexivity.
  Qed.

  Global Instance Proper_Mguard_impl {A}
  : Proper (Bool.leb ==> Mimpl ==> Mimpl) (@Mguard M _ A).
  Proof.
    do 3 red. intros.
    red in H. destruct x; subst; simpl; auto.
    eapply Mimpl_Mzero.
  Qed.

  Lemma Mbind_then_Mzero : forall {T U} (m : M T),
      Meq (@Mzero M _ U) (Mbind m (fun _ => Mzero)).
  Proof.
    split.
    { eapply Mimpl_Mzero. }
    { rewrite Mbind_ignore. reflexivity. }
  Qed.

  Lemma Mbind_Mguard : forall {T U} (m : M T) p (k : T -> M U),
      Meq (Mbind (Mguard p m) k)
          (Mguard p (Mbind m k)).
  Proof.
    intros. unfold Mguard. destruct p; simpl; try reflexivity.
    rewrite Mbind_Mzero. reflexivity.
  Qed.

  Lemma Mguard_and : forall {T} p q (m : M T),
      Meq (Mguard (p && q) m)
          (Mguard p (Mguard q m)).
  Proof. destruct p; destruct q; reflexivity. Qed.

  Lemma Mguard_perm : forall {T} p q (m : M T),
      Meq (Mguard q (Mguard p m))
          (Mguard p (Mguard q m)).
  Proof. destruct p; destruct q; reflexivity. Qed.

  Global Instance Proper_Mguard_eq {A : Type}
    :  Proper (eq ==> Meq ==> Meq) (@Mguard M _ A).
  Proof.
    do 3 red. unfold Mguard. intros; subst.
    destruct y; auto. reflexivity.
  Qed.

  Lemma Mguard_impl : forall {T} (a b : bool) (m1 m2 : M T),
      Bool.leb a b ->
      (a = true -> Mimpl m1 m2) ->
      Mimpl (Mguard a m1)
            (Mguard b m2).
  Proof.
    intros. red in H.
    destruct a; simpl.
    { subst. apply H0. reflexivity. }
    { apply Mimpl_Mzero. }
  Qed.

End extras.

Arguments Mmap {M DM T U} _ _ : rename.
Arguments Mdprod {M DM T U} _ _.
Arguments Mprod {M DM T U} _ _.
Arguments query {M DM S T} _ _ _.
Arguments embedded_dependency {M DM S S'} _ _ _ _.

Ltac rw_M :=
  repeat first [ setoid_rewrite Mbind_assoc
               | setoid_rewrite Mbind_Mret
               | setoid_rewrite Mret_Mbind
               | setoid_rewrite Mbind_Mzero
               | setoid_rewrite Mmap_Mbind
               | setoid_rewrite Mbind_Mguard
               | setoid_rewrite <- Mbind_then_Mzero ].
