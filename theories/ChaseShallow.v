Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Shallow.

Definition Pred (T: Type) : Type := T -> Prop.

Global Instance DataModel_Pred : DataModel Pred.
refine
{| Mret := fun _ x y => x = y
; Mzero := fun _ _ => False
; Mguard := fun _ p x => if p then x else fun _ => False
; Mbind := fun _ _ c k x =>
             exists y, c y /\ k y x
; Mimpl := fun _ a b => forall x, a x -> b x
; makeM := fun _ ls x => List.In x ls
|}.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.
Defined.


(*
Definition M (T : Type) : Type := T -> Prop.
Definition Mconcat {t} (I : M (M t)) : M t :=
  fun j => exists J, I J /\ J j.
Definition Mmap {a b} (f : a -> b) (X : M a) : M b :=
  fun y => exists x, X x /\ (f x = y).
Definition Mbind {T U : Type} (c1 : M T) (c2 : T -> M U) : M U :=
  Mconcat (Mmap c2 c1).
Definition Mzero {t} : M t := fun _ => False.
Definition Mguard : forall {T}, bool -> M T -> M T :=
  fun _ p x => if p then x else Mzero.
Definition Mret : forall {T}, T -> M T :=

Definition Meq {T} : M T -> M T -> Prop := fun a b => forall x, a x <-> b x.
Definition Mimpl {T} : M T -> M T -> Prop := fun a b => forall x, a x -> b x.
Definition Mcomap {T U} : (U -> T) -> M T -> M U :=
  fun f P x => P (f x).

Theorem Mmap_Mbind : forall {A B} (f : A -> B) (c : M A),
    Meq (Mmap f c) (Mbind c (fun x => Mret (f x))).
Proof.
  compute. intros.
  split; intros;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : exists x, _ |- _ => destruct H
         | |- exists x, _ => eexists
         | |- _ /\ _ => split
         | |- _ => eassumption
         end.
  reflexivity.
  subst. assumption.
Qed.


Theorem Mbind_assoc : forall {A B C} (c1 : M A) (c2 : A -> M B) (c3 : B -> M C),
    Meq (Mbind (Mbind c1 c2) c3)
        (Mbind c1 (fun x => Mbind (c2 x) c3)).
Proof.
  compute. intros.
  split; intros;
  repeat first [ progress forward_reason
               | subst ]; repeat eexists; eauto.
Qed.

Theorem Mbind_Mret : forall {A B} (x : A) (c : A -> M B),
    Meq (Mbind (Mret x) c) (c x).
Proof.
  compute. intros.
  split; intros;
  repeat first [ progress forward_reason
               | subst ]; repeat eexists; eauto.
Qed.

Theorem Mret_Mbind : forall {A} (c : M A),
    Meq (Mbind c Mret) c.
Proof.
  compute. intros.
  split; intros;
  repeat first [ progress forward_reason
               | subst ]; repeat eexists; eauto.
Qed.


Definition RelAnd {A} (r P : A -> A -> Prop) : A -> A -> Prop :=
  fun x y => r x y /\ P x y.

Instance Proper_Mbind : forall {A B},
    Proper (Meq ==> (pointwise_relation _ Meq) ==> Meq) (@Mbind A B).
Proof.
  do 4 red; intros; unfold Mbind, Mmap, Mconcat.
  split; intros;
  repeat first [ progress forward_reason
               | subst ]; repeat eexists; eauto.
  { eapply H. eassumption. }
  { eapply H0. eauto. }
  { eapply H. eassumption. }
  { eapply H0. eauto. }
Qed.

Definition drespectful {A} (F : A -> Type) (r : A -> A -> Prop) (rF : forall x y, r x y -> F x -> F y -> Prop) : forall (x y : forall x, F x) , Prop :=
  fun f g => forall x y (pf : r x y), @rF _ _ pf (f x) (g y).

(*
Axiom Mbind_DProper : forall {A B} P,
    Proper ((RelAnd eq (fun x _ => P x) ==> Meq) ==> Meq) (@Mbind A B P).
*)

Instance Proper_Mguard : forall {A},
    Proper (eq ==> Meq ==> Meq) (@Mguard A).
Proof.
  do 4 red; intros; unfold Mguard.
  split; intros;
  repeat first [ progress forward_reason
               | subst ]; repeat eexists; eauto.
  { destruct y; eauto. eapply H0. eauto. }
  { destruct y; eauto. eapply H0. eauto. }
Qed.

Definition Mplus {T U} (a : M T) (b : M U) : M (T * U) :=
  (Mbind a (fun x => Mbind b (fun y => Mret (x,y)))).

(*Axiom tbl_movies : M (string * string). *)

Definition query {S T: Type}
           (P : M S)
           (C : S -> bool)
           (E : S -> T) : M T :=
  Mbind P (fun x => Mguard (C x) (Mret (E x))).

Definition embedded_dependency {S S'}
           (F : M S) (Gf : S -> bool)
           (B : M S') (Gb : S -> S' -> bool) :=
  Meq (query F Gf (fun x => x))
      (query (Mplus F B)
             (fun ab => Gf (fst ab) && Gb (fst ab) (snd ab))
             (fun x => fst x)).

Instance Transitive_Meq : forall {T}, Transitive (@Meq T).
Proof.
  unfold Meq. red. intros. etransitivity; eauto.
Qed.
Instance Reflexive_Meq : forall {T}, Reflexive (@Meq T).
Proof.
  unfold Meq; red; reflexivity.
Qed.
Instance Symmetry_Meq : forall {T}, Symmetric (@Meq T).
Proof.
  unfold Meq; red; intros. symmetry. eauto.
Qed.

Instance Transitive_Mimpl : forall {T}, Transitive (@Mimpl T).
Proof.
  unfold Mimpl; red; intros; eauto.
Qed.
Instance Reflexive_Mimpl : forall {T}, Reflexive (@Mimpl T).
Proof.
  unfold Mimpl; red; intros; eauto.
Qed.

Lemma Mbind_Mimpl : forall {T V} (P : M T) (Q : M _) (k : _ -> M V),
    Mimpl P Q ->
    Meq (Mbind P k) (Mbind (Mplus P Q) (fun x => k (fst x))).
Proof.
  intros.
  red. intros.
  unfold Mplus, Mbind, Mconcat, Mmap.
  apply exists_iff; intro.
  apply and_iff; try tauto.
  split.
  { intros. red in H. destruct H0 as [ ? [ ? ? ] ].
    specialize (H _ H0).
    subst.
    repeat first [ eexists | split | eassumption ]. }
  { intro.
    repeat match goal with
           | H : exists x, _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | |- _ => subst
           end.
    repeat first [ eexists | split | eassumption ].
    red in H2. subst. reflexivity. }
Qed.

Lemma Mguard_Mmap : forall {A B C} (f : A -> B) (X : M A) (P : _ -> bool) (k : M C),
    Meq (Mbind X (fun x => Mguard (P (f x)) k))
        (Mbind (Mmap f X) (fun x => Mguard (P x) k)).
Proof.
  intros. unfold Meq, Mbind, Mmap, Mconcat.
  intros.
  split; intros; repeat (forward_reason; subst); repeat eexists; eauto.
Qed.

Lemma Mguard_andb : forall {A} (P Q : bool) (k : M A),
    Meq (Mguard (P && Q) k) (Mguard P (Mguard Q k)).
Proof.
  intros.
  destruct P; destruct Q; simpl; reflexivity.
Qed.
*)

Section chase.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

Theorem chase_sound_general {S S' T U}
(* q  *) (P : M S) (C : S -> bool) (E : S -> T)
(* ed *) (F : M S') (Gf : S' -> bool) (B : M U) (Gb : S' -> U -> bool) :
(* ed_sound *)
  forall
    (edc : embedded_dependency F Gf B Gb)
    (h : S -> S')
    (bh : Mimpl (Mmap h P) F)
    (fh : forall x, C x = true -> Gf (h x) = true),
    Meq (query P C E)
        (query (Mplus P B)
               (fun ab : (S * U)%type => C (fst ab) && Gb (h (fst ab)) (snd ab))
               (fun ab => E (fst ab))).
Proof.
  intros.
  transitivity (query P (fun x => C x && Gf (h x)) E).
  { admit. (* unfold query, Mbind, Mret, Mguard, Mconcat, Mmap.
    red. intro.
    eapply exists_iff. intro.
    eapply and_iff; [ | tauto ].
    apply exists_iff. intro.
    apply and_iff; try tauto.
    intro.
    specialize (fh x1).
    destruct (C x1); simpl in *.
    { specialize (fh eq_refl).
      rewrite fh. tauto. }
    { tauto. } *) }
  transitivity (query (Mplus P B)
                      (fun ab => C (fst ab) && Gf (h (fst ab)) && Gb (h (fst ab)) (snd ab))
                      (fun ab => E (fst ab))).
  { admit. (* unfold query, Mplus in *.
    repeat setoid_rewrite Mbind_assoc.
    repeat setoid_rewrite Mbind_Mret. simpl.
    repeat setoid_rewrite Mbind_assoc in edc.
    repeat setoid_rewrite Mbind_Mret in edc. simpl in edc.
    revert edc bh.
    unfold Meq, Mimpl, Mbind, Mguard, Mret, Mconcat, Mmap, Mzero.
    intros.
    split.
    { intros.
      forward_reason.
      specialize (edc (h x1)).
      specialize (fh x1).
      consider (C x1 && Gf (h x1)).
      { intros. subst. subst.
        destruct edc.
        destruct H0.
        { eexists. split.
          exists (h x1).
          split. eapply bh. eauto.
          reflexivity.
          eapply andb_true_iff in H1. destruct H1.
          rewrite H1. reflexivity. }
        { clear H2.
          forward_reason. subst.
          forward_reason. subst.
          consider (Gf x0 && Gb x0 x2).
          { intros. subst.
            apply andb_true_iff in H3. destruct H3.
            eexists. split.
            eexists. split. 2: reflexivity.
            2: simpl. eassumption.
            eexists. split.
            eexists. split. 2: reflexivity.
            eassumption.
            eapply andb_true_iff in H1.
            destruct H1.
            rewrite H1. rewrite H5. rewrite H4. simpl. reflexivity. }
          { inversion 2. } } }
      { intros; subst. inversion H0. } }
    { intros.
      forward_reason. subst.
      forward_reason. subst.
      consider (C x1 && Gf (h x1) && Gb (h x1) x2).
      { intros; subst.
        eapply andb_true_iff in H1. destruct H1.
        eapply andb_true_iff in H1. destruct H1.
        eexists. split.
        eexists; split; [ eassumption | reflexivity ].
        rewrite H1. rewrite H3. reflexivity. }
      { inversion 2. } } *) }
  { unfold query, Mplus.
    repeat setoid_rewrite Mbind_assoc.
    repeat setoid_rewrite Mbind_Mret. simpl.
    eapply Proper_Mbind; try reflexivity. red; intros.
    eapply Proper_Mbind; try reflexivity. red; intros.
    eapply Proper_Mguard; try reflexivity.
    specialize (fh a). clear - fh.
    consider (C a); try reflexivity.
    intros. rewrite H0; auto. }
Qed.

End chase.