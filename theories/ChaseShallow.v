Require Import Coq.Bool.Bool.
Require Import ExtLib.Data.Prop.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.

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
  fun _ x y => x = y.
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


Axiom Mbind_assoc : forall {A B C} (c1 : M A) (c2 : A -> M B) (c3 : B -> M C),
    Meq (Mbind (Mbind c1 c2) c3)
        (Mbind c1 (fun x => Mbind (c2 x) c3)).
Axiom Mbind_Mret : forall {A B} (x : A) (c : A -> M B),
    Meq (Mbind (Mret x) c) (c x).
Axiom Mret_Mbind : forall {A} (c : M A),
    Meq (Mbind c Mret) c.

Definition RelAnd {A} (r P : A -> A -> Prop) : A -> A -> Prop :=
  fun x y => r x y /\ P x y.

Axiom Proper_Mbind : forall {A B},
    Proper (Meq ==> (pointwise_relation _ Meq) ==> Meq) (@Mbind A B).
Existing Instance Proper_Mbind.

Definition drespectful {A} (F : A -> Type) (r : A -> A -> Prop) (rF : forall x y, r x y -> F x -> F y -> Prop) : forall (x y : forall x, F x) , Prop :=
  fun f g => forall x y (pf : r x y), @rF _ _ pf (f x) (g y).

Axiom Mbind_DProper : forall {A B} P,
    Proper ((RelAnd eq (fun x _ => P x) ==> Meq) ==> Meq) (@Mbind A B P).

Axiom Proper_Mguard : forall {A},
    Proper (eq ==> Meq ==> Meq) (@Mguard A).
Existing Instance Proper_Mguard.

(*Axiom tbl_movies : M (string * string). *)

Definition query {S T: Type}
           (P : M S)
           (C : S -> bool)
           (E : S -> T) : M T :=
  Mbind P (fun x => Mguard (C x) (Mret (E x))).

Theorem chase_sound {S T U}
        (P : M S) (C : S -> bool) (E : S -> T)
        (Q : M U) (B1 : S -> bool) (B2 : S -> U -> bool) :
        (query P B1 (fun x => x) =
         query (Mbind P (fun x => Mbind Q (fun y => Mret (x,y))))
               (fun ab => B1 (fst ab) && B2 (fst ab) (snd ab))
               (fun x => fst x)) ->
        (forall x, C x = true ->
                   B1 x = true) ->
        query P C E =
        query (Mbind P (fun x => Mbind Q (fun y => Mret (x,y))))
              (fun ab => C (fst ab) && B2 (fst ab) (snd ab))
              (fun ab => E (fst ab)).
Proof.
Admitted.

Definition Mplus {T U} (a : M T) (b : M U) : M (T * U) :=
  (Mbind a (fun x => Mbind b (fun y => Mret (x,y)))).

Require Import ExtLib.Tactics.

Axiom Transitive_Meq : forall {T}, Transitive (@Meq T).
Existing Instance Transitive_Meq.
Axiom Reflexive_Meq : forall {T}, Reflexive (@Meq T).
Existing Instance Reflexive_Meq.
Axiom Symmetry_Meq : forall {T}, Symmetric (@Meq T).
Existing Instance Symmetry_Meq.

Axiom Transitive_Mimpl : forall {T}, Transitive (@Mimpl T).
Existing Instance Transitive_Mimpl.
Axiom Reflexive_Mimpl : forall {T}, Reflexive (@Mimpl T).
Existing Instance Reflexive_Mimpl.


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

Theorem chase_sound_general {S S' T U}
(* q  *) (P : M S) (C : S -> bool) (E : S -> T)
(* ed *) (F : M S') (Gf : S' -> bool) (B : M U) (Gb : S' -> U -> bool) :
(* ed_sound *)
forall
      (edc : Meq (query F Gf (fun x => x))
                 (query (Mplus F B)
                        (fun ab => Gf (fst ab) && Gb (fst ab) (snd ab))
                        (fun x => fst x)))
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
  { unfold query, Mbind, Mret, Mguard, Mconcat, Mmap.
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
    { tauto. } }
  transitivity (query (Mplus P B)
                      (fun ab => C (fst ab) && Gf (h (fst ab)) && Gb (h (fst ab)) (snd ab))
                      (fun ab => E (fst ab))).
  { unfold query, Mplus in *.
    repeat setoid_rewrite Mbind_assoc.
    repeat setoid_rewrite Mbind_Mret. simpl.

    (** this is looking a bit more promising **)
    admit. }
  { clear - fh. admit. }
Qed.


(* all relations have the same type *)

q := for (x1 <- R1)    (** S = R1 *)
     where (C1 x1)

d := for (r1 <- R1 ; r2 <- R2 ; r3 <- R3)  (* S'=typeof R1 * typeof R2 * typeof R3 *)
     where (B1 r1 r2 r3)
     exists (s1 <- S1)
     where (B2 r1 r2 r3 s1)



Definition q :=
  Mbind tbl_movies (fun m1 =>
                      Mbind tbl_movies (fun m2 =>
                                          Mguard (fst m1 = fst m2)
                                                 (Mret (fst m1, snd m2)))).

Definition bd