Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.DataModel.

Set Implicit Arguments.
Set Strict Implicit.

Section chase.
  Variable M : Type -> Type.
  Context {DM : DataModel M}.

  Lemma Mbind_Mguard_cont {T U : Type} (m : M T) (k : T -> M U) p
  : Meq (Mbind m (fun x => Mguard p (k x)))
        (Mguard p (Mbind m k)).
  Proof. destruct p; simpl. reflexivity. rewrite <- Mbind_then_Mzero. reflexivity. Qed.

  Instance Reflexive_leb : Reflexive leb.
  Proof. red. red. destruct x; reflexivity. Qed.

  Instance Transitive_leb : Transitive leb.
  Proof. red. red. destruct x; simpl; auto. intros; subst. destruct z; auto. Qed.


  Lemma duplicate {T} (m : M T)
  : Meq m (Mbind m (fun _ => m)).
  Proof.
    split. 2: setoid_rewrite Mbind_ignore; reflexivity.
    transitivity (Mbind m (fun _ => Mbind m Mret)).
    rewrite <- Mbind_perm.
    generalize (@Mbind_dup M _ T T m (fun x => Mret (fst x))).
    simpl. intro. rewrite <- H.
    rewrite Mret_Mbind. reflexivity.
    setoid_rewrite Mret_Mbind. reflexivity.
  Qed.

  Definition Meqsat {T} (m m' : M T) : Prop :=
    Meq (Mbind m (fun _ => Mret tt))
        (Mbind m' (fun _ => Mret tt)).

  Instance Reflexive_Meqsat {T} : Reflexive (@Meqsat T).
  Proof. red. red. reflexivity. Qed.

  Instance Transitive_Meqsat {T} : Transitive (@Meqsat T).
  Proof. red. unfold Meqsat. intros. etransitivity; eassumption. Qed.

  Lemma Mbind_ignore_eqsat {T U} (m1 m2 : M T) (k : M U)
  : Meqsat m1 m2 ->
    Meq (Mbind m1 (fun _ => k))
        (Mbind m2 (fun _ => k)).
  Proof.
    unfold Meqsat.
    intros.
    transitivity (Mbind m1 (fun _ => Mbind (Mret tt) (fun _ => k))).
    { setoid_rewrite Mbind_Mret. reflexivity. }
    { setoid_rewrite <- Mbind_assoc. rewrite H.
      rw_M. reflexivity. }
  Qed.


(*
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
        (query (Mprod P B)
               (fun ab : (S * U)%type => C (fst ab) && Gb (h (fst ab)) (snd ab))
               (fun ab => E (fst ab))).
Proof.
  intros.
  transitivity (query P (fun x => C x && Gf (h x)) E).
  { unfold query. clear - fh.
    eapply Proper_Mbind_eq; try reflexivity.
    red. intros. specialize (fh a).
    destruct (C a); try reflexivity.
    simpl. rewrite fh; reflexivity. }
  transitivity (query (Mprod P B)
                      (fun ab => C (fst ab) && Gf (h (fst ab)) && Gb (h (fst ab)) (snd ab))
                      (fun ab => E (fst ab))).
  { red in edc. unfold query, Mprod in *. revert edc.
    rw_M. intros.
    transitivity
      (Mbind P (fun x => Mguard (C x) (Mbind (Mbind F (fun z => Mguard (Gf z) (Mret z))) (fun _ => Mret (E x))))).
    { clear - bh fh. admit.
    }
    transitivity
      (Mbind P (fun x => Mguard (C x) (Mbind (Mbind F (fun z => Mbind B (fun y => Mguard (Gf z) (Mguard (Gb z y) (Mret z))))) (fun _ => Mret (E x))))).
    { setoid_rewrite H; clear H.
      simpl. rw_M. setoid_rewrite Mguard_and. reflexivity. }
    { clear - bh fh. admit. } }
  { unfold query, Mprod. rw_M. simpl.
    eapply Proper_Mbind_eq; try reflexivity. red; intros.
    eapply Proper_Mbind_eq; try reflexivity. red; intros.
    eapply Proper_Mguard; try reflexivity.
    specialize (fh a). clear - fh.
    consider (C a); try reflexivity.
    intros. rewrite H0; auto. }
Abort.
*)

End chase.
