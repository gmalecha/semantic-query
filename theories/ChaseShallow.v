Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import SemanticQuery.Shallow.

Set Implicit Arguments.
Set Strict Implicit.

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
    eapply Proper_Mbind_eq; try reflexivity. red; intros.
    eapply Proper_Mbind_eq; try reflexivity. red; intros.
    eapply Proper_Mguard; try reflexivity.
    specialize (fh a). clear - fh.
    consider (C a); try reflexivity.
    intros. rewrite H0; auto. }
Qed.

End chase.