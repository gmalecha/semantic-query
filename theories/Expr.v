Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import SemanticQuery.Types.

Set Implicit Arguments.
Set Strict Implicit.

(** Deeply embedded expressions **)
Inductive expr (vars : list type) : type -> UU :=
| Var : forall T, member T vars -> expr vars T
| Proj : forall T r, expr vars (Tuple r) -> member T r -> expr vars T
| Eq : forall T, expr vars T -> expr vars T -> expr vars Bool.

Definition Env : list type -> U := hlist typeD.
Definition exprT (ls : list type) (T : Type) : Type :=
  Env ls -> T.

Fixpoint exprD {vars} {t} (e : expr vars t)
: exprT vars (typeD t) :=
  match e in expr _ t return exprT vars (typeD t) with
  | Var _ m => hlist_get m
  | Proj _ r e' f =>
    let eD := @exprD vars (Tuple r) e' in
    let fD := tuple_get typeD f in
    fun vs => fD (eD vs)
  | Eq T l r =>
    let lD := exprD l in
    let rD := exprD r in
    let eqD := @val_dec T in
    fun vs => if eqD (lD vs) (rD vs) then true else false
  end.

Fixpoint member_lift {T} {t : T} (vs vs' : list T) (m : member t vs')
: member t (vs ++ vs') :=
  match vs as vs return member t (vs ++ vs') with
  | nil => m
  | v :: vs => MN _ (member_lift _ m)
  end.

Fixpoint expr_lift {T} vs vs' (e : expr vs' T) {struct e}
: expr (vs ++ vs') T :=
  match e in expr _ T return expr (vs ++ vs') T with
  | Var _ m => Var (member_lift _ m)
  | Proj _ _ a b => Proj (expr_lift _ a) b
  | Eq T a b => Eq (expr_lift _ a) (expr_lift _ b)
  end.

Fixpoint member_weaken_app {T} {t : T} (vs vs' : list T) (m : member t vs')
  : member t (vs' ++ vs) :=
  match m in member _ vs' return member t (vs' ++ vs) with
  | MZ _ => MZ _ _
  | MN _ _ m => MN _ (member_weaken_app _ m)
  end.

Fixpoint expr_weaken_app {T} vs vs' (e : expr vs' T) {struct e}
  : expr (vs' ++ vs) T :=
  match e in expr _ T return expr (vs' ++ vs) T with
  | Var _ a => Var (member_weaken_app _ a)
  | Proj _ _ a b => Proj (expr_weaken_app _ a) b
  | Eq T a b => Eq (expr_weaken_app _ a) (expr_weaken_app _ b)
  end.

Section _subst.
  Context {vars vars' : list type}.
  Variable (f :forall {x}, member x vars -> member x vars').

  Fixpoint expr_subst  {T}
           (e : expr vars T) {struct e} : expr vars' T :=
    match e in expr _ T return expr vars' T with
    | Var _ v => Var (f v)
    | Proj _ _ v c => Proj (expr_subst v) c
    | Eq T a b => Eq (expr_subst a) (expr_subst b)
    end.
End _subst.

Section member_eq.
  Context {T:Type}.
  Variable Teq : forall a b : T, {a = b} + {a <> b}.
  Context {t : T}.

  Let Tdec (a b : T) : a = b \/ a <> b :=
    match Teq a b with
    | left pf => or_introl pf
    | right pf => or_intror pf
    end.

  (** TODO: Move this to ExtLib **)
  Fixpoint member_eq {ls} (m1 : member t ls) {struct m1}
  : forall m2, {m1 = m2} + {m1 <> m2}.
  refine
    match m1 as m1 in member _ ls
          return forall m2, {m1 = m2} + {m1 <> m2}
    with
    | MZ ls => fun m2 =>
                match m2 as m2 in member _ X
                      return match X as X return member t X -> Type with
                             | nil => fun _ => Empty_set
                             | x :: xs => fun m2 : member t (x :: xs) =>
                                            forall pf : t = x,
                                              let m2 := match pf in _ = X return member X _ with
                                                        | eq_refl => m2
                                                        end in
                                              {@MZ _ x xs = m2} +
                                              {@MZ _ x xs <> m2}
                             end m2
                with
                | MZ _ => fun pf => left _
                | MN _ _ _ => fun pf => right _
                end eq_refl
    | MN l ls m1' => fun m2 =>
                match m2 as m2 in member _ X
                      return match X as X return member t X -> Type with
                             | nil => fun _ => Empty_set
                             | x :: xs => fun m2 : member t (x :: xs) =>
                                            forall m1' : member t xs,
                                              (forall x : member t xs,
                                                  {m1' = x} + {m1' <> x}) ->
                                            {@MN _ _ x xs m1' = m2} +
                                            {@MN _ _ x xs m1' <> m2}
                             end m2
                with
                | MZ _ => fun _ _ => right _
                | MN _ _ m2' => fun _ rec =>
                                  match rec m2' with
                                  | left pf => left (f_equal _ pf)
                                  | right pf => right _
                                  end
                end m1' (member_eq _ m1')
    end.
    refine (@K_dec _ Tdec _ (fun pf => MZ t ls1 =
                                       match pf in (_ = X) return (member X (t :: ls1)) with
                                       | eq_refl => MZ t ls1
                                       end) eq_refl pf).
    destruct pf. clear.
    intro.
    refine match H in _ = X return match X with
                                   | MN _ _ _ => False
                                   | MZ _ => True
                                   end
           with
           | eq_refl => I
           end.
    clear. intro.
    refine match H in _ = X return match X with
                                   | MN _ _ _ => True
                                   | MZ _ => False
                                   end
           with
           | eq_refl => I
           end.
    intro.
    apply pf. clear - H.
    eapply (@Injection.injection _ (Injective_MN _ _ _)) in H.
    red in H. simpl in H. apply H.
  Defined.
End member_eq.

Inductive Expr_ctor : Type := EVar | EProj | EEq.
Definition ctor_for {ts t} (e : expr ts t) : Expr_ctor :=
  match e with
  | Eq _ _ _ => EEq
  | Var _ _ => EVar
  | Proj _ _ _ _ => EProj
  end.
Definition f_apply {T U} (f : T -> U) (a b : T) (pf : a = b) : f a = f b :=
  match pf in _ = t return f a = f t with
  | eq_refl => eq_refl
  end.

Lemma not_Var : forall a b c X,
    EVar <> ctor_for X ->
    @Var a b c <> X.
Proof.
  red; intros; eapply (@f_apply _ _ ctor_for _ _) in H0; auto.
Defined.

Lemma not_Proj : forall a b c d e X,
    EProj <> ctor_for X ->
    @Proj a b c d e <> X.
Proof.
  red; intros; eapply (@f_apply _ _ ctor_for _ _) in H0; auto.
Defined.

Lemma not_Eq : forall a b c d X,
    EEq <> ctor_for X ->
    @Eq a b c d <> X.
Proof.
  red; intros; eapply (@f_apply _ _ ctor_for _ _) in H0; auto.
Defined.

Section expr_eq.
  Context {vs : list type}.

  Fixpoint expr_eq {T} (a b : expr vs T) {struct a} : {a = b} + {a <> b}.
    refine
      (match a as a in expr _ T
             return forall b : expr vs T, {a = b} + {a <> b}
       with
       | Var _ m1 => fun b =>
                       match b as b in expr _ T
                             return forall m1, {Var m1 = b} + {Var m1 <> b}
                       with
                       | Var _ m2 => fun m1 =>
                                       match member_eq type_dec m1 m2 with
                                       | left pf => left match pf in _ = t return _ = _ with
                                                         | eq_refl => eq_refl
                                                         end
                                       | right pf => right _
                                       end
                       | _ => fun _ => right _
                       end m1
       | Proj x y e1 f1 => fun b : expr vs x =>
                             match b as b in expr _ T
                                   return forall (e1 : expr vs (Tuple y)) f1,
                                 (forall e2, {e1 = e2} + {e1 <> e2}) ->
                                 {@Proj _ T y e1 f1 = b} +
                                 {Proj e1 f1 <> b}
                             with
                             | Proj x' y' e2 f2 => fun e1 f1 rec =>
                                                     match List.list_eq_dec type_dec y' y with
                                                     | left pf =>
                                                       match rec match pf in _ = t return expr _ (Tuple t) with
                                                                 | eq_refl => e2
                                                                 end
                                                       with
                                                       | left pf' =>
                                                         match member_eq type_dec f1
                                                                         match pf in _ = t return member _ t with
                                                                         | eq_refl => f2
                                                                         end
                                                         with
                                                         | left pf => left _
                                                         | right _ => right _
                                                         end
                                                       | right _ => right _
                                                       end
                                                     | right pf => right _
                                                     end
                             | _ => fun _ _ _ => right _
                             end e1 f1 (@expr_eq _ e1)
       | Eq T1 l1 r1 => fun b : expr vs Bool =>
                          match b as b in expr _ T'
                                return match T' as T' return expr vs T' -> Type with
                                       | Bool => fun b => forall T1 (l1 r1 : expr vs T1),
                                                     (forall l2, {l1 = l2} + {l1 <> l2}) ->
                                                     (forall r2, {r1 = r2} + {r1 <> r2}) ->
                                                     {Eq l1 r1 = b} + {Eq l1 r1 <> b}
                                       | _ => fun _ => unit
                                       end b
                          with
                          | Eq T2 l2 r2 => fun T1 l1 r1 recL recR =>
                                             match type_dec T2 T1 with
                                             | left pf =>
                                               match recL match pf in _ = t return expr _ t with
                                                          | eq_refl => l2
                                                          end
                                                     , recR match pf in _ = t return expr _ t with
                                                            | eq_refl => r2
                                                            end
                                               with
                                               | left _ , left _ => left _
                                               | _ , _ => right _
                                               end
                                             | right _ => right _
                                             end
                          | _ => _
                          end T1 l1 r1 (@expr_eq _ l1) (@expr_eq _ r1)
       end b);
    try solve [ clear ; first [ eapply not_Var | eapply not_Proj | eapply not_Eq ] ; simpl; congruence ].
    Lemma Injective_Var : forall ts t (m1 m2 : member t ts),
        Var m1 = Var m2 -> m1 = m2.
    Proof.
      intros.
      refine (match H in _ = t
                    return match t in expr _ Z
                                 return member Z ts -> Prop
                           with
                           | Var x mx => fun m1 => m1 = mx
                           | _ => fun _ => True
                           end m1
              with
              | eq_refl => eq_refl
              end).
    Defined.
    intro pf'. apply pf. apply Injective_Var. apply pf'.
    subst. reflexivity.
    Lemma Injective_Proj
      : forall ts T t t' (a : expr ts (Tuple t)) (a' : expr ts (Tuple t'))
               (f : member T t) (f' : member T t'),
        Proj a f = Proj a' f' ->
        exists pf : t' = t, a = match pf in _ = X return expr _ (Tuple X) with
                                | eq_refl => a'
                                end /\ f = match pf in _ = X return member _ X with
                                           | eq_refl => f'
                                           end.
    Proof.
      intros.
      inversion H. exists (eq_sym H1).
      admit.
    Defined.
    Lemma Injective_Eq : forall ts T T' (a b : expr ts T) (c d : expr ts T'),
        Eq a b = Eq c d ->
        exists pf : T' = T,
          a = match pf in _ = X return expr _ X with
              | eq_refl => c
              end /\
          b = match pf in _ = X return expr _ X with
              | eq_refl => d
              end.
    Proof.
      intros. inversion H. exists (eq_sym H1).
      admit.
    Defined.
    intro. eapply Injective_Proj in H. destruct H as [ ? [ ? ? ] ]. subst.
    clear expr_eq; admit.
    clear expr_eq; intro; admit.
    clear expr_eq; intro; admit.
    { clear.
      destruct T0; try exact tt.
      intros; admit. }
    { clear.
      destruct T0; try exact tt.
      intros; admit. }
    subst. reflexivity.
    clear expr_eq. intro; admit.
    clear expr_eq. intro; admit.
    clear expr_eq. intro; admit.
  Defined.

End expr_eq.