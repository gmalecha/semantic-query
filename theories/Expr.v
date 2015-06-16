Require Import Coq.Lists.List.
Require Import Coq.Logic.Eqdep_dec.
Require Import ExtLib.Data.Member.
Require Import ExtLib.Data.HList.
Require Import SemanticQuery.Types.

Set Implicit Arguments.
Set Strict Implicit.

(** Deeply embedded expressions **)
Inductive expr (vars : list type) : type -> Type@{UU} :=
| Var : forall T, member T vars -> expr vars T
| Proj : forall T r, expr vars (Tuple r) -> member T r -> expr vars T
| Eq : forall T, expr vars T -> expr vars T -> expr vars Bool
| Lt : expr vars Nat -> expr vars Nat -> expr vars Bool
| Const : forall T, typeD T -> expr vars T.

Definition Env : list type -> Type@{U} := hlist typeD.
Definition exprT (ls : list type) (T : Type) : Type :=
  Env ls -> T.

Fixpoint exprD {vars} {t} (e : expr vars t)
: exprT vars (typeD t) :=
  match e in expr _ t return exprT vars (typeD t) with
  | Var m => hlist_get m
  | Proj e' f =>
    let eD := @exprD vars (Tuple _) e' in
    let fD := tuple_get typeD f in
    fun vs => fD (eD vs)
  | Eq l r =>
    let lD := exprD l in
    let rD := exprD r in
    let eqD := @val_dec _ in
    fun vs => if eqD (lD vs) (rD vs) then true else false
  | Lt l r =>
    let lD := exprD l in
    let rD := exprD r in
    fun vs => if Compare_dec.lt_dec (lD vs) (rD vs) then true else false
  | Const _ T v => fun _ => v
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
  | Var m => Var (member_lift _ m)
  | Proj a b => Proj (expr_lift _ a) b
  | Eq a b => Eq (expr_lift _ a) (expr_lift _ b)
  | Lt a b => Lt (expr_lift _ a) (expr_lift _ b)
  | Const _ T v => @Const _ T v
  end.

Fixpoint member_weaken_app {T} {t : T} (vs vs' : list T) (m : member t vs')
  : member t (vs' ++ vs) :=
  match m in member _ vs' return member t (vs' ++ vs) with
  | MZ _ _ => MZ _ _
  | MN _ m => MN _ (member_weaken_app _ m)
  end.

Fixpoint expr_weaken_app {T} vs vs' (e : expr vs' T) {struct e}
  : expr (vs' ++ vs) T :=
  match e in expr _ T return expr (vs' ++ vs) T with
  | Var a => Var (member_weaken_app _ a)
  | Proj a b => Proj (expr_weaken_app _ a) b
  | Eq a b => Eq (expr_weaken_app _ a) (expr_weaken_app _ b)
  | Lt a b => Lt (expr_weaken_app _ a) (expr_weaken_app _ b)
  | Const _ T v => @Const _ T v
  end.

Section _subst.
  Context {vars vars' : list type}.
  Variable (f :forall {x}, member x vars -> member x vars').

  Fixpoint expr_subst  {T}
           (e : expr vars T) {struct e} : expr vars' T :=
    match e in expr _ T return expr vars' T with
    | Var v => Var (f v)
    | Proj v c => Proj (expr_subst v) c
    | Eq a b => Eq (expr_subst a) (expr_subst b)
    | Lt a b => Lt (expr_subst a) (expr_subst b)
    | Const _ T v => @Const _ T v
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
    | MZ _ ls => fun m2 =>
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
                | MZ _ _ => fun pf => left _
                | MN _ _ => fun pf => right _
                end eq_refl
    | @MN _ _ l ls m1' => fun m2 =>
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
                | MZ _ _ => fun _ _ => right _
                | MN _ m2' => fun _ rec =>
                                  match rec m2' with
                                  | left pf => left (f_equal _ pf)
                                  | right pf => right _
                                  end
                end m1' (member_eq _ m1')
    end.
    refine (@K_dec _ Tdec _ (fun pf => MZ t l =
                                       match pf in (_ = X) return (member X (t :: l)) with
                                       | eq_refl => MZ t l
                                       end) eq_refl pf).
    destruct pf. clear.
    intro.
    refine match H in _ = X return match X with
                                   | MN _ _ => False
                                   | MZ _ _ => True
                                   end
           with
           | eq_refl => I
           end.
    clear. intro.
    refine match H in _ = X return match X with
                                   | MN _ _ => True
                                   | MZ _ _ => False
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

Inductive Expr_ctor : Type := EVar | EProj | EEq | ELt | EConst.
Definition ctor_for {ts t} (e : expr ts t) : Expr_ctor :=
  match e with
  | Eq _ _ => EEq
  | Lt _ _ => ELt
  | Var _ => EVar
  | Proj _ _ => EProj
  | Const _ _ _ => EConst
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

Lemma not_Const : forall a b c X,
    EConst <> ctor_for X ->
    @Const a b c <> X.
Proof.
  red; intros; eapply (@f_apply _ _ ctor_for _ _) in H0; auto.
Defined.

Lemma not_Lt : forall a b c X,
    ELt <> ctor_for X ->
    @Lt a b c <> X.
Proof.
  red; intros; eapply (@f_apply _ _ ctor_for _ _) in H0; auto.
Defined.

Lemma Injective_Var : forall ts t (m1 m2 : member t ts),
    Var m1 = Var m2 -> m1 = m2.
Proof.
  intros.
  refine (match H in _ = t
                return match t in expr _ Z
                             return member Z ts -> Prop
                       with
                       | Var mx => fun m1 => m1 = mx
                       | _ => fun _ => True
                       end m1
          with
          | eq_refl => eq_refl
          end).
Defined.

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
  refine
    match H in _ = X
          return match X in expr _ T
                       return forall t, expr ts (Tuple t) -> member T t -> Prop
                 with
                 | @Proj _ T' t'' x y =>
                   fun t''' a'' f'' =>
                     exists pf : t'' = t''',
                               a'' = match pf in _ = X return expr ts (Tuple X) with
                                   | eq_refl => x
                                   end /\
                               f'' = match pf in _ = X return member T' X with
                                     | eq_refl => y
                                     end
                 | _ => fun _ _ _ => True
                 end t a f
    with
    | eq_refl => _
    end.
  exists eq_refl. tauto.
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
  intros.
  refine
    match H in _ = X
          return match X in expr _ T
                       return forall t, expr ts t -> expr ts t -> Prop
                 with
                 | @Eq _ t'' x y =>
                   fun T a'' b'' =>
                     exists pf : t'' = T,
                               a'' = match pf in _ = X return expr ts X with
                                     | eq_refl => x
                                     end /\
                               b'' = match pf in _ = X return expr ts X with
                                     | eq_refl => y
                                     end
                 | _ => fun _ _ _ => True
                 end T a b
    with
    | eq_refl => _
    end.
  exists eq_refl. tauto.
Defined.

Lemma Injective_Lt : forall ts (a b : expr ts Nat) (c d : expr ts Nat),
    Lt a b = Lt c d ->
    a = c /\ b = d.
Proof.
  intros. inversion H. clear. auto.
Defined.

Lemma Injective_Const : forall ts T v v',
    @Const ts T v = @Const ts T v' ->
    v = v'.
Proof.
  intros.
  refine
    match H in _ = X
          return match X in expr _ T
                       return typeD T -> Prop
                 with
                 | @Const _ t'' x =>
                   fun v =>
                     v = x
                 | _ => fun _ => True
                 end v
    with
    | eq_refl => eq_refl
    end.
Defined.

Definition UIP_type (a : type) (pf : a = a) : pf = eq_refl.
Proof.
  refine (K_dec _ (fun x => x = eq_refl) eq_refl pf).
  intros. destruct (type_dec x y); auto.
Defined.

Definition UIP_list_type (a : list type) (pf : a = a) : pf = eq_refl.
Proof.
  refine (K_dec _ (fun x => x = eq_refl) eq_refl pf).
  intros. destruct (list_eq_dec type_dec x y); auto.
Defined.

Section expr_eq.
  Context {vs : list type}.

  Fixpoint expr_eq {T} (a b : expr vs T) {struct a} : {a = b} + {a <> b}.
    refine
      (match a as a in expr _ T
             return forall b : expr vs T, {a = b} + {a <> b}
       with
       | Var m1 => fun b =>
                       match b as b in expr _ T
                             return forall m1, {Var m1 = b} + {Var m1 <> b}
                       with
                       | Var m2 => fun m1 =>
                                       match member_eq type_dec m1 m2 with
                                       | left pf => left match pf in _ = t return _ = _ with
                                                         | eq_refl => eq_refl
                                                         end
                                       | right pf => right _
                                       end
                       | _ => fun _ => right _
                       end m1
       | @Proj _ x y e1 f1 => fun b : expr vs x =>
                             match b as b in expr _ T
                                   return forall (e1 : expr vs (Tuple y)) f1,
                                 (forall e2, {e1 = e2} + {e1 <> e2}) ->
                                 {@Proj _ T y e1 f1 = b} +
                                 {Proj e1 f1 <> b}
                             with
                             | @Proj _ x' y' e2 f2 => fun e1 f1 rec =>
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
       | @Eq _ T1 l1 r1 => fun b : expr vs Bool =>
                          match b as b in expr _ T'
                                return match T' as T' return expr vs T' -> Type with
                                       | Bool => fun b => forall T1 (l1 r1 : expr vs T1),
                                                     (forall l2, {l1 = l2} + {l1 <> l2}) ->
                                                     (forall r2, {r1 = r2} + {r1 <> r2}) ->
                                                     {Eq l1 r1 = b} + {Eq l1 r1 <> b}
                                       | _ => fun _ => unit
                                       end b
                          with
                          | @Eq _ T2 l2 r2 => fun T1 l1 r1 recL recR =>
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
       | Lt l r => fun b : expr vs Bool =>
                     match b as b in expr _ T'
                           return match T' as T' return expr _ T' -> Type
                                  with
                                  | Bool => fun b => forall l r : expr _ Nat,
                                      (forall x, {l = x} + {l <> x}) ->
                                      (forall x, {r = x} + {r <> x}) ->
                                      {Lt l r = b} + {Lt l r <> b}
                                  | _ => fun _ => unit
                                  end b
                     with
                     | Lt l' r' => fun _ _ recL recR =>
                                     match recL l' with
                                     | left pf => match recR r' with
                                                  | left pf' => left _
                                                  | right _ => right _
                                                  end
                                     | right _ => right _
                                     end
                     | Eq _ _ => fun _ _ _ _ => right _
                     | _ => _
                     end l r (expr_eq _ l) (expr_eq _ r)
       | Const _ T v => fun b : expr vs T =>
                        match b as b in expr _ T'
                              return forall v : typeD T', 
                            {@Const _ T' v = b} +
                            {@Const _ T' v <> b}
                        with
                        | Const _ _ v => fun v' => match val_dec v v' with
                                                 | left pf => left _
                                                 | right pf => right _
                                                 end
                        | _ => fun _ => right _
                        end v
       end b);
    try solve [ clear ; first [ eapply not_Var | eapply not_Proj | eapply not_Eq  | eapply not_Const | eapply not_Lt ] ; simpl; congruence ].
    { intro pf'. apply pf. apply Injective_Var. apply pf'. }
    { subst. reflexivity. }
    { intro. eapply Injective_Proj in H. destruct H as [ ? [ ? ? ] ]. subst.
      clear - n.
      rewrite (UIP_list_type x0) in n. auto. }
    { clear - n. subst. intro.
      eapply Injective_Proj in H. apply n.
      destruct H as [ ? [ ? ? ] ].
      clear - H. rewrite (UIP_list_type x) in H. assumption. }
    { clear - pf.
      intro. eapply Injective_Proj in H.
      destruct H; auto. }
    { clear.
      destruct t; try exact tt.
      intros.
      right. eapply not_Eq. compute. congruence. }
    { clear.
      destruct t; try exact tt.
      intros. right.
      eapply not_Eq. compute. congruence. }
    { subst. reflexivity. }
    { subst. clear - n.
      intro.
      eapply Injective_Eq in H.
      destruct H as [ ? [ ? ? ] ].
      apply n.
      rewrite (UIP_type x) in H0. assumption. }
    { subst. clear - n.
      intro. eapply Injective_Eq in H.
      destruct H as [ ? [ ? ? ] ].
      apply n. clear - H.
      rewrite (UIP_type x) in H. assumption. }
    { clear - n.
      intro. eapply Injective_Eq in H.
      destruct H. auto. }
    { intros. right.
      clear. eapply not_Eq. simpl. congruence. }
    { destruct t; try exact tt.
      intros. right.
      eapply not_Eq. simpl. congruence. }
    { destruct t; try exact tt.
      intros; right.
      eapply not_Lt. simpl. congruence. }
    { destruct t; try exact tt.
      intros; right.
      eapply not_Lt. simpl. congruence. }
    { subst. reflexivity. }
    { intro. apply Injective_Lt in H. destruct H. auto. }
    { intro. apply Injective_Lt in H. destruct H. auto. }
    { destruct t; try exact tt.
      intros; right.
      eapply not_Lt. simpl. congruence. }
    { subst. reflexivity. }
    { clear - pf.
      intro. eapply Injective_Const in H.
      auto. }
  Defined.

End expr_eq.