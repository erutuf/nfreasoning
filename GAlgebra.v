Require Import List Field PeanoNat Arith.
Set Implicit Arguments.

Definition done_sbt A (H : Type)(t : A) := True.

Ltac substq1 := repeat
    match goal with
    | [H : forall _ : ?T, _ = _,  t0 : ?T |- _] =>
      let P := type of H in
      match goal with
      | H0 : done_sbt P t0 |- _ => fail 1
      | _ => rewrite (H t0) in *; assert (done_sbt P t0) by constructor
      end
    | [H : forall _ : ?T, _ -> _ = _,  t0 : ?T |- _] =>
      let P := type of H in
      match goal with
      | H0 : done_sbt P t0 |- _ => fail 1
      | _ => rewrite (H t0) in * by auto; assert (done_sbt P t0) by constructor
      end
    end.

Ltac substq0 := subst; repeat
    match goal with
    | H : _ = _ |- _ =>
        let P := type of H in
        match goal with
        | _ : done_sbt P tt |- _ => fail 1
        | _ => rewrite H in *; assert (done_sbt P tt) by constructor
        end
    end.

Ltac substq := substq0; substq1.

Record Field K := mkField
  { Kzero : K; Kone : K;
    Kplus : K -> K -> K; Kmult : K -> K -> K; Ksub : K -> K -> K;
    Kopp : K -> K;
    Kinv : K -> K;
    Kdiv : K -> K -> K;
    Kfield : field_theory Kzero Kone Kplus Kmult Ksub Kopp Kdiv Kinv eq
  }.

Record GAlgebra K G (dim : G -> nat)(KField : Field K) := mkGAlg
  { Gzero : nat -> G; Gone : nat -> G;
    Gplus : G -> G -> G;
    Gminus : G -> G -> G;
    Gmult : G -> G -> G;
    Gscalar : K -> G -> G;
    Gzero_dim : forall n, dim (Gzero n) = n;
    Gone_dim : forall n, dim (Gone n) = n;
    Gplus_dim : forall (l1 l2 : G), dim l1 = dim l2 -> dim (Gplus l1 l2) = dim l1;
    Gmult_dim : forall (l1 l2 : G), dim l1 = dim l2 -> dim (Gmult l1 l2) = dim l1;
    Gscalar_dim : forall (k : K)(l : G), dim (Gscalar k l) = dim l;
    Gminus_def : forall (l1 l2 : G), Gminus l1 l2 = Gplus l1 (Gscalar (KField.(Kopp) KField.(Kone)) l2);
    Gplus_ident_l : forall (l : G)(n : nat), dim l = n -> Gplus (Gzero n) l = l;
    Gmult_ident_l : forall (l : G)(n : nat), dim l = n -> Gmult (Gone n) l = l;
    Gplus_assoc : forall (l1 l2 l3 : G), dim l1 = dim l2 -> dim l2 = dim l3 ->
      Gplus (Gplus l1 l2) l3 = Gplus l1 (Gplus l2 l3);
    Gplus_comm : forall (l1 l2 : G), dim l1 = dim l2 -> Gplus l1 l2 = Gplus l2 l1;
    Gmult_assoc : forall (l1 l2 l3 : G), dim l1 = dim l2 -> dim l2 = dim l3 ->
      Gmult (Gmult l1 l2) l3 = Gmult l1 (Gmult l2 l3);
    Gmult_comm : forall (l1 l2 : G), dim l1 = dim l2 -> Gmult l1 l2 = Gmult l2 l1;
    Gplus_mult_distrib_l : forall (l1 l2 l3 : G), dim l1 = dim l2 -> dim l2 = dim l3 ->
      Gmult l1 (Gplus l2 l3) = Gplus (Gmult l1 l2) (Gmult l1 l3);
    Gscalar_plus_distrib : forall (k : K)(l1 l2 : G), dim l1 = dim l2 ->
      Gscalar k (Gplus l1 l2) = Gplus (Gscalar k l1) (Gscalar k l2);
    Gscalar_zero : forall (l : G), Gscalar KField.(Kzero) l = Gzero (dim l);
    Kplus_scalar_distrib : forall (k1 k2 : K)(l : G),
      Gplus (Gscalar k1 l) (Gscalar k2 l) = Gscalar (KField.(Kplus) k1 k2) l;
    Kmult_scalar_comm : forall (k1 k2 : K)(l : G),
      Gscalar k1 (Gscalar k2 l) = Gscalar (KField.(Kmult) k1 k2) l;
    Gscalar_one : forall (l : G), Gscalar KField.(Kone) l = l;
    Gscalar_mult_comm_l : forall (k : K)(l1 l2 : G), dim l1 = dim l2 ->
      Gmult (Gscalar k l1) l2 = Gscalar k (Gmult l1 l2)}.

Section GAlgebra.
  Variable K : Type.
  Variable K_Field : Field K.

  Add Field k_field : K_Field.(Kfield).

  Variable G : Type.
  Variable dim : G -> nat.
  Variable G_GAlg : GAlgebra dim K_Field.

  Notation K0 := K_Field.(Kzero).
  Notation K1 := K_Field.(Kone).
  Infix "+!" := K_Field.(Kplus) (at level 50, left associativity).
  Infix "*!" := K_Field.(Kmult) (at level 40, left associativity).
  Infix "-!" := K_Field.(Ksub) (at level 50, left associativity).
  Notation "-! x" := (K_Field.(Kopp) x) (at level 60).

  Notation G0 := G_GAlg.(Gzero).
  Notation G1 := G_GAlg.(Gone).
  Infix "+^" := G_GAlg.(Gplus) (at level 50, left associativity).
  Infix "*^" := G_GAlg.(Gmult) (at level 40, left associativity).
  Infix ".^" := G_GAlg.(Gscalar) (at level 45, no associativity).
  Infix "-^" := G_GAlg.(Gminus) (at level 50, left associativity).

  Lemma Gminus_dim : forall l1 l2, dim l1 = dim l2 ->
    dim (l1 -^ l2) = dim l1.
  Proof.
    intros. rewrite G_GAlg.(Gminus_def). rewrite G_GAlg.(Gplus_dim); [auto|].
    rewrite G_GAlg.(Gscalar_dim). auto.
  Qed.

  Lemma  Gplus_ident_r : forall (l : G)(n : nat), dim l = n -> l +^ (G0 n) = l.
  Proof.
    intros. rewrite G_GAlg.(Gplus_comm). apply G_GAlg.(Gplus_ident_l). auto.
    rewrite H. rewrite G_GAlg.(Gzero_dim). auto.
  Qed.

  Lemma Gmult_ident_r : forall (l : G)(n : nat), dim l = n -> l *^ (G1 n) = l.
  Proof.
    intros. rewrite G_GAlg.(Gmult_comm). apply G_GAlg.(Gmult_ident_l). auto.
    rewrite G_GAlg.(Gone_dim). auto.
  Qed.

  Lemma Gscalar_mult_comm_r : forall (k : K)(l1 l2 : G), dim l1 = dim l2 ->
      l1 *^ (k .^ l2) = k .^ (l1 *^ l2).
  Proof.
    intros. rewrite G_GAlg.(Gmult_comm).
    rewrite Gscalar_mult_comm_l; [auto|].
    f_equal. auto using G_GAlg.(Gmult_comm).
    auto. rewrite Gscalar_dim. auto.
  Qed.

  Lemma Gplus_minus_zero : forall l n, dim l = n -> l -^ l = G0 n.
  Proof with simpl in *.
    intros. subst. rewrite G_GAlg.(Gminus_def).
    rewrite <- (G_GAlg.(Gscalar_one) l) at 1...
    rewrite G_GAlg.(Kplus_scalar_distrib)...
    replace (K1 +! (-! K1)) with K0 by field.
    apply G_GAlg.(Gscalar_zero).
  Qed.

  Lemma Gplus_mult_distrib_r : forall (l1 l2 l3 : G), dim l1 = dim l2 -> dim l2 = dim l3 ->
      (l1 +^ l2) *^ l3 = (l1 *^ l3) +^ (l2 *^ l3).
  Proof with simpl in *.
    intros. repeat rewrite (G_GAlg.(Gmult_comm) _ l3).
    apply Gplus_mult_distrib_l; auto.
    4: rewrite G_GAlg.(Gplus_dim).
    all: substq; auto.
  Qed.

  Lemma Gminus_distrib_l : forall l1 l2 l3, dim l1 = dim l2 -> dim l2 = dim l3 ->
    (l1 -^ l2) *^ l3 = l1 *^ l3 -^ l2 *^ l3.
  Proof with simpl in *.
    intros. repeat rewrite G_GAlg.(Gminus_def).
    rewrite <- G_GAlg.(Gscalar_mult_comm_l).
    apply (@Gplus_mult_distrib_r l1 ((-! K1) .^ l2) l3).
    all: try rewrite G_GAlg.(Gscalar_dim); substq; auto.
  Qed.

  Lemma Gmult_zero_l : forall l n, dim l = n -> G0 n *^ l = G0 n.
  Proof with simpl in *.
    intros. subst.
    rewrite <- (@Gplus_minus_zero l) at 1 by auto.
    rewrite Gminus_distrib_l by auto.
    rewrite (@Gplus_minus_zero _ (dim l)); [auto|].
    apply G_GAlg.(Gmult_dim). auto.
  Qed.

  Lemma Gmult_zero_r : forall l n, dim l = n -> l *^ G0 n = G0 n.
  Proof with simpl in *.
    intros. rewrite G_GAlg.(Gmult_comm).
    - apply Gmult_zero_l. auto.
    - rewrite G_GAlg.(Gzero_dim). auto.
  Qed.

  Lemma Gscalar_G0 : forall k n, k .^ (G0 n) = G0 n.
  Proof with simpl in *.
    intros. rewrite <- (@Gplus_minus_zero (G0 n)) at 1.
    rewrite G_GAlg.(Gminus_def).
    rewrite G_GAlg.(Gscalar_plus_distrib).
    rewrite G_GAlg.(Kmult_scalar_comm).
    replace (k *! (-! K1)) with ((-! K1) *! k) by field.
    rewrite <- G_GAlg.(Kmult_scalar_comm).
    rewrite <- G_GAlg.(Gminus_def). apply Gplus_minus_zero.
    all: try rewrite G_GAlg.(Gscalar_dim); try rewrite G_GAlg.(Gzero_dim); auto.
  Qed.

  Lemma Geq_eq_zero : forall l1 l2, dim l1 = dim l2 ->
    l1 -^ l2 = G0 (dim l1) -> l1 = l2.
  Proof with simpl in *.
    intros. rewrite <- (Gplus_ident_r (n := dim l1)) by auto.
    rewrite <- (@Gplus_ident_r l2 (dim l2)) by auto.
    rewrite <- (@Gplus_minus_zero l2) by auto.
    rewrite G_GAlg.(Gminus_def) in *. rewrite <- G_GAlg.(Gplus_assoc).
    rewrite (G_GAlg.(Gplus_comm) l1).
    rewrite G_GAlg.(Gplus_assoc). f_equal. rewrite <- H. auto.
    all: try rewrite G_GAlg.(Gscalar_dim); auto.
  Qed.

  Lemma Gplus_neg_zero : forall l,
      l +^ ((-! K1) .^ l) = G0 (dim l).
  Proof.
    intros.
    rewrite <- (@Gplus_minus_zero l (dim l)) by auto.
    rewrite Gminus_def.
    auto.
  Qed.

  Inductive Ident :=
  | I0 : Ident
  | I1 : Ident
  | IVar : nat -> Ident.

  Inductive Term :=
  | TermOne : Ident -> Term
  | TermCons : Ident -> Term -> Term.

  Definition Exp := list (K * Term).

  Definition NormalForm := list (K * list nat).

  Fixpoint ins n (ns : list nat) : list nat :=
    match ns with
    | nil => n :: nil
    | m::ns' =>
      if le_dec n m
        then n :: m :: ns'
        else m :: ins n ns'
    end.

  Fixpoint merge (ns1 ns2 : list nat) : list nat :=
    match ns1 with
    | nil => ns2
    | n::rest => merge rest (ins n ns2)
    end.

  Fixpoint normalize_term (t : Term) : list nat :=
    match t with
    | TermOne i =>
      match i with
      | I0 => 0 :: nil
      | I1 => 1 :: nil
      | IVar n => n :: nil
      end
    | TermCons i t' =>
      match i with
      | I0 => 0 :: nil
      | I1 => normalize_term t'
      | IVar n => ins n (normalize_term t')
      end
    end.

  Inductive comparison := Lt | Eq | Gt.

  Fixpoint compare_ns (ns1 ns2 : list nat) : comparison :=
    match (ns1, ns2) with
    | (nil, nil) => Eq
    | ((_::_), nil) => Gt
    | (nil, (_::_)) => Lt
    | (n1::ns1', n2::ns2') =>
      match lt_eq_lt_dec n1 n2 with
      | inleft (left _) => Lt
      | inleft (right _) => compare_ns ns1' ns2'
      | inright _ => Gt
      end
    end.

  Lemma compare_ns_eq : forall ns1 ns2, compare_ns ns1 ns2 = Eq -> ns1 = ns2.
  Proof with simpl in *.
    induction ns1; destruct ns2...
    - auto.
    - discriminate.
    - discriminate.
    - destruct (lt_eq_lt_dec a n) as [[]|] eqn:Heqan.
      + discriminate.
      + intros. f_equal; firstorder.
      + discriminate.
  Qed.

  Fixpoint ins_ns (kt : K * list nat)(nf : NormalForm) : NormalForm :=
    match nf with
    | nil => kt :: nil
    | kt' :: rest =>
      let (k, t) := kt in
      let (k', t') := kt' in
      match compare_ns t t' with
      | Lt => kt :: kt' :: rest
      | Eq => ((k +! k'), t) :: rest
      | Gt => kt' :: ins_ns kt rest
      end
    end.

  Fixpoint exp2nf (exp : Exp) : NormalForm :=
    match exp with
    | nil => nil
    | (k, t) :: rest => ins_ns (k, normalize_term t) (exp2nf rest)
    end.

  Fixpoint getKey' (n : nat)(val : nat)(table : list (G * nat)) : G :=
    match table with
    | nil => G0 n
    | (key, val') :: table' =>
      if Nat.eq_dec val val'
        then key
        else getKey' n val table'
    end.

  Definition getKey (n : nat)(val : nat)(table : list (G * nat)) : G :=
    match val with
    | 0 => G0 n
    | 1 => G1 n
    | _ => getKey' n val table
    end.

  Lemma getKey_In : forall n val table,
    In (getKey n val table) (map fst table) \/ getKey n val table = G0 n \/ getKey n val table = G1 n.
  Proof with simpl in *.
    intros. destruct val as [|[]]; [auto..|].
    unfold getKey.
    remember (S (S n0)) as n'...
    induction table; [subst; auto|]...
    destruct a. destruct IHtable as [|[]]; destruct (Nat.eq_dec n' n1); firstorder.
  Qed.

  Definition ident2G (n : nat)(i : Ident)(table : list (G * nat)) : G :=
    match i with
    | I0 => G0 n
    | I1 => G1 n
    | IVar m => getKey n m table
    end.

  Fixpoint term2G (n : nat)(t : Term)(table : list (G * nat)) : G :=
    match t with
    | TermOne i => ident2G n i table
    | TermCons i t' => ident2G n i table *^ term2G n t' table
    end.

  Fixpoint exp2G (n : nat)(exp : Exp)(table : list (G * nat)) : G :=
    match exp with
    | nil => G0 n
    | (k, t)::rest => k .^ term2G n t table +^ exp2G n rest table
    end.

  Fixpoint ns2G' (n d : nat)(ns : list nat)(table : list (G * nat)) : G :=
    match ns with
    | nil => getKey n d table
    | m::ns' => getKey n d table *^ ns2G' n m ns' table
    end.
  Definition ns2G (n : nat)(ns : list nat)(table : list (G * nat)) : G :=
    match ns with
    | nil => G0 n
    | m::ns' => ns2G' n m ns' table
    end.

  Fixpoint nf2G (n : nat)(nf : NormalForm)(table : list (G * nat)) : G :=
    match nf with
    | nil => G0 n
    | (k, ns)::nf' => k .^ ns2G n ns table +^ nf2G n nf' table
    end.

  Definition table_dim (table : list (G * nat))(n : nat) :=
    forall x, In x (map fst table) -> dim x = n.

  Lemma getKey_dim : forall n val table,
    table_dim table n ->
    dim (getKey n val table) = n.
  Proof with simpl in *.
    intros. unfold table_dim in H. destruct (getKey_In n val table) as [|[]]; [firstorder|..].
    - rewrite H0. apply G_GAlg.(Gzero_dim).
    - rewrite H0. apply G_GAlg.(Gone_dim).
  Qed.

  Lemma ident2G_dim : forall n i table,
    table_dim table n ->
    dim (ident2G n i table) = n.
  Proof with simpl in *.
    intros.
    destruct i...
    - apply G_GAlg.(Gzero_dim).
    - apply G_GAlg.(Gone_dim).
    - unfold table_dim in H.
      destruct (getKey_In n n0 table) as [|[]]; [firstorder|..].
      + rewrite H0. apply G_GAlg.(Gzero_dim).
      + rewrite H0. apply G_GAlg.(Gone_dim).
  Qed.

  Lemma term2G_dim : forall n t table,
    table_dim table n ->
    dim (term2G n t table) = n.
  Proof with simpl in *.
    intros.
    induction t; simpl in *; [auto using ident2G_dim|].
    rewrite G_GAlg.(Gmult_dim); [auto using ident2G_dim|].
    rewrite IHt. auto using ident2G_dim.
  Qed.

  Lemma exp2G_dim : forall n exp table,
    table_dim table n ->
    dim (exp2G n exp table) = n.
  Proof with simpl in *.
    intros. induction exp; simpl in *; [auto using G_GAlg.(Gzero_dim)|].
    destruct a.
    rewrite G_GAlg.(Gplus_dim); rewrite G_GAlg.(Gscalar_dim); [auto using term2G_dim|].
    rewrite IHexp. auto using term2G_dim.
  Qed.

  Lemma ns2G'_dim : forall n m ns table,
    table_dim table n ->
    dim (ns2G' n m ns table) = n.
  Proof with simpl in *.
    intros. revert m. induction ns; simpl in *; [auto using getKey_dim|]; intros.
    rewrite G_GAlg.(Gmult_dim).
    - apply getKey_dim. auto.
    - rewrite IHns. apply getKey_dim. auto.
  Qed.

  Lemma ns2G_dim : forall n ns table,
    table_dim table n ->
    dim (ns2G n ns table) = n.
  Proof with simpl in *.
    intros. destruct ns...
    - apply G_GAlg.(Gzero_dim).
    - apply ns2G'_dim. auto.
  Qed.

  Lemma ns2G'_ins : forall n table ns m n0,
    table_dim table n ->
    ns2G' n n0 (ins m ns) table = ns2G' n m (n0 :: ns) table.
  Proof with simpl in *.
    induction ns; intros...
    - apply G_GAlg.(Gmult_comm). repeat rewrite getKey_dim; auto.
    - destruct (le_dec m a)...
      + repeat rewrite <- G_GAlg.(Gmult_assoc).
        f_equal. apply G_GAlg.(Gmult_comm).
        all: repeat rewrite getKey_dim; try rewrite ns2G'_dim; auto.
      + rewrite IHns by auto.
        repeat rewrite <- G_GAlg.(Gmult_assoc).
        f_equal. apply G_GAlg.(Gmult_comm).
        all: repeat rewrite getKey_dim; try rewrite ns2G'_dim; auto.
  Qed.

  Lemma ns2G_ins : forall n table ns m,
    table_dim table n ->
    ns2G n (ins m ns) table = ns2G n (m :: ns) table.
  Proof with simpl in *.
    intros. destruct ns; [auto|]. remember (n0 :: ns) as ns'...
    rewrite Heqns' at 1...
    destruct (le_dec m n0); [subst; auto|]...
    subst. apply ns2G'_ins. auto.
  Qed.

  Lemma nf2G_dim : forall n nf table,
    table_dim table n ->
    dim (nf2G n nf table) = n.
  Proof with simpl in *.
    intros. induction nf; simpl in *; [auto using G_GAlg.(Gzero_dim)|].
    destruct a.
    rewrite G_GAlg.(Gplus_dim).
    - rewrite G_GAlg.(Gscalar_dim). auto using ns2G_dim.
    - rewrite IHnf. rewrite G_GAlg.(Gscalar_dim). auto using ns2G_dim.
  Qed.

  Lemma nf2G_ins : forall n table nf t,
    table_dim table n ->
    nf2G n (ins_ns t nf) table = nf2G n (t :: nf) table.
  Proof with simpl in *.
    induction nf; [auto|]...
    intros. destruct t. destruct a.
    destruct (compare_ns l l0) eqn:Hcomp...
    - auto.
    - apply compare_ns_eq in Hcomp. subst.
      rewrite <- G_GAlg.(Gplus_assoc).
      rewrite <- G_GAlg.(Kplus_scalar_distrib). auto.
      repeat rewrite G_GAlg.(Gscalar_dim).
      repeat rewrite ns2G_dim; auto.
      rewrite G_GAlg.(Gscalar_dim).
      rewrite ns2G_dim; [rewrite nf2G_dim|]; auto.
    - rewrite IHnf; [|auto]. repeat rewrite <- G_GAlg.(Gplus_assoc).
      rewrite (G_GAlg.(Gplus_comm) (k0 .^ ns2G n l0 table)). auto.
      all: repeat rewrite G_GAlg.(Gscalar_dim).
      all: repeat rewrite ns2G_dim; [try rewrite nf2G_dim|..]; auto.
  Qed.

  Lemma ns_inj : forall n table t,
    table_dim table n ->
    term2G n t table = ns2G n (normalize_term t) table.
  Proof with simpl in *.
    intros. induction t...
    - destruct i; auto.
    - destruct i...
      + apply Gmult_zero_l. apply term2G_dim. auto.
      + rewrite G_GAlg.(Gmult_ident_l); [auto|].
        apply term2G_dim. auto.
      + rewrite ns2G_ins; [|auto]...
        clear IHt. induction t...
        * destruct i; simpl; auto...
        * destruct i...
          { rewrite Gmult_zero_l. repeat rewrite Gmult_zero_r. auto.
            - rewrite getKey_dim; auto.
            - rewrite term2G_dim; auto. }
          { rewrite G_GAlg.(Gmult_ident_l). auto.
            rewrite term2G_dim; auto. }
          { rewrite ns2G'_ins by auto... rewrite <- IHt.
            repeat rewrite <- G_GAlg.(Gmult_assoc).
            f_equal. apply G_GAlg.(Gmult_comm).
            all: repeat rewrite getKey_dim; try rewrite term2G_dim; auto. }
  Qed.

  Lemma nf_inj : forall n table exp,
    table_dim table n ->
    exp2G n exp table = nf2G n (exp2nf exp) table.
  Proof with simpl in *.
    intros.
    induction exp; [auto|]...
    destruct a. rewrite nf2G_ins; [|auto]...
    rewrite IHexp. f_equal. f_equal. apply ns_inj; auto.
  Qed.

  Theorem uniq : forall n table exp1 exp2,
    table_dim table n ->
    exp2nf exp1 = exp2nf exp2 -> exp2G n exp1 table = exp2G n exp2 table.
  Proof with simpl in *.
    intros. repeat rewrite nf_inj by auto.
    f_equal. auto.
  Qed.

End GAlgebra.

Create HintDb galg.
Hint Rewrite Gminus_def Gmult_zero_l Gmult_zero_r Gplus_ident_l Gplus_ident_r
  Gmult_ident_l Gmult_ident_r Gplus_mult_distrib_l Gplus_mult_distrib_r
  Gscalar_plus_distrib Gscalar_zero Gscalar_one Gscalar_mult_comm_l
  Gscalar_mult_comm_r Kplus_scalar_distrib Kmult_scalar_comm Gplus_assoc
  Gmult_assoc Gscalar_G0 Gplus_neg_zero : galg.

Create HintDb gdim.
Hint Rewrite Gzero_dim Gone_dim Gplus_dim Gmult_dim Gminus_dim Gscalar_dim : gdim.

Ltac lookup key table :=
  match table with
  | nil => constr:(@None nat)
  | ?t :: ?table' =>
    match t with
    | (key, ?n) => constr:(Some n)
    | _ => lookup key table'
    end
  end.

Ltac gen_table' ga x table :=
  let opt := lookup x table in
  let g0 := eval simpl in (Gzero ga) in
  let g1 := eval simpl in (Gone ga) in
  let gmult := eval simpl in (Gmult ga) in
  let gscalar := eval simpl in (Gscalar ga) in
  let gplus := eval simpl in (Gplus ga) in
  let gminus := eval simpl in (Gminus ga) in
  match opt with
  | None =>
    match x with
    | gscalar _ ?y => gen_table' ga y table
    | gmult ?y ?z =>
      let table' := gen_table' ga y table in
      gen_table' ga z table'
    | gplus ?y ?z =>
      let table' := gen_table' ga y table in
      gen_table' ga z table'
    | gminus ?y ?z =>
      let table' := gen_table' ga y table in
      gen_table' ga z table'
    | g0 _ => constr:table
    | g1 _ => constr:table
    | _ =>
      let n := eval simpl in (2 + length table)%nat in
      constr:((x, n) :: table)
    end
  | Some _ => constr:table
  end.

Ltac gen_table galg x :=
  let G := type of x in
  gen_table' galg x (@nil (G * nat)).

Ltac to_term galg table x :=
  let g0 := eval simpl in (Gzero galg) in
  let g1 := eval simpl in (Gone galg) in
  let gmult := eval simpl in (Gmult galg) in
  match x with
  | gmult ?y ?z =>
    let ez := to_term galg table z in
    match y with
    | g0 _ => constr:(TermCons (IVar O) ez)
    | g1 _ => constr:(TermCons (IVar (S O)) ez)
    | _ =>
      let ey_opt := lookup y table in
      match ey_opt with
      | Some ?ey  => constr:(TermCons (IVar ey) ez)
      | _ => fail "ey_opt" y
      end
    end
  | g0 _ => constr:(TermOne (IVar O))
  | g1 _ => constr:(TermOne (IVar (S O)))
  | _ => let ex_opt := lookup x table in
    match ex_opt with
    | Some ?ex => constr:(TermOne (IVar ex))
    | _ => fail "ex_opt" x
    end
  end.

Ltac get_field galg :=
  match type of galg with
  | GAlgebra _ ?F => constr:F
  end.

Definition galg_helper G (x : G) := True.

Ltac to_exp galg table x :=
  let KF := get_field galg in
  let k1 := eval simpl in (Kone KF) in
  let gplus := eval simpl in (Gplus galg) in
  let gscalar := eval simpl in (Gscalar galg) in
  lazymatch x with
  | gplus ?y ?z =>
    let ez := to_exp galg table z in
    lazymatch y with
    | gscalar ?k ?y' =>
      let ty := to_term galg table y' in
      constr:((k, ty) :: ez)
    | _ =>
      let ty := to_term galg table y in
      constr:((k1, ty) :: ez)
    end
  | gscalar ?k ?x' =>
    let tx := to_term galg table x' in
    constr:((k, tx) :: nil)
  | _ =>
    let tx := to_term galg table x in
    constr:((k1, tx) :: nil)
  end.

Ltac get_dim galg :=
  match type of galg with
  | GAlgebra ?dim _ => constr:dim
  end.

Tactic Notation "gautorewrite" constr(ga) :=
  let gzero := eval simpl in (Gzero ga) in
  let gone := eval simpl in (Gone ga) in
  let gplus := eval simpl in (Gplus ga) in
  let gmult := eval simpl in (Gmult ga) in
  let gminus := eval simpl in (Gminus ga) in
  let gscalar := eval simpl in (Gscalar ga) in
  replace gzero with (Gzero ga) by auto;
  replace gone with (Gone ga) by auto;
  replace gplus with (Gplus ga) by auto;
  replace gmult with (Gmult ga) by auto;
  replace gminus with (Gminus ga) by auto;
  replace gscalar with (Gscalar ga) by auto;
  autorewrite with galg; simpl.

Ltac gautorewritein galg H :=
  let gzero := eval simpl in (Gzero galg) in
  let gone := eval simpl in (Gone galg) in
  let gplus := eval simpl in (Gplus galg) in
  let gmult := eval simpl in (Gmult galg) in
  let gminus := eval simpl in (Gminus galg) in
  let gscalar := eval simpl in (Gscalar galg) in
  replace gzero with (Gzero galg) in H by auto;
  replace gone with (Gone galg) in H by auto;
  replace gplus with (Gplus galg) in H by auto;
  replace gmult with (Gmult galg) in H by auto;
  replace gminus with (Gminus galg) in H by auto;
  replace gscalar with (Gscalar galg)  in H by auto;
  autorewrite with galg in H; simpl in H.

Tactic Notation "gautorewrite" constr(ga) "in" constr(H) :=
  gautorewritein ga H.

Tactic Notation "gdautorewrite" constr(ga) :=
  let gzero := eval simpl in (Gzero ga) in
  let gone := eval simpl in (Gone ga) in
  let gplus := eval simpl in (Gplus ga) in
  let gmult := eval simpl in (Gmult ga) in
  let gminus := eval simpl in (Gminus ga) in
  let gscalar := eval simpl in (Gscalar ga) in
  replace gzero with (Gzero ga) by auto;
  replace gone with (Gone ga) by auto;
  replace gplus with (Gplus ga) by auto;
  replace gmult with (Gmult ga) by auto;
  replace gminus with (Gminus ga) by auto;
  replace gscalar with (Gscalar ga) by auto;
  autorewrite with gdim || simpl.

Ltac gdautorewritein galg H :=
  let gzero := eval simpl in (Gzero galg) in
  let gone := eval simpl in (Gone galg) in
  let gplus := eval simpl in (Gplus galg) in
  let gmult := eval simpl in (Gmult galg) in
  let gminus := eval simpl in (Gminus galg) in
  let gscalar := eval simpl in (Gscalar galg) in
  replace gzero with (Gzero galg) in H by auto;
  replace gone with (Gone galg) in H by auto;
  replace gplus with (Gplus galg) in H by auto;
  replace gmult with (Gmult galg) in H by auto;
  replace gminus with (Gminus galg) in H by auto;
  replace gscalar with (Gscalar galg)  in H by auto;
  autorewrite with gdim in H; simpl in H.

Tactic Notation "gdautorewrite" constr(ga) "in" constr(H) :=
  gdautorewritein ga H.

Ltac field_vanish' x f0 :=
  try (replace x with f0 by field).

Ltac field_vanish galg :=
  let F := get_field galg in
  let f0 := eval simpl in (Kzero F) in
  let gscalar := eval simpl in (Gscalar galg) in
  repeat (
    match goal with
    | |- context[gscalar ?k _] =>
      match goal with
      | H : galg_helper k |- _ => fail 1
      | _ => field_vanish' k f0; assert (galg_helper k) by constructor
      end
    end
  ).

Ltac galg_simplify_with_table d x ga table :=
  let F := get_field ga in
  let ex := to_exp ga table x in
  replace x with (exp2G ga d ex table);
  [|simpl; gautorewrite ga; auto];
  [
    replace (exp2G ga d ex table) with (nf2G ga d (exp2nf F ex) table);
    [|symmetry; apply nf_inj; unfold table_dim; auto]
  |..];
  [simpl; field_vanish ga; gautorewrite ga|..].

Ltac galg_simplify d x ga :=
  let G := type of x in
  let F := get_field ga in
  let dim := get_dim ga in
  let H_ := fresh "H_" in
  assert (galg_helper x) as H_ by constructor;
  let table := gen_table ga x in
  let H_ := fresh in
  enough (table_dim dim table d) as H_; unfold table_dim in *;
  [
    gautorewrite ga;
    [
      gautorewrite ga in H_;
      [
        match type of H_ with
        | galg_helper ?x' =>
          clear H_;
          let ex := to_exp ga table x' in
          replace x' with (exp2G ga d ex table) by
              (simpl in *; gautorewrite ga; auto);
          replace (exp2G ga d ex table) with (nf2G ga d (exp2nf F ex) table) by
              (symmetry; apply nf_inj; unfold table_dim; auto)
        end
      |..]
    |..];
    [
      solve [
          simpl;
          field_vanish ga;
          gautorewrite ga ]
    |
      repeat gdautorewrite ga;
      repeat rewrite H_;
      simpl;
      auto
    ]
  |
    apply Forall_forall; simpl
  ].

Ltac galgebra d ga :=
  let dim := get_dim ga in
  let F := get_field ga in
  let f0 := eval simpl in (Kzero F) in
  let gplus := eval simpl in (Gplus ga) in
  let d' := fresh in
  let Heqd := fresh in
  remember d as d' eqn:Heqd;
  match goal with
  | |- ?x = ?y =>
    let z := constr:(gplus x y) in
    let table := gen_table ga z in
    let H_ := fresh in
    enough (table_dim dim table d') as H_; unfold table_dim in *;
    [
      apply (Geq_eq_zero ga);
      [ repeat gdautorewrite ga; repeat rewrite H_; simpl; now (tauto || firstorder)|];
      gautorewrite ga;
      [
        match goal with
        | |- ?x' = _ => galg_simplify_with_table d' x' ga table
        end;
        [
          auto
        |..]
      |..];
      repeat (gdautorewrite ga);
      repeat rewrite H_;
      simpl;
      auto
    |
      apply Forall_forall; simpl; subst d'
    ]
  end.