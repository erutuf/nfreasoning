Require Import List PeanoNat Omega Recdef.
Set Implicit Arguments.

Record CommSemigroup A := mkCSG
  { CSelem : A;
    CSplus : A -> A -> A;
    CSplus_assoc : forall x y z : A, CSplus (CSplus x y) z = CSplus x (CSplus y z);
    CSplus_comm : forall x y : A, CSplus x y = CSplus y x }.

Section CommSemigroup.

  Variable A : Type.
  Variable A_CSG : CommSemigroup A.
  Infix "+!" := A_CSG.(CSplus) (at level 50, left associativity).

  Inductive Exp :=
  | ExpVar : nat -> Exp
  | ExpPlus : Exp -> Exp -> Exp.

  Definition NF := list nat.

  Fixpoint ins n (nf : NF) : NF :=
    match nf with
    | nil => n :: nil
    | m::nf' =>
      if le_dec n m
        then n :: m :: nf'
        else m :: ins n nf'
    end.

  Fixpoint exp2nf' (ex : Exp)(nf : NF) : NF :=
    match ex with
    | ExpVar n => ins n nf
    | ExpPlus ey ez => exp2nf' ez (exp2nf' ey nf)
    end.
  Definition exp2nf ex := exp2nf' ex nil.

  Fixpoint getKey (val : nat)(table : list (A * nat)) : A :=
    match table with
    | nil => A_CSG.(CSelem)
    | (key,val')::table' =>
      if Nat.eq_dec val val'
        then key
        else getKey val table'
    end.

  Fixpoint exp2A (ex : Exp)(table : list (A * nat)) : A :=
    match ex with
    | ExpVar n => getKey n table
    | ExpPlus ey ez => exp2A ey table +! exp2A ez table
    end.

  Fixpoint nf2A nf table :=
    match nf with
    | nil => A_CSG.(CSelem)
    | n::nil => getKey n table
    | n::nf' => getKey n table +! nf2A nf' table
    end.

  Fixpoint addnf a nf table :=
    match nf with
    | nil => a
    | n::nf' => getKey n table +! addnf a nf' table
    end.

  Lemma addnf_plus : forall table a b nf,
    addnf (a +! b) nf table = a +! addnf b nf table.
  Proof with simpl in *.
    induction nf; [auto|]...
    rewrite IHnf. repeat rewrite <- A_CSG.(CSplus_assoc).
    rewrite (A_CSG.(CSplus_comm) a). reflexivity.
  Qed.

  Lemma addnf_comm : forall table a b nf,
    a +! addnf b nf table = b +! addnf a nf table.
  Proof with simpl in *.
    intros. rewrite <- addnf_plus. rewrite A_CSG.(CSplus_comm). rewrite addnf_plus. auto.
  Qed.

  Lemma addnf_nf2A : forall table n nf,
    addnf (getKey n table) nf table = nf2A (n::nf) table.
  Proof with simpl in *.
    induction nf; [auto|]... rewrite IHnf.
    destruct nf.
    - apply A_CSG.(CSplus_comm).
    - repeat rewrite <- A_CSG.(CSplus_assoc). f_equal.
      apply A_CSG.(CSplus_comm).
  Qed.

  Lemma addnf_left : forall table a n nf,
    addnf a (n::nf) table = a +! nf2A (n::nf) table.
  Proof with simpl in*.
    intros.
    rewrite <- (addnf_nf2A table n nf).
    induction nf; simpl in *; [auto|].
    - apply (A_CSG.(CSplus_comm)).
    - rewrite (A_CSG.(CSplus_comm) (getKey a0 table)).
      repeat rewrite <- A_CSG.(CSplus_assoc). rewrite IHnf.
      repeat rewrite A_CSG.(CSplus_assoc). f_equal. apply A_CSG.(CSplus_comm).
  Qed.

  Lemma nf2A_ins : forall table n nf,
    nf2A (ins n nf) table = nf2A (n::nf) table.
  Proof with simpl in *.
    induction n; induction nf; [auto..|]...
    destruct (le_dec (S n) a)...
     - auto.
     - f_equal. rewrite IHnf.
      destruct nf...
       + apply A_CSG.(CSplus_comm).
       + destruct (le_dec (S n) n1); simpl;
        repeat rewrite <- A_CSG.(CSplus_assoc); f_equal; apply A_CSG.(CSplus_comm).
  Qed.

  Function list_ind2' X (P : list X -> Prop) (H : P nil) (H0 : forall x, P (x :: nil))
    (H1 : forall x y l, P (y :: l) -> P (x :: y :: l)) l {measure length l} : P l :=
    match l return P l with
    | nil => H
    | x::nil => H0 x
    | x::y::l' => H1 x y l' (list_ind2' P H H0 H1 (y :: l'))
    end.
  Proof.
    intros. subst. auto.
  Qed.

  Definition list_ind2 : forall X (P : list X -> Prop),
    P nil ->
    (forall x, P (x :: nil)) ->
    (forall x y l, P (y:: l) -> (P (x :: y :: l))) ->
    forall l, P l := fun X P H H0 H1 l => list_ind2' P H H0 H1 l.

  Lemma exp2nf'_cons : forall ex nf,
    exp2nf' ex nf <> nil.
  Proof with simpl in *.
    induction ex; induction nf...
    - discriminate.
    - destruct (le_dec n a); discriminate.
    - intro. firstorder.
    - intro. firstorder.
  Qed.

  Lemma nf_inj : forall ex nf table,
    addnf (exp2A ex table) nf table = nf2A (exp2nf' ex nf) table.
  Proof with simpl in *.
    induction ex.
    - apply (list_ind2 (fun nf => forall table,
    addnf (exp2A (ExpVar n) table) nf table = nf2A (exp2nf' (ExpVar n) nf) table)); intros...
      + auto.
      + destruct (le_dec n x); simpl; [apply A_CSG.(CSplus_comm)|auto].
      + specialize (H table).
        destruct (le_dec n x); destruct (le_dec n y)...
        * repeat rewrite <- A_CSG.(CSplus_assoc).
          rewrite (A_CSG.(CSplus_comm) (getKey n table)).
          repeat rewrite A_CSG.(CSplus_assoc). f_equal. auto.
        * rewrite H. rewrite nf2A_ins...
          destruct l...
          { rewrite (A_CSG.(CSplus_comm) (getKey y table)).
            repeat rewrite <- A_CSG.(CSplus_assoc).
            f_equal. apply A_CSG.(CSplus_comm). }
          { destruct (le_dec n n1); repeat rewrite <- A_CSG.(CSplus_assoc); f_equal;
            rewrite (A_CSG.(CSplus_comm) (getKey n table)); repeat rewrite A_CSG.(CSplus_assoc); f_equal; apply A_CSG.(CSplus_comm). }
        * f_equal. auto.
        * rewrite H. auto.
    - apply (list_ind2 (fun nf => forall (table : list (A * nat)),
        addnf (exp2A (ExpPlus ex1 ex2) table) nf table =
        nf2A (exp2nf' (ExpPlus ex1 ex2) nf) table)); intros...
      + rewrite <- IHex2.
        destruct (exp2nf' ex1 nil) eqn:?.
        { apply exp2nf'_cons in Heqn. contradiction. }
        rewrite addnf_left. rewrite A_CSG.(CSplus_comm). f_equal.
        rewrite <- Heqn. rewrite <- IHex1... auto.
      + rewrite <- IHex2.
        destruct (exp2nf' ex1 (x :: nil)) eqn:?.
        { apply exp2nf'_cons in Heqn. contradiction. }
        rewrite addnf_left. rewrite <- Heqn. rewrite <- IHex1...
        rewrite (A_CSG.(CSplus_comm) (exp2A ex1 table)). repeat rewrite <- A_CSG.(CSplus_assoc).
        f_equal. apply A_CSG.(CSplus_comm).
      + rewrite H. rewrite <- (IHex2 (exp2nf' ex1 (x :: y :: l))).
        destruct (exp2nf' ex1 (x :: y :: l)) eqn:?.
        { apply exp2nf'_cons in Heqn. contradiction. }
        rewrite addnf_left. rewrite <- Heqn. rewrite <- IHex1.
        rewrite addnf_left. simpl. rewrite <- A_CSG.(CSplus_assoc). rewrite <- A_CSG.(CSplus_assoc).
        rewrite (A_CSG.(CSplus_comm) _ (getKey x table)). rewrite A_CSG.(CSplus_assoc). f_equal.
        rewrite <- IHex2.
        destruct (exp2nf' ex1 (y :: l)) eqn:?.
        { apply exp2nf'_cons in Heqn1. contradiction. }
        rewrite addnf_left. rewrite <- Heqn1. rewrite A_CSG.(CSplus_assoc). f_equal.
        rewrite <- IHex1. rewrite addnf_left. auto.
  Qed.

  Lemma uniq' : forall table ex ey nf,
    exp2nf' ex nf = exp2nf' ey nf ->
    addnf (exp2A ex table) nf table = addnf (exp2A ey table) nf table.
  Proof with simpl in *.
    intros. rewrite nf_inj. rewrite nf_inj. rewrite H. auto.
  Qed.

  Lemma uniq : forall ex ey table,
    exp2nf ex = exp2nf ey -> exp2A ex table = exp2A ey table.
  Proof with simpl in *.
    unfold exp2nf. intros. apply (uniq' table) in H... auto.
  Qed.

End CommSemigroup.

Ltac lookup key table :=
  match table with
  | nil => constr:(@None nat)
  | ?t :: ?table' =>
    match t with
    | (key, ?n) => constr:(Some n)
    | _ => lookup key table'
    end
  end.

Ltac get_CSelem csg := eval simpl in (CSelem csg).
Ltac get_CStype csg :=
  let a0 := get_CSelem csg in
  type of a0.
Ltac get_CSplus csg := eval simpl in (CSplus csg).
Ltac get_CSplus_assoc csg := eval simpl in (CSplus_assoc csg).
Ltac get_CSplus_comm csg := eval simpl in (CSplus_comm csg).

Ltac gen_table' csg x n table :=
  let opt := lookup x table in
  let csplus := get_CSplus csg in
  match opt with
  | None =>
    match x with
    | csplus ?y ?z =>
      let res := gen_table' csg y n table in
      match res with
      | (?n', ?table') =>
        gen_table' csg z n' table'
      end
    | _ => constr:(S n, (x, n)::table)
    end
  | Some ?n' => constr:(n, table)
  end.

Ltac gen_table csg x :=
  let A := get_CStype csg in
  gen_table' csg x O (@nil (A * nat)).

Ltac to_exp csg table x :=
  let csplus := get_CSplus csg in
  match x with
  | csplus ?y ?z =>
    let ey := to_exp csg table y in
    let ez := to_exp csg table z in
    constr:(ExpPlus ey ez)
  | _ =>
    let ex_opt := lookup x table in
    match ex_opt with
    | Some ?ex => constr:(ExpVar ex)
    end
  end.

Ltac semigroup csg :=
  match goal with
  | |- ?x = ?y =>
    let t := gen_table csg x in
    match t with
    | (_, ?table) =>
      let ex := to_exp csg table x in
      let ey := to_exp csg table y in
      enough (exp2A csg ex table = exp2A csg ey table) by auto;
      apply uniq;
      unfold exp2nf;
      auto
    end
  end.