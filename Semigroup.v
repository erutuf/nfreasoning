Require Import List PeanoNat Omega.
Set Implicit Arguments.

Section Test.
  Variable A : Type.
  Variable bot : A.
  Variable Aplus : A -> A -> A.
  Infix "+!" := Aplus (at level 50, left associativity).
  Variable Aplus_assoc : forall x y z : A, (x +! y) +! z = x +! (y +! z).
  Variable Aplus_comm : forall x y, x +! y = y +! x.
  Variable Aeq_dec : forall x y : A, {x = y} + {x <> y}.

  Inductive ExpA :=
  | ExpVar : nat -> ExpA
  | ExpPlus : ExpA -> ExpA -> ExpA.

  Ltac lookup key table :=
    match table with
    | nil => constr:(@None nat)
    | ?t :: ?table' =>
      match t with
      | (key, ?n) => constr:(Some n)
      | _ => lookup key table'
      end
    end.

  Ltac gen_table' x n table :=
    let opt := lookup x table in
    match opt with
    | None =>
      match x with
      | ?y +! ?z =>
        let res := gen_table' y n table in
        match res with
        | (?n', ?table') =>
          gen_table' z n' table'
        end
      | _ => constr:(S n, (x, n)::table)
      end
    end.

  Ltac gen_table x y :=
    let res1 := gen_table' x O (@nil (A * nat)) in
    match res1 with
    | (?n, ?table) =>
      let res2 := gen_table' y n table in
      match res2 with
      | (_, ?table') => table'
      end
    end.

  Ltac to_exp table x :=
    match x with
    | ?y +! ?z =>
      let ey := to_exp table y in
      let ez := to_exp table z in
      constr:(ExpPlus ey ez)
    | _ =>
      let ex_opt := lookup x table in
      match ex_opt with
      | Some ?ex => constr:(ExpVar ex)
      end
    end.

  Definition NFA := list nat.

  Fixpoint ins n (nf : NFA) : NFA :=
    match nf with
    | nil =>
      match n with
      | O => 1 :: nil
      | S n' => (repeat O (S n')) ++ (1 :: nil)
      end
    | m::nf' =>
      match n with
      | O => (S m) :: nf'
      | S n' => m :: ins n' nf'
      end
    end.

  Fixpoint exp2nf' (ex : ExpA)(nf : NFA) : NFA :=
    match ex with
    | ExpVar n => ins n nf
    | ExpPlus ey ez => exp2nf' ez (exp2nf' ey nf)
    end.
  Definition exp2nf ex := exp2nf' ex nil.

  Fixpoint getKey (val : nat)(table : list (A * nat)) : A :=
    match table with
    | nil => bot
    | (key,val')::table' =>
      if Nat.eq_dec val val'
        then key
        else getKey val table'
    end.

  Fixpoint exp2A (ex : ExpA)(table : list (A * nat)) : A :=
    match ex with
    | ExpVar n => getKey n table
    | ExpPlus ey ez => exp2A ey table +! exp2A ez table
    end.

  Lemma repeat_inj : forall X (x : X) n m, repeat x n = repeat x m -> n = m.
  Proof with simpl in *.
    induction n; destruct m; (discriminate || firstorder).
    f_equal... inversion H. firstorder.
  Qed.

  Lemma ins_inj : forall n m nf, ins n nf = ins m nf -> n = m.
  Proof with simpl in *.
    induction n; intros...
    - destruct nf; destruct m; (discriminate || auto)...
      inversion H. exfalso. omega.
    - destruct nf; destruct m; simpl in *; (discriminate || auto)...
      inversion H. f_equal. apply app_inv_tail in H1. eauto using repeat_inj.
      inversion H. exfalso. omega.
      inversion H. firstorder.
  Qed.

  Axiom uniq : forall ex ey table , exp2nf ex = exp2nf ey -> exp2A ex table = exp2A ey table.
  (* TODO: proof *)

  Ltac semigroup :=
    match goal with
    | |- ?x = ?y =>
      let t := gen_table' x O (@nil (A * nat)) in
      match t with
      | (_, ?table) =>
        let ex := to_exp table x in
        let ey := to_exp table y in
        enough (exp2A ex table = exp2A ey table) by auto;
        apply uniq;
        unfold exp2nf;
        auto
      end
    end.

  Goal forall x y z, (x +! y) +! z = y +! (z +! x).
  Proof.
    intros.
    semigroup.
  Qed.

  Goal forall x y z w, (x +! y) +! (z +! w) = w +! (x +! z) +! y.
  Proof.
    intros.
    semigroup.
  Qed.
End Test.