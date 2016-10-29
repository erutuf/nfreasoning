Require Import List Field PeanoNat Arith.
Require Import Reals RealField.
Require Import Substq GAlgebra.
Set Implicit Arguments.
Import ListNotations.

Section Sample.
  Variable K : Type.
  Variable K_Field : Field K.

  Add Field k_field' : K_Field.(Kfield).

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

  Goal forall (x y z : G)(k l : K)(n : nat), (forall w : G, List.In w [x; y; z] -> dim w = n) ->
    (k .^ x) *^ y +^ l .^ z +^ (-! k) .^ x *^ y +^ k .^ z
    = k *! l .^ y *^ x +^ ((-! l) .^ (k .^ y *^ x) +^ k .^ z) +^ l .^ z.
  Proof.
    intros.
    galgebra n G_GAlg. all: repeat rewrite H; simpl; firstorder.
  Qed.
End Sample.

Section ListSample.

  Open Scope R_scope.

  Definition R_Field : Field R :=
    mkField Rfield.

  Fixpoint zipWith A B C (f : A -> B -> C) l1 l2 : list C :=
    match l1, l2 with
    | (a::l1'), (b::l2') => f a b :: zipWith f l1' l2'
    | _, _ => []
    end.

  Definition V0 n := repeat R0 n.
  Definition V1 n := repeat R1 n.

  Definition Vplus x y := zipWith Rplus x y.
  Definition Vmult x y := zipWith Rmult x y.
  Definition Vscalar k x := map (Rmult k) x.
  Definition Vminus x y := Vplus x (Vscalar (-1) y).

  Lemma V0_dim : forall n, length (V0 n) = n.
  Proof.
    unfold V0. intros. apply repeat_length.
  Qed.

  Lemma V1_dim : forall n, length (V1 n) = n.
  Proof.
    unfold V1. intros. apply repeat_length.
  Qed.

  Lemma zipWith_length : forall A B C l1 l2 (f : A -> B -> C),
    length l1 = length l2 -> length (zipWith f l1 l2) = length l1.
  Proof with simpl in *.
    induction l1; induction l2; intros; auto...
    f_equal. inversion H. firstorder.
  Qed.

  Lemma Vplus_dim : forall l1 l2, length l1 = length l2 -> length (Vplus l1 l2) = length l1.
  Proof.
    unfold Vplus. auto using zipWith_length.
  Qed.

  Lemma Vmult_dim : forall l1 l2, length l1 = length l2 -> length (Vmult l1 l2) = length l1.
  Proof.
    unfold Vmult. auto using zipWith_length.
  Qed.

  Lemma Vscalar_dim : forall k l, length (Vscalar k l) = length l.
  Proof.
    unfold Vscalar. auto using map_length.
  Qed.

  Lemma Vminus_def : forall l1 l2, Vminus l1 l2 = Vplus l1 (Vscalar (-1) l2).
  Proof.
    unfold Vminus. auto.
  Qed.

  Lemma Vplus_ident_l : forall l n, length l = n -> Vplus (V0 n) l = l.
  Proof with simpl in *.
    unfold Vplus, V0.
    induction l; destruct n; intros; auto; simpl in *; try congruence.
    inversion H. f_equal; [field|auto].
  Qed.

  Lemma Vmult_ident_l : forall l n, length l = n -> Vmult (V1 n) l = l.
  Proof with simpl in *.
    unfold Vmult, V1.
    induction l; destruct n; intros; auto; simpl in *; try congruence.
    inversion H. f_equal; [field|auto].
  Qed.

  Lemma Vplus_assoc : forall l1 l2 l3, length l1 = length l2 -> length l2 = length l3 ->
    Vplus (Vplus l1 l2) l3 = Vplus l1 (Vplus l2 l3).
  Proof with simpl in *.
    unfold Vplus.
    induction l1; destruct l2; destruct l3; simpl in *; congruence || auto...
    intros. f_equal; [field|auto].
  Qed.

  Lemma Vplus_comm : forall l1 l2, length l1 = length l2 ->
    Vplus l1 l2 = Vplus l2 l1.
  Proof with simpl in *.
    unfold Vplus.
    induction l1; destruct l2; simpl in *; congruence || auto...
    intros. inversion H. f_equal; [field|auto].
  Qed.

  Lemma Vmult_assoc : forall l1 l2 l3, length l1 = length l2 -> length l2 = length l3 ->
    Vmult (Vmult l1 l2) l3 = Vmult l1 (Vmult l2 l3).
  Proof with simpl in *.
    unfold Vmult.
    induction l1; destruct l2; destruct l3; simpl in *; congruence || auto...
    intros. f_equal; [field|auto].
  Qed.

  Lemma Vmult_comm : forall l1 l2, length l1 = length l2 ->
    Vmult l1 l2 = Vmult l2 l1.
  Proof with simpl in *.
    unfold Vmult.
    induction l1; destruct l2; simpl in *; congruence || auto...
    intros. inversion H. f_equal; [field|auto].
  Qed.

  Lemma Vplus_mult_distrib_l : forall l1 l2 l3,
    length l1 = length l2 -> length l2 = length l3 ->
    Vmult l1 (Vplus l2 l3) = Vplus (Vmult l1 l2) (Vmult l1 l3).
  Proof with simpl in *.
    unfold Vmult, Vplus.
    induction l1; destruct l2; destruct l3; simpl in *; congruence || auto...
    intros. f_equal; [field|]. inversion H. inversion H0. auto.
  Qed.

  Lemma Vscalar_plus_distrib : forall k l1 l2, length l1 = length l2 ->
    Vscalar k (Vplus l1 l2) = Vplus (Vscalar k l1) (Vscalar k l2).
  Proof with simpl in *.
    unfold Vscalar, Vplus.
    induction l1; destruct l2; simpl in *; congruence || auto...
    intros. inversion H. f_equal; [field|auto].
  Qed.

  Lemma Vscalar_zero : forall l, Vscalar R0 l = V0 (length l).
  Proof with simpl in *.
    unfold Vscalar, V0. induction l; [auto|]...
    f_equal; [field|auto].
  Qed.

  Lemma Rplus_scalar_distrib : forall k1 k2 l,
    Vplus (Vscalar k1 l) (Vscalar k2 l) = Vscalar (k1 + k2) l.
  Proof with simpl in *.
    unfold Vscalar, Vplus.
    induction l; [auto|]...
    f_equal; [field|auto].
  Qed.

  Lemma Rmult_scalar_comm : forall k1 k2 l,
    Vscalar k1 (Vscalar k2 l) = Vscalar (k1 * k2) l.
  Proof with simpl in *.
    unfold Vscalar.
    induction l; [auto|]...
    f_equal; [field|auto].
  Qed.

  Lemma Vscalar_one : forall l, Vscalar 1 l = l.
  Proof with simpl in *.
    unfold Vscalar. induction l; [auto|]...
    f_equal; [field|auto].
  Qed.

  Lemma Vscalar_mult_comm_l : forall k l1 l2, length l1 = length l2 ->
    Vmult (Vscalar k l1) l2 = Vscalar k (Vmult l1 l2).
  Proof with simpl in *.
    unfold Vscalar, Vmult.
    induction l1; destruct l2; simpl in *; congruence || auto...
    intros. inversion H. f_equal; [field|auto].
  Qed.

  Definition list_GAlg : @GAlgebra R (list R) (@length R) R_Field :=
    mkGAlg (@length R) R_Field V0 V1 Vplus Vminus Vmult Vscalar
    V0_dim V1_dim Vplus_dim Vmult_dim Vscalar_dim Vminus_def
    Vplus_ident_l Vmult_ident_l Vplus_assoc Vplus_comm Vmult_assoc Vmult_comm
    Vplus_mult_distrib_l Vscalar_plus_distrib Vscalar_zero Rplus_scalar_distrib
    Rmult_scalar_comm Vscalar_one Vscalar_mult_comm_l.

  Infix "+^" := Vplus (at level 50, left associativity).
  Infix "*^" := Vmult (at level 40, left associativity).
  Infix "-^" := Vminus (at level 50, left associativity).
  Infix ".^" := Vscalar (at level 45, no associativity).

  Goal forall k1 k2 v1 v2 n, length v1 = n -> length v2 = n ->
    (k1 .^ v1) +^ k2 .^ (v1 *^ v2) +^ (k2 - k1) .^ v1 = (k2 .^ v1) *^ v2 +^ k2 .^ v1.
  Proof.
    intros.
    galgebra n list_GAlg. all: simpl; firstorder.
  Qed.

  Goal forall v1 v2 n, length v1 = S n -> length v2 = S n ->
    v1 = v2 +^ (v1 -^ v2).
  Proof.
    intros.
    galgebra (S n) list_GAlg. firstorder.
  Qed.
End ListSample.