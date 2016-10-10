Require Import Semigroup.
Set Implicit Arguments.

Section Sample.
  Variable A : Type.
  Variable bot : A.
  Variable Aplus : A -> A -> A.
  Infix "+!" := Aplus (at level 50, left associativity).
  Variable Aplus_assoc : forall x y z : A, (x +! y) +! z = x +! (y +! z).
  Variable Aplus_comm : forall x y, x +! y = y +! x.

  Definition Acsg :=
    {| CSelem := bot;
       CSplus := Aplus;
       CSplus_assoc := Aplus_assoc;
       CSplus_comm := Aplus_comm; |}.

  Goal forall x y z, (x +! y) +! z = y +! (z +! x).
  Proof.
    intros.
    semigroup Acsg.
  Qed.

  Goal forall x y z w, (x +! y) +! (z +! w) = w +! (x +! z) +! y.
  Proof.
    intros.
    semigroup Acsg.
  Qed.

  Goal forall x y z, x +! y +! x +! z = x +! x +! y +! z.
  Proof.
    intros.
    semigroup Acsg.
  Qed.

  Goal forall x y z w,
    (x +! y) +! (x +! z +! (w +! y) +! w) = w +! w +! z +! y +! y+! x +! x.
  Proof.
    intros.
    semigroup Acsg.
  Qed.
End Sample.