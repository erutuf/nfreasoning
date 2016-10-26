Require Import List Field PeanoNat Arith.
Require Import Substq GAlgebra.
Set Implicit Arguments.

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

Goal forall (x y z : G)(k l : K)(n : nat), (forall w, In w (x :: y :: z :: nil) -> dim w = n) ->
  k .^ x *^ y +^ l .^ x +^ y *^ z = y *^ z +^ (k .^ x *^ y +^ l .^ x).
  intros.
  galgebra n G_GAlg.
  all: repeat rewrite H; firstorder.
Qed.
