
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