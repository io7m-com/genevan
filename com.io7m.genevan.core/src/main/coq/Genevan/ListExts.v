Require Coq.Lists.List.
Require Coq.Lists.SetoidList.

Theorem InA_In : forall (A : Type) (x : A) (xs : list A),
  SetoidList.InA (@eq _) x xs -> List.In x xs.
Proof.
  induction xs as [|y ys]. {
    intros H_in.
    inversion H_in.
  } {
    intros H_in.
    inversion H_in.
    subst; simpl in *; auto.
    subst; simpl in *; auto.
  }
Qed.

Lemma InMapPair : forall (A B : Type) (x : A) (y : B) es,
  List.In (x, y) es ->
    List.In x (List.map fst es) /\ List.In y (List.map snd es).
Proof.
  induction es as [|f fs]. {
    intros H_f0.
    inversion H_f0.
  } {
    intros H_in0.
    destruct H_in0 as [H_inL|H_inR]. {
      constructor; (left; destruct f as [f0 f1]; rewrite H_inL; reflexivity).
    } {
      constructor; (right; destruct (IHfs H_inR) as [H0 H1]; auto).
    }
  }
Qed.
