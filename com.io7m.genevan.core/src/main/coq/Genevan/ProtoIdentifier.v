Require Coq.Structures.Equalities.
Require Coq.Strings.String.

Require Genevan.ProtoVersion.
Require Genevan.ProtoName.

Record t := {
  name    : ProtoName.t;
  version : ProtoVersion.t;
}.

Module Dec : Equalities.UsualDecidableType 
  with Definition t := t.

  Definition t := t.
  Definition eq       := @Logic.eq t.
  Definition eq_refl  := @Logic.eq_refl t.
  Definition eq_sym   := @Logic.eq_sym t.
  Definition eq_trans := @Logic.eq_trans t.

  #[local]
  Instance eq_equiv : RelationClasses.Equivalence eq := { }.

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    intros x y.
    destruct (String.string_dec (name x) (name y)) as [HnL|HnR]. {
      destruct (ProtoVersion.Ord.eq_dec (version x) (version y)) as [HvL|HvR]. {
        left.
        destruct x as [xn xv].
        destruct y as [yn yv].
        simpl in *.
        rewrite HnL in *.
        rewrite HvL in *.
        reflexivity.
      } {
        destruct x as [xn xv].
        destruct y as [yn yv].
        simpl in *.
        subst xn.
        right.
        unfold not; intro Hcontra; simpl in *.
        assert (xv = yv) by congruence.
        contradiction.
      }
    } {
      destruct x as [xn xv].
      destruct y as [yn yv].
      simpl in *.
      right.
      unfold not; intro Hcontra; simpl in *.
      assert (xn = yn) by congruence.
      contradiction.
    }
  Qed.

End Dec.

Definition isCompatibleWith (x y : t) : Prop :=
  name x = name y /\ ProtoVersion.isCompatibleWith (version x) (version y).

Theorem isCompatibleWith_reflexive : forall x,
  isCompatibleWith x x.
Proof.
  intro x.
  constructor.
  reflexivity.
  apply ProtoVersion.isCompatibleWith_reflexive.
Qed.

Theorem isCompatibleWith_symmetric : forall x y,
  isCompatibleWith x y -> isCompatibleWith y x.
Proof.
  intros x y [Hxy0 Hxy1].
  constructor.
  symmetry; exact Hxy0.
  apply (ProtoVersion.isCompatibleWith_symmetric _ _ Hxy1).
Qed.

Theorem isCompatibleWith_transitive : forall x y z,
  isCompatibleWith x y -> isCompatibleWith y z -> isCompatibleWith x z.
Proof.
  intros x y z [Hxy0 Hxy1] [Hyz0 Hyz1].
  constructor.
  - rewrite Hxy0.
    exact Hyz0.
  - apply (ProtoVersion.isCompatibleWith_transitive _ _ _ Hxy1 Hyz1).
Qed.

Theorem isCompatibleWith_Eq : RelationClasses.Equivalence isCompatibleWith.
Proof.
  constructor.
  exact isCompatibleWith_reflexive.
  exact isCompatibleWith_symmetric.
  exact isCompatibleWith_transitive.
Qed.
