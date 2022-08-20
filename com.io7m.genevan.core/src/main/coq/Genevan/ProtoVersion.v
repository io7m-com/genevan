Require Coq.Structures.Orders.
Require Coq.Classes.RelationClasses.
Require Coq.Arith.Compare_dec.
Require Coq.Arith.PeanoNat.

(** * Protocol Version *)

(** A _protocol version_ encodes the version number of a _semantically-versioned_
    protocol, consisting of a _major_ and _minor_ version. The _minor_ version
    is incremented on compatible changes, and the _major_ version is
    incremented on incompatible changes. *)

Record t := {
  major : nat;
  minor : nat
}.

(** A protocol version _x_ is defined to be _compatible_ with a protocol
    version _y_ if the major versions are equal. The basic assumption is that
    any peer that supports major version _M_ of a protocol _P_ can speak to any
    other peer that supports major version _M_ of _P_, regardless of the minor
    version supported by either peer. *)

Definition isCompatibleWith (x y : t) : Prop :=
  (major x) = (major y).

(** The _isCompatibleWith_ relation is reflexive. *)

Theorem isCompatibleWith_reflexive : forall x, isCompatibleWith x x.
Proof. intro x. apply eq_refl. Qed.

(** The _isCompatibleWith_ relation is symmetric. *)

Theorem isCompatibleWith_symmetric : forall x y,
  isCompatibleWith x y -> isCompatibleWith y x.
Proof.
  intros x y Hxy.
  apply eq_sym.
  exact Hxy.
Qed.

(** The _isCompatibleWith_ relation is transitive. *)

Theorem isCompatibleWith_transitive : forall x y z,
  isCompatibleWith x y -> isCompatibleWith y z -> isCompatibleWith x z.
Proof.
  unfold isCompatibleWith.
  intros x y z Hxy Hyz.
  rewrite Hxy.
  exact Hyz.
Qed.

(** The _isCompatibleWith_ relation is therefore an equivalence relation. *)

#[local]
Instance isCompatibleWith_Eq : RelationClasses.Equivalence isCompatibleWith.
Proof.
  constructor.
  exact isCompatibleWith_reflexive.
  exact isCompatibleWith_symmetric.
  exact isCompatibleWith_transitive.
Qed.

(** Protocol versions are ordered. *)

Module Ord : Orders.UsualOrderedType
  with Definition t := t.

  Definition t := t.
  Definition eq (x y : t) := x = y.

  Definition eq_refl  := @Logic.eq_refl t.
  Definition eq_sym   := @Logic.eq_sym t.
  Definition eq_trans := @Logic.eq_trans t.

  (** For a protocol version _x_ to be _less than_ a protocol version _y_,
      either the major version of _x_ is less than the major version of _y_,
      or the major versions of _x_ and _y_ are equal and the minor version of
      _x_ is less than the minor version of _y_. *)

  Definition lt (x y : t) : Prop :=
    major x < major y \/ (major x = major y /\ minor x < minor y).

  #[local]
  Instance lt_is_irreflexive : RelationClasses.Irreflexive lt.
  Proof.
    hnf; intro x; hnf.
    unfold lt.
    intro Hc.
    destruct Hc as [HcL|[HcR0 HcR1]].
    - pose proof (PeanoNat.Nat.lt_irrefl (major x)); contradiction.
    - pose proof (PeanoNat.Nat.lt_irrefl (minor x)); contradiction.
  Qed.

  #[local]
  Instance lt_is_transitive : RelationClasses.Transitive lt.
  Proof.
    hnf; intro x; hnf.
    unfold lt.
    intros y z [HxyL|[HxyR0 HxyR1]] [HyzL|[HyzR0 HyzR1]].
    - left; apply (PeanoNat.Nat.lt_trans _ _ _ HxyL HyzL).
    - rewrite HyzR0 in *; left; auto.
    - rewrite HxyR0 in *; left; auto.
    - right. 
      constructor.
      * rewrite HxyR0 in *; exact HyzR0.
      * apply (PeanoNat.Nat.lt_trans _ _ _ HxyR1 HyzR1).
  Qed.

  #[local]
  Instance lt_strorder : RelationClasses.StrictOrder lt := { }.

  #[local]
  Instance eq_equiv : RelationClasses.Equivalence eq := { }.

  Theorem lt_compat : Morphisms.Proper (Morphisms.respectful Logic.eq (Morphisms.respectful Logic.eq iff)) lt.
  Proof.
    unfold Morphisms.Proper.
    unfold Morphisms.respectful.
    intros x y Heq0 x0 y0 Heq1.
    rewrite Heq0.
    rewrite Heq1.
    constructor; tauto.
  Qed.

  Definition compare (x y : t) : comparison :=
    match Nat.compare (major x) (major y) with
    | Eq => Nat.compare (minor x) (minor y)
    | Lt => Lt
    | Gt => Gt
    end.

  Definition compare_spec : forall x y : t, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros x y.
    destruct (compare x y) eqn:Hcomp. {
      apply CompEq.
      unfold compare in Hcomp.
      destruct (Nat.compare (major x) (major y)) eqn:Hmajxy. {
        pose proof (Compare_dec.nat_compare_eq _ _ Hmajxy) as H0.
        pose proof (Compare_dec.nat_compare_eq _ _ Hcomp) as H1.
        destruct x as [xM xm].
        destruct y as [yM ym].
        auto.
      } {
        contradict Hcomp; discriminate.
      } {
        contradict Hcomp; discriminate.
      }
    } {
      apply CompLt.
      unfold compare in Hcomp.
      destruct (Nat.compare (major x) (major y)) eqn:Hmajxy. {
        pose proof (Compare_dec.nat_compare_eq _ _ Hmajxy) as H0.
        rewrite <- Compare_dec.nat_compare_lt in Hcomp.
        right; constructor; auto.
      } {
        rewrite <- Compare_dec.nat_compare_lt in Hmajxy.
        left; auto.
      } {
        contradict Hcomp; discriminate.
      }
    } {
      apply CompGt.
      unfold compare in Hcomp.
      destruct (Nat.compare (major x) (major y)) eqn:Hmajxy. {
        pose proof (Compare_dec.nat_compare_eq _ _ Hmajxy) as H0.
        pose proof (Compare_dec.nat_compare_Gt_gt _ _ Hcomp) as H1.
        unfold gt in H1.
        right; constructor.
        symmetry; auto.
        auto.
      } {
        contradict Hcomp; discriminate.
      } {
        pose proof (Compare_dec.nat_compare_Gt_gt _ _ Hmajxy) as H0.
        unfold gt in H0.
        left; auto.
      }
    }
  Qed.

  (** Protocol versions have decidable equality. *)

  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
  Proof.
    destruct x as [xM xm].
    destruct y as [yM ym].
    destruct (PeanoNat.Nat.eq_dec xM yM) as [HML|HMR]. {
      destruct (PeanoNat.Nat.eq_dec xm ym) as [HmL|HmR]. {
        subst xM.
        subst xm.
        left; reflexivity.
      } {
        right. intro Hc. assert (xm = ym) as H0 by congruence. contradiction.
      }
    } {
      right. intro Hc. assert (xM = yM) as H0 by congruence. contradiction.
    }
  Qed.

End Ord.
