Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersTac.

Import ListNotations.

Definition ProtoName := string.

Inductive ProtoVersion := {
  prMajor : nat;
  prMinor : nat
}.

Inductive ProtoIdentifier := {
  prName    : ProtoName;
  prVersion : ProtoVersion
}.

Module Type ComparableRequirements := Typ <+ HasEq <+ HasLt <+ HasCompare.

Module Type ComparableRelations (Import E : ComparableRequirements).
  Parameter eq_compare      : forall x y, compare x y = Eq <-> x = y.
  Parameter lt_compare      : forall x y, compare x y = Lt <-> lt x y.
  Parameter gt_compare      : forall x y, compare x y = Gt <-> lt y x.
  Parameter lt_gt_compare   : forall x y, compare x y = Lt <-> compare y x = Gt.
End ComparableRelations.

Module Type BigOrder := UsualTotalOrder <+ HasCompare <+ ComparableRelations.

Module ProtoVersionOrd <: BigOrder.

  Definition t                         := ProtoVersion.
  Definition eq (x y : ProtoVersion)   := x = y.

  Definition protoVersionCmp (p0 p1 : ProtoVersion) : comparison :=
    match Nat.compare (prMajor p0) (prMajor p1) with
    | Eq => Nat.compare (prMinor p0) (prMinor p1)
    | Lt => Lt
    | Gt => Gt
    end.

  Definition compare                   := protoVersionCmp.
  Definition lt (p0 p1 : ProtoVersion) := protoVersionCmp p0 p1 = Lt.
  Definition le (p0 p1 : ProtoVersion) := lt p0 p1 \/ p0 = p1.

  Definition eq_dec : forall (x y : ProtoVersion),
    {x = y}+{x <> y}.
  Proof.
    decide equality.
    apply Nat.eq_dec.
    apply Nat.eq_dec.
  Qed.

  #[export]
  Instance eq_equiv : Equivalence eq := { }.

  Inductive ProtoVersionCmpLtCases : ProtoVersion -> ProtoVersion -> Prop :=
    | PVCMajorLt : forall p0 p1,
      Nat.compare (prMajor p0) (prMajor p1) = Lt ->
        ProtoVersionCmpLtCases p0 p1
    | PVCMinorLt : forall p0 p1,
      (prMajor p0) = (prMajor p1) ->
        Nat.compare (prMinor p0) (prMinor p1) = Lt ->
          ProtoVersionCmpLtCases p0 p1.

  Theorem protoVersionCmpLtCases : forall p0 p1,
    protoVersionCmp p0 p1 = Lt -> ProtoVersionCmpLtCases p0 p1.
  Proof.
    intros p0 p1 H0.
    unfold protoVersionCmp in H0.
    destruct (prMajor p0 ?= prMajor p1) eqn:Hmaj. {
      destruct (prMinor p0 ?= prMinor p1) eqn:Hmin. {
        contradict H0; discriminate.
      } {
        apply PVCMinorLt.
        rewrite Nat.compare_eq_iff in Hmaj.
        exact Hmaj.
        exact Hmin.
      } {
        contradict H0; discriminate.
      }
    } {
      apply PVCMajorLt.
      exact Hmaj.
    } {
      contradict H0; discriminate.
    }
  Qed.

  Definition eq_compare0 : forall p0 p1, protoVersionCmp p0 p1 = Eq -> p0 = p1.
  Proof.
    intros p0 p1 Hceq.
    unfold protoVersionCmp in Hceq.
    destruct (prMajor p0 ?= prMajor p1) eqn:Hmaj. {
      rewrite Nat.compare_eq_iff in *.
      destruct p0 as [p0M p0m].
      destruct p1 as [p1M p1m].
      intuition.
    } {
      contradict Hceq; discriminate.
    } {
      contradict Hceq; discriminate.
    }
  Qed.

  Definition eq_compare1 : forall p0 p1, p0 = p1 -> protoVersionCmp p0 p1 = Eq.
  Proof.
    intros p0 p1 Hceq.
    rewrite Hceq.
    unfold protoVersionCmp.
    rewrite Nat.compare_refl.
    rewrite Nat.compare_refl.
    reflexivity.
  Qed.

  Definition eq_compare : forall p0 p1, protoVersionCmp p0 p1 = Eq <-> p0 = p1.
  Proof.
    intros p0 p1.
    constructor.
    apply eq_compare0.
    apply eq_compare1.
  Qed.

  #[local]
  Instance lt_is_irreflexive : Irreflexive lt.
  Proof.
    unfold Irreflexive.
    unfold Reflexive.
    unfold complement.
    unfold lt.
    unfold protoVersionCmp.
    intros x.
    assert (forall y, Nat.compare y y = Eq) as Hneq. {
      intros y.
      destruct (Nat.compare_eq_iff y y) as [Hz0 Hz1].
      assert (y = y) as Hyeqy by (apply eq_refl).
      apply (Hz1 Hyeqy).
    }
    rewrite (Hneq (prMajor x)).
    rewrite (Hneq (prMinor x)).
    intro Hcontra; contradict Hcontra; discriminate.
  Qed.

  #[local]
  Instance lt_is_transitive : Transitive lt.
  Proof.
    unfold Transitive.
    unfold lt.
    intros x y z Hxy Hyz.
    pose proof (protoVersionCmpLtCases x y Hxy) as Hxyc.
    pose proof (protoVersionCmpLtCases y z Hyz) as Hyzc.
    unfold protoVersionCmp.

    destruct Hxyc as [
        p0 p1 H_xyc_major_lt
      | p2 p3 H_xyc_major_eq H_xyc_minor_lt
    ]. {
      destruct Hyzc as [
          p1 p2 H_yzc_major_lt
        | p1 p2 H_yzc_major_eq H_yzc_minor_lt
      ]. {
        rewrite <- Compare_dec.nat_compare_lt in H_xyc_major_lt.
        rewrite <- Compare_dec.nat_compare_lt in H_yzc_major_lt.
        assert (prMajor p0 < prMajor p2) as H_p0p2
          by (apply (Nat.lt_trans _ _ _ H_xyc_major_lt H_yzc_major_lt)).
        rewrite Compare_dec.nat_compare_lt in H_p0p2.
        rewrite H_p0p2.
        reflexivity.
      } {
        rewrite H_yzc_major_eq in H_xyc_major_lt.
        rewrite H_xyc_major_lt.
        reflexivity.
      }
    } {
      destruct Hyzc as [
          p3 p4 H_yzc_major_lt
        | p3 p4 H_yzc_major_eq H_yzc_minor_lt
      ]. {
        rewrite <- H_xyc_major_eq in H_yzc_major_lt.
        rewrite H_yzc_major_lt.
        reflexivity.
      } {
        rewrite <- H_xyc_major_eq in H_yzc_major_eq.
        rewrite <- H_yzc_major_eq.
        rewrite Nat.compare_refl.
        rewrite <- Compare_dec.nat_compare_lt in *.
        apply (Nat.lt_trans _ _ _ H_xyc_minor_lt H_yzc_minor_lt).
      }
    }
  Qed.

  #[export]
  Instance lt_strorder : StrictOrder lt := {

  }.

  #[export]
  Instance lt_compat : Proper (Logic.eq ==> Logic.eq ==> iff) lt.
  Proof.
    unfold Proper.
    unfold respectful.
    intros x y Heq0 x0 y0 Heq1.
    rewrite Heq0.
    rewrite Heq1.
    constructor; tauto.
  Qed.

  Definition le_lteq : forall p0 p1, le p0 p1 <-> lt p0 p1 \/ p0 = p1.
  Proof.
    intros p0 p1.
    constructor.
    intro Hle.
    destruct Hle as [Hle0|Hle1].
      left; auto.
      right; auto.
    intro Hlteq.
    destruct Hlteq as [Hlteq0|Hlteq1].
      left; auto.
      right; auto.
  Qed.

  Definition lt_total : forall p0 p1, lt p0 p1 \/ p0 = p1 \/ lt p1 p0.
  Proof.
    intros p0 p1.
    unfold lt.
    destruct (protoVersionCmp p0 p1) eqn:Hcomp. {
      right. left.
      apply (eq_compare0 _ _ Hcomp).
    } {
      left; reflexivity.
    } {
      right. right.
      unfold protoVersionCmp in *.
      destruct (prMajor p0 ?= prMajor p1) eqn:Hmaj. {
        rewrite Nat.compare_eq_iff in Hmaj.
        rewrite Hmaj.
        rewrite Nat.compare_refl.
        rewrite Nat.compare_lt_iff.
        rewrite Nat.compare_gt_iff in Hcomp.
        intuition.
      } {
        contradict Hcomp; discriminate.
      } {
        rewrite Nat.compare_gt_iff in Hmaj.
        assert (prMajor p1 ?= prMajor p0 = Lt) as Hlt. {
          rewrite Nat.compare_lt_iff.
          intuition.
        }
        rewrite Hlt.
        reflexivity.
      }
    }
  Qed.

  Definition lt_compare0 : forall p0 p1, protoVersionCmp p0 p1 = Lt -> lt p0 p1.
  Proof.
    intros p0 p1 Hlt.
    exact Hlt.
  Qed.

  Definition lt_compare1 : forall p0 p1, lt p0 p1 -> protoVersionCmp p0 p1 = Lt.
  Proof.
    intros p0 p1 Hlt.
    exact Hlt.
  Qed.

  Definition lt_compare : forall x y, compare x y = Lt <-> lt x y.
  Proof.
    constructor.
    apply lt_compare1.
    apply lt_compare0.
  Qed.

  Definition gt_compare0 : forall p0 p1, protoVersionCmp p0 p1 = Gt -> lt p1 p0.
  Proof.
    intros p0 p1 Hlt.
    unfold lt.
    unfold protoVersionCmp.
    unfold protoVersionCmp in Hlt.
    destruct (prMajor p0 ?= prMajor p1) eqn:Hmaj. {
      rewrite Nat.compare_eq_iff in Hmaj.
      rewrite Nat.compare_gt_iff in Hlt.
      rewrite Hmaj in *.
      rewrite Nat.compare_refl.
      rewrite Nat.compare_lt_iff.
      exact Hlt.
    } {
      contradict Hlt; discriminate.
    } {
      rewrite Nat.compare_gt_iff in Hmaj.
      rewrite <- Nat.compare_lt_iff in Hmaj.
      rewrite Hmaj.
      reflexivity.
    }
  Qed.

  Definition gt_compare1 : forall p0 p1, lt p1 p0 -> protoVersionCmp p0 p1 = Gt.
  Proof.
    intros p0 p1 Hlt.
    unfold lt in Hlt.

    destruct (protoVersionCmpLtCases _ _ Hlt) as [
        p0 p1 H_major_lt
      | p2 p3 H_major_eq H_minor_lt
    ]. {
      unfold protoVersionCmp.
      destruct (prMajor p1 ?= prMajor p0) eqn:Hmaj. {
        rewrite Nat.compare_eq_iff in *.
        rewrite Nat.compare_lt_iff in *.
        rewrite Hmaj in *.
        contradict H_major_lt.
        apply Nat.lt_irrefl.
      } {
        rewrite Nat.compare_lt_iff in *.
        contradict H_major_lt.
        apply (Nat.lt_asymm _ _ Hmaj).
      } {
        reflexivity.
      }
    } {
      unfold protoVersionCmp.
      symmetry in H_major_eq.
      rewrite <- Nat.compare_eq_iff in H_major_eq.
      rewrite H_major_eq.
      rewrite Nat.compare_gt_iff.
      rewrite Nat.compare_lt_iff in H_minor_lt.
      exact H_minor_lt.
    }
  Qed.

  Definition gt_compare : forall x y, compare x y = Gt <-> lt y x.
  Proof.
    constructor.
    apply gt_compare0.
    apply gt_compare1.
  Qed.

  Definition lt_gt_compare : forall x y, compare x y = Lt <-> compare y x = Gt.
  Proof.
    intros x y.
    unfold compare in *.
    constructor. {
      intros Hlt.
      unfold protoVersionCmp in *.
      destruct (prMajor x ?= prMajor y) eqn:Hmaj. {
        rewrite Nat.compare_eq_iff in Hmaj.
        symmetry in Hmaj.
        rewrite <- Nat.compare_eq_iff in Hmaj.
        rewrite Hmaj.
        rewrite Nat.compare_lt_iff in Hlt.
        rewrite Nat.compare_gt_iff.
        exact Hlt.
      } {
        rewrite Nat.compare_lt_iff in Hmaj.
        rewrite <- Nat.compare_gt_iff in Hmaj.
        rewrite Hmaj.
        reflexivity.
      } {
        contradict Hlt; discriminate.
      }
    } {
      intros Hlt.
      unfold protoVersionCmp in *.
      destruct (prMajor y ?= prMajor x) eqn:Hmaj. {
        rewrite Nat.compare_eq_iff in Hmaj.
        symmetry in Hmaj.
        rewrite <- Nat.compare_eq_iff in Hmaj.
        rewrite Hmaj.
        rewrite Nat.compare_gt_iff in Hlt.
        rewrite <- Nat.compare_lt_iff in Hlt.
        exact Hlt.
      } {
        contradict Hlt; discriminate.
      } {
        rewrite Nat.compare_gt_iff in Hmaj.
        rewrite <- Nat.compare_lt_iff in Hmaj.
        rewrite Hmaj.
        reflexivity.
      }
    }
  Qed.

  Definition compare_spec : forall x y, CompareSpec (x = y) (lt x y) (lt y x) (compare x y).
  Proof.
    intros x y.
    destruct (compare x y) eqn:Hcomp. {
      apply CompEq.
      rewrite eq_compare in Hcomp.
      exact Hcomp.
    } {
      apply CompLt.
      rewrite lt_compare in Hcomp.
      exact Hcomp.
    } {
      apply CompGt.
      rewrite gt_compare in Hcomp.
      exact Hcomp.
    }
  Qed.

End ProtoVersionOrd.

Module Type MaxType (Ord : BigOrder).
  Parameter max             : forall x y : Ord.t, Ord.t.
  Parameter max_idempotent  : forall x, max x x = x.
  Parameter max_commutative : forall x y, max x y = max y x.
  Parameter max_associative : forall x y z, max (max x y) z = max x (max y z).
  Parameter max_order       : forall x y, max x y = y <-> Ord.lt x y \/ x = y.
  Parameter max_le          : forall x y, Ord.le x (max x y).
  Parameter max_either      : forall x y z, max x y = z -> z = x \/ z = y.
  Parameter max_le_trans    : forall x y z, Ord.le x y -> Ord.le x (max y z).
End MaxType.

Module Max (Ord : BigOrder) <: MaxType Ord.

  Definition max (x y : Ord.t) : Ord.t :=
    match Ord.compare x y with
    | Eq => x
    | Lt => y
    | Gt => x
    end.

  Theorem max_idempotent : forall x, max x x = x.
  Proof.
    intro x.
    unfold max.
    assert (x = x) as Hx by reflexivity.
    rewrite <- Ord.eq_compare in Hx.
    rewrite Hx.
    reflexivity.
  Qed.

  Theorem max_commutative : forall x y, max x y = max y x.
  Proof.
    intros x y.
    unfold max.
    destruct (Ord.compare x y) eqn:Hcomp. {
      assert (Ord.compare y x = Eq) as Hcompsym. {
        rewrite Ord.eq_compare.
        symmetry.
        rewrite <- Ord.eq_compare.
        exact Hcomp.
      }
      rewrite Hcompsym.
      rewrite Ord.eq_compare in Hcomp.
      exact Hcomp.
    } {
      rewrite Ord.lt_gt_compare in Hcomp.
      rewrite Hcomp.
      reflexivity.
    } {
      rewrite <- Ord.lt_gt_compare in Hcomp.
      rewrite Hcomp.
      reflexivity.
    }
  Qed.

  Theorem max_associative : forall x y z, max (max x y) z = max x (max y z).
  Proof.
    intros x y z.
    unfold max.
    destruct (Ord.compare x y) eqn:Hcompxy. {
      destruct (Ord.compare x z) eqn:Hcompxz. {
        destruct (Ord.compare y z) eqn:Hcompyz. {
          rewrite Hcompxy.
          reflexivity.
        } {
          rewrite Hcompxz.
          reflexivity.
        } {
          rewrite Hcompxy.
          reflexivity.
        }
      } {
        destruct (Ord.compare y z) eqn:Hcompyz. {
          rewrite Hcompxy.
          rewrite Ord.eq_compare in *.
          rewrite Hcompxy in *.
          rewrite Hcompyz in *.
          reflexivity.
        } {
          rewrite Hcompxz.
          reflexivity.
        } {
          rewrite Hcompxy.
          rewrite Ord.eq_compare in *.
          rewrite Hcompxy in *.
          rewrite Hcompyz in Hcompxz.
          contradict Hcompxz; discriminate.
        }
      } {
        destruct (Ord.compare y z) eqn:Hcompyz. {
          rewrite Hcompxy.
          reflexivity.
        } {
          rewrite Hcompxz.
          reflexivity.
        } {
          rewrite Hcompxy.
          reflexivity.
        }
      }
    } {
      destruct (Ord.compare y z) eqn:Hcompyz. {
        rewrite Hcompxy.
        reflexivity.
      } {
        destruct (Ord.compare x z) eqn:Hcompxz. {
          rewrite Ord.eq_compare in *.
          symmetry.
          exact Hcompxz.
        } {
          reflexivity.
        } {
          assert (Ord.compare x z = Lt) as Hcontra. {
            pose proof (Ord.lt_strorder) as H.
            destruct H as [H_irrefl H_trans].
            unfold Transitive in H_trans.
            rewrite Ord.lt_compare in *.
            apply (H_trans _ _ _ Hcompxy Hcompyz).
          }
          rewrite Hcompxz in Hcontra.
          contradict Hcontra; discriminate.
        }
      } {
        rewrite Hcompxy.
        reflexivity.
      }
    } {
      destruct (Ord.compare x z) eqn:Hcompxz. {
        destruct (Ord.compare y z) eqn:Hcompyz. {
          rewrite Hcompxy.
          reflexivity.
        } {
          rewrite Hcompxz.
          reflexivity.
        } {
          rewrite Hcompxy.
          reflexivity.
        }
      } {
        destruct (Ord.compare y z) eqn:Hcompyz. {
          rewrite Hcompxy.
          rewrite Ord.eq_compare in Hcompyz.
          rewrite Hcompyz in *.
          rewrite Hcompxz in Hcompxy.
          contradict Hcompxy; discriminate.
        } {
          rewrite Hcompxz.
          reflexivity.
        } {
          rewrite Ord.gt_compare in *.
          rewrite <- Ord.lt_compare in *.
          assert (Ord.compare y z = Lt) as Hcontra. {
            pose proof (Ord.lt_strorder) as H.
            destruct H as [H_irrefl H_trans].
            unfold Transitive in H_trans.
            rewrite Ord.lt_compare in *.
            apply (H_trans _ _ _ Hcompxy Hcompxz).
          }
          rewrite Ord.lt_compare in Hcontra.
          rewrite <- Ord.gt_compare in Hcontra.
          rewrite Hcompyz in Hcontra.
          contradict Hcontra; discriminate.
        }
      } {
        destruct (Ord.compare y z) eqn:Hcompyz. {
          rewrite Hcompxy.
          reflexivity.
        } {
          rewrite Hcompxz.
          reflexivity.
        } {
          rewrite Hcompxy.
          reflexivity.
        }
      }
    }
  Qed.

  Theorem max_order0 : forall x y, max x y = y -> Ord.lt x y \/ x = y.
  Proof.
    unfold max.
    intros x y Heq.
    destruct (Ord.compare x y) eqn:Hcomp. {
      right; exact Heq.
    } {
      rewrite Ord.lt_compare in Hcomp.
      left; exact Hcomp.
    } {
      right; exact Heq.
    }
  Qed.

  Theorem max_order1 : forall x y, Ord.lt x y \/ x = y -> max x y = y.
  Proof.
    unfold max.
    intros x y Heq.
    destruct Heq as [Hlt|Heq]. {
      destruct (Ord.compare x y) eqn:Hcomp. {
        rewrite <- Ord.lt_compare in Hlt.
        rewrite Hlt in Hcomp.
        contradict Hcomp; discriminate.
      } {
        reflexivity.
      } {
        rewrite <- Ord.lt_compare in Hlt.
        rewrite Hlt in Hcomp.
        contradict Hcomp; discriminate.
      }
    } {
      rewrite <- Ord.eq_compare in Heq.
      rewrite Heq.
      rewrite Ord.eq_compare in Heq.
      exact Heq.
    }
  Qed.

  Theorem max_order : forall x y, max x y = y <-> Ord.lt x y \/ x = y.
  Proof.
    intros x y.
    constructor.
    apply max_order0.
    apply max_order1.
  Qed.

  Theorem max_le : forall x y, Ord.le x (max x y).
  Proof.
    intros x y.
    unfold max.
    destruct (Ord.compare x y) eqn:Hxy. {
      rewrite Ord.le_lteq.
      right; reflexivity.
    } {
      rewrite Ord.lt_compare in Hxy.
      rewrite Ord.le_lteq.
      left; exact Hxy.
    } {
      rewrite Ord.le_lteq.
      right; reflexivity.
    }
  Qed.

  Theorem max_either : forall x y z, max x y = z -> z = x \/ z = y.
  Proof.
    intros x y z Hmax.
    unfold max in Hmax.
    destruct (Ord.compare x y) eqn:Hxy. {
      left; symmetry; exact Hmax.
    } {
      right; symmetry; exact Hmax.
    } {
      left; symmetry; exact Hmax.
    }
  Qed.

  Theorem lt_trans : forall x y z, Ord.lt x y -> Ord.lt y z -> Ord.lt x z.
  Proof.
    destruct (Ord.lt_strorder) as [H_irr H_trans].
    unfold Transitive in H_trans.
    exact H_trans.
  Qed.

  Theorem max_le_trans : forall x y z, Ord.le x y -> Ord.le x (max y z).
  Proof.
    intros x y z Hle.
    rewrite Ord.le_lteq in *.
    unfold max.
    destruct (Ord.compare y z) eqn:Hyz. {
      rewrite Ord.eq_compare in Hyz.
      subst z.
      exact Hle.
    } {
      rewrite Ord.lt_compare in Hyz.
      destruct Hle as [Hle0|Hle1]. {
        left; apply (lt_trans _ _ _ Hle0 Hyz).
      } {
        subst x.
        left; exact Hyz.
      }
    } {
      exact Hle.
    }
  Qed.

End Max.

Module Type MaxListsType (Ord : BigOrder).
  Parameter maxList            : list Ord.t -> option Ord.t.
  Parameter maxSpec            : forall xs y, maxList xs = Some y -> Forall (fun k => Ord.le k y) xs.
  Parameter maxListNoneImplies : forall x, maxList x = None <-> x = [].
  Parameter maxListExists      : forall x, x <> [] <-> exists y, maxList x = Some y.
  Parameter maxListIn          : forall xs x, maxList xs = (Some x) -> In x xs.
End MaxListsType.

Module MaxLists (Ord : BigOrder) (M : MaxType Ord) <: MaxListsType Ord.

  Fixpoint maxList
    (xs : list Ord.t)
  : option Ord.t :=
    match xs with
    | []      => None
    | y :: ys =>
      match maxList ys with
      | None   => Some y
      | Some w => Some (M.max y w)
      end
    end.

  Lemma maxListEmpty : maxList [] = None.
  Proof. reflexivity. Qed.

  Lemma maxListNoneImplies0 : forall x, maxList x = None -> x = [].
  Proof.
    intros x H_none.
    induction x as [|y ys]. {
      reflexivity.
    } {
      simpl in H_none.
      destruct (maxList ys) eqn:Heq. {
        contradict H_none; discriminate.
      } {
        contradict H_none; discriminate.
      }
    }
  Qed.

  Lemma maxListNoneImplies1 : forall x, x = [] -> maxList x = None.
  Proof.
    intros x H_none.
    rewrite H_none. reflexivity.
  Qed.

  Lemma maxListNoneImplies : forall x, maxList x = None <-> x = [].
  Proof.
    intros x.
    constructor.
    apply maxListNoneImplies0.
    apply maxListNoneImplies1.
  Qed.

  Lemma maxListExists0 : forall x, x <> [] -> exists y, maxList x = Some y.
  Proof.
    intros x H_nonempty.
    destruct x as [|y ys]. {
      contradict H_nonempty. reflexivity.
    } {
      simpl.
      destruct (maxList ys) eqn:Hm. {
        exists (M.max y t).
        reflexivity.
      } {
        exists y.
        reflexivity.
      }
    }
  Qed.

  Lemma maxListExists1 : forall x, (exists y, maxList x = Some y) -> x <> [].
  Proof.
    intros x H_nonempty.
    destruct x as [|y ys]. {
      simpl in H_nonempty.
      destruct H_nonempty as [w Hw].
      contradict Hw; discriminate.
    } {
      discriminate.
    }
  Qed.

  Lemma maxListExists : forall x, x <> [] <-> exists y, maxList x = Some y.
  Proof.
    intros x.
    constructor.
    apply maxListExists0.
    apply maxListExists1.
  Qed.

  Lemma lt_irrefl : forall x, ~Ord.lt x x.
  Proof.
    intros x.
    destruct (Ord.lt_strorder) as [HI HT].
    unfold Irreflexive in HI.
    unfold Reflexive in HI.
    unfold complement in HI.
    unfold not.
    intro Hcontra.
    apply (HI _ Hcontra).
  Qed.

  Theorem maxSpec : forall xs y,
    maxList xs = Some y ->
      Forall (fun k => Ord.le k y) xs.
  Proof.
    intros xs.
    induction xs as [|p ps]. {
      intros y Hcontra.
      contradict Hcontra; discriminate.
    } {
      intros y Hsome.
      simpl in Hsome.

      (*
        The recursive call will either return some value `w` that
        needs to be demonstrated to be greater than or equal to
        the rest of the elements in the list, or it will return
        nothing, in which case the existing list element `p` will
        be returned, and is clearly greater than or equal to nothing.

        match maxList ps with
        | Some w => Some (M.max p w)
        | None   => Some p
        end = Some y
      *)

      destruct (maxList ps) as [w|] eqn:Hmeq. {
        assert (M.max p w = y) as H_max_eq_y by congruence.
        constructor. {
          rewrite <- H_max_eq_y.
          apply M.max_le.
        } {
          (* We can prove that w is >= the rest of the list. *)
          assert (Forall (fun k : Ord.t => Ord.le k w) ps) as Hrest. {
            apply IHps.
            reflexivity.
          }
          (* So now we need to prove that w <= (max p w) and
             apply that to all elements of the list (Forall) *)
          subst y.
          assert (forall k, Ord.le k w -> Ord.le k (M.max p w)) as H_impl. {
            intros k H_k_le_w.
            rewrite M.max_commutative.
            apply (M.max_le_trans k w p H_k_le_w).
          }
          apply (Forall_impl _ H_impl Hrest).
        }
      } {
        rewrite maxListNoneImplies in Hmeq.
        subst ps.
        assert (p = y) as Heq by congruence.
        subst y.
        constructor.
        rewrite Ord.le_lteq.
        right; reflexivity.
        constructor.
      }
    }
  Qed.

  Theorem maxListIn : forall xs x, maxList xs = (Some x) -> In x xs.
  Proof.
    intros xs x H_some.
    induction xs as [|y ys]. {
      contradict H_some; discriminate.
    } {
      simpl in H_some.
      destruct (maxList ys) as [s|]. {
        assert (M.max y s = x) as Heq by (congruence).
        destruct (M.max_either _ _ _ Heq) as [HL|HR]. {
          subst y.
          left; reflexivity.
        } {
          right. apply IHys. f_equal. symmetry. exact HR.
        }
      } {
        assert (y = x) as Heq by congruence.
        subst y.
        left; reflexivity.
      }
    }
  Qed.

End MaxLists.

Definition isSupportedBy
  (x y : ProtoIdentifier)
: Prop :=
  (prName x) = (prName y) /\ (prMajor (prVersion x) = prMajor (prVersion y)).

Theorem isSupportedBySymmetric : forall x y, isSupportedBy x y -> isSupportedBy y x.
Proof.
  intros x y Hxy.
  destruct Hxy as [H0 H1].
  symmetry in H0.
  symmetry in H1.
  constructor.
  exact H0.
  exact H1.
Qed.

Theorem isSupportedByReflexive : forall x, isSupportedBy x x.
Proof.
  intros x.
  constructor; reflexivity.
Qed.

Theorem isSupportedByTransitive : forall x y z, isSupportedBy x y -> isSupportedBy y z -> isSupportedBy x z.
Proof.
  intros x y z Hxy Hyz.
  destruct Hxy as [Hxy0 Hxy1].
  destruct Hyz as [Hyz0 Hyz1].
  constructor.
  congruence.
  congruence.
Qed.

Theorem isSupportedByEquiv : Equivalence isSupportedBy.
Proof.
  constructor.
  exact isSupportedByReflexive.
  exact isSupportedBySymmetric.
  exact isSupportedByTransitive.
Qed.

Theorem isSupportedByDec
  (x y : ProtoIdentifier)
: {isSupportedBy x y}+{~isSupportedBy x y}.
Proof.
  destruct (string_dec (prName x) (prName y)) as [H_name_eq|H_name_neq]. {
    destruct (Nat.eq_dec (prMajor (prVersion x)) (prMajor (prVersion y))) as [H_ver_eq|H_ver_neq]. {
      left.
      constructor.
      exact H_name_eq.
      exact H_ver_eq.
    } {
      right.
      unfold not.
      intro Hcontra.
      inversion Hcontra.
      contradiction.
    }
  } {
    right.
    unfold not.
    intro Hcontra.
    inversion Hcontra.
    contradiction.
  }
Qed.

Definition isSupportedByAny
  (x  : ProtoIdentifier)
  (xs : list ProtoIdentifier)
: Prop :=
  Exists (isSupportedBy x) xs.

Theorem isSupportedByAnyDec
  (x  : ProtoIdentifier)
  (xs : list ProtoIdentifier)
: {isSupportedByAny x xs}+{~isSupportedByAny x xs}.
Proof.
  unfold isSupportedByAny.
  apply Exists_dec.
  apply isSupportedByDec.
Qed.

Theorem isSupportedByAnyFalse : forall x, ~isSupportedByAny x [].
Proof.
  intros x.
  unfold isSupportedByAny.
  rewrite Exists_nil.
  auto.
Qed.

Inductive Error :=
  | ErrorNoSolution
  | ErrorAmbiguous : list ProtoIdentifier -> Error.

Inductive Result (A : Set) : Set :=
  | Success : A     -> Result A
  | Failure : Error -> Result A.

Definition withoutUnsupported
  (serverSupports : list ProtoIdentifier)
  (clientSupports : list ProtoIdentifier)
: Result (list ProtoIdentifier) :=
  match filter (fun i => 
    match isSupportedByAnyDec i clientSupports with
    | left _  => true
    | right _ => false
    end
  ) serverSupports with
  | [] => Failure _ ErrorNoSolution
  | xs => Success _ xs
  end.

Lemma withoutUnsupportedFilterForallClient : forall ss cs,
  Forall (fun k => isSupportedByAny k cs) 
    (filter (fun i => match isSupportedByAnyDec i cs with
             | left _  => true
             | right _ => false
             end) ss).
Proof.
  intros ss.
  induction ss as [|y ys]. {
    intros cs.
    apply Forall_nil.
  } {
    intros cs.
    simpl.
    destruct (isSupportedByAnyDec y cs) as [Hs|Hns]. {
      constructor.
      exact Hs.
      apply IHys.
    } {
      apply IHys.
    }
  }
Qed.

Lemma withoutUnsupportedFilterForallServer : forall ss cs,
  Forall (fun k => isSupportedByAny k ss) 
    (filter (fun i => match isSupportedByAnyDec i cs with
             | left _  => true
             | right _ => false
             end) ss).
Proof.
  intros ss cs.
  induction ss as [|ss0 ssrest]. {
    constructor.
  } {
    simpl in *.
    destruct (isSupportedByAnyDec ss0 cs) as [HL|HR]. {
      constructor. {
        constructor.
        apply isSupportedByReflexive.
      } {
        rewrite Forall_forall.
        intros x H_in.
        rewrite Forall_forall in IHssrest.
        pose proof (IHssrest _ H_in) as H_rest.
        unfold isSupportedByAny in *.
        rewrite Exists_cons.
        right.
        exact H_rest.
      }
    } {
      rewrite Forall_forall.
      intros x H_in.
      rewrite Forall_forall in IHssrest.
      pose proof (IHssrest _ H_in) as H_rest.
      unfold isSupportedByAny in *.
      rewrite Exists_cons.
      right.
      exact H_rest.
    }
  }
Qed.

Lemma withoutUnsupportedFilterForallServerIn : forall ss cs,
  Forall (fun k => In k ss) 
    (filter (fun i => match isSupportedByAnyDec i cs with
             | left _  => true
             | right _ => false
             end) ss).
Proof.
  intros ss cs.
  induction ss as [|ss0 ssrest]. {
    constructor.
  } {
    simpl in *.
    destruct (isSupportedByAnyDec ss0 cs) as [HL|HR]. {
      constructor. {
        constructor.
        reflexivity.
      } {
        rewrite Forall_forall.
        intros x H_in.
        rewrite Forall_forall in IHssrest.
        pose proof (IHssrest _ H_in) as H_rest.
        right.
        exact H_rest.
      }
    } {
      rewrite Forall_forall.
      intros x H_in.
      rewrite Forall_forall in IHssrest.
      pose proof (IHssrest _ H_in) as H_rest.
      right.
      exact H_rest.
    }
  }
Qed.

Theorem withoutUnsupportedNoClient : forall ss,
  withoutUnsupported ss [] = Failure _ ErrorNoSolution.
Proof.
  unfold withoutUnsupported.
  intros ss.
  assert (filter (fun i : ProtoIdentifier => if isSupportedByAnyDec i [] then true else false) ss = []) as H_empty. {
    induction ss as [|x xs]. {
      reflexivity.
    } {
      simpl.
      assert ((if isSupportedByAnyDec x [] then true else false) = false) as H_false. {
        destruct (isSupportedByAnyDec x []) as [HL|HR]. {
          contradict HL.
          apply isSupportedByAnyFalse. 
        } {
          reflexivity.
        }
      }
      rewrite H_false.
      exact IHxs.
    }
  }

  rewrite H_empty.
  reflexivity.
Qed.

Theorem withoutUnsupportedErrorIsNoSolution : forall ss cs e,
  withoutUnsupported ss cs = Failure _ e ->
    e = ErrorNoSolution.
Proof.
  intros ss cs e.
  unfold withoutUnsupported.
  destruct (filter (fun i : ProtoIdentifier => if isSupportedByAnyDec i cs then true else false) ss) as [|y ys] eqn:Hm. {
    intro Heq.
    congruence.
  } {
    intro Hneq.
    contradict Hneq; discriminate.
  }
Qed.

Theorem withoutUnsupportedSuccessForAllClient : forall ss cs rs,
  withoutUnsupported ss cs = Success _ rs ->
    Forall (fun k => isSupportedByAny k cs) rs.
Proof.
  unfold withoutUnsupported.
  intros ss cs rs H_succ.
  destruct (filter (fun i : ProtoIdentifier => if isSupportedByAnyDec i cs then true else false) ss) as [|t ts] eqn:Hfilt. {
    contradict H_succ; discriminate.
  } {
    assert (t :: ts = rs) by congruence.
    subst rs.
    clear H_succ.
    pose proof (withoutUnsupportedFilterForallClient ss cs) as Hfa.
    rewrite Hfilt in Hfa.
    exact Hfa.
  }
Qed.

Theorem withoutUnsupportedSuccessForAllServer : forall ss cs rs,
  withoutUnsupported ss cs = Success _ rs ->
    Forall (fun k => isSupportedByAny k ss) rs.
Proof.
  unfold withoutUnsupported.
  intros ss cs rs H_succ.
  destruct (filter (fun i : ProtoIdentifier => if isSupportedByAnyDec i cs then true else false) ss) as [|t ts] eqn:Hfilt. {
    contradict H_succ; discriminate.
  } {
    assert (t :: ts = rs) by congruence.
    subst rs.
    clear H_succ.
    pose proof (withoutUnsupportedFilterForallServer ss cs) as Hfa.
    rewrite Hfilt in Hfa.
    exact Hfa.
  }
Qed.

Theorem withoutUnsupportedSuccessInServer : forall ss cs rs,
  withoutUnsupported ss cs = Success _ rs ->
    Forall (fun k => In k ss) rs.
Proof.
  unfold withoutUnsupported.
  intros ss cs rs H_succ.
  destruct (filter (fun i : ProtoIdentifier => if isSupportedByAnyDec i cs then true else false) ss) as [|t ts] eqn:Hfilt. {
    contradict H_succ; discriminate.
  } {
    assert (t :: ts = rs) by congruence.
    subst rs.
    clear H_succ.
    pose proof (withoutUnsupportedFilterForallServerIn ss cs) as Hfa.
    rewrite Hfilt in Hfa.
    exact Hfa.
  }
Qed.

Theorem withoutUnsupportedSuccessNonEmpty : forall ss cs rs,
  withoutUnsupported ss cs = Success _ rs -> [] <> rs.
Proof.
  unfold withoutUnsupported.
  intros ss cs rs H_succ.
  destruct (filter (fun i : ProtoIdentifier => if isSupportedByAnyDec i cs then true else false) ss) as [|t ts] eqn:Hfilt. {
    contradict H_succ; discriminate.
  } {
    assert (t :: ts = rs) by congruence.
    subst rs.
    discriminate.
  }
Qed.

Definition protocolsOf
  (identifiers : list ProtoIdentifier)
: list ProtoName :=
  map prName identifiers.

Theorem protocolsOfIn : forall xs x,
  In x xs -> In (prName x) (protocolsOf xs).
Proof.
  unfold protocolsOf.
  induction xs as [|y ys]. {
    intros x H_in.
    inversion H_in.
  } {
    intros x H_in.
    destruct H_in as [Heq|Hrest]. {
      subst y.
      simpl.
      left; reflexivity.
    } {
      simpl.
      right.
      apply (IHys _ Hrest).
    }
  }
Qed.

Theorem protocolsOfNamesForall : forall (xs : list ProtoIdentifier),
  Forall (fun name => exists i, prName i = name /\ In i xs) (protocolsOf xs).
Proof.
  intros xs.
  unfold protocolsOf.
  rewrite Forall_map.
  induction xs as [|y ys]. {
    constructor.
  } {
    constructor. {
      exists y.
      apply conj. reflexivity. left; reflexivity.
    }
    rewrite Forall_forall in *.
    intros x Hxin.
    pose proof (IHys _ Hxin) as [k [Hk0 Hk1]].
    exists k.
    apply conj.
    exact Hk0.
    apply in_cons.
    exact Hk1.
  }
Qed.

Definition distinctProtocolsOf
  (identifiers : list ProtoIdentifier)
: list ProtoName :=
  nodup string_dec (protocolsOf identifiers).

Theorem distinctProtocolsOfForallNames : forall xs,
  Forall (fun name => exists i, prName i = name /\ In i xs) (distinctProtocolsOf xs).
Proof.
  unfold distinctProtocolsOf.
  intros xs.
  pose proof (protocolsOfNamesForall xs) as H_nfa.
  rewrite Forall_forall in *.
  intros x H_in_nodup.
  rewrite nodup_In in H_in_nodup.
  apply (H_nfa x H_in_nodup).
Qed.

Lemma distinctProtocolsOfNames0 : forall xs n,
  In n (protocolsOf xs) -> In n (distinctProtocolsOf xs).
Proof.
  intros xs n H_in.
  apply nodup_In.
  exact H_in.
Qed.

Lemma distinctProtocolsOfNames1 : forall xs n,
  In n (distinctProtocolsOf xs) -> In n (protocolsOf xs).
Proof.
  intros xs n H_in.
  unfold distinctProtocolsOf in H_in.
  rewrite nodup_In in *.
  exact H_in.
Qed.

Theorem distinctProtocolsOfNames : forall xs n,
  In n (protocolsOf xs) <-> In n (distinctProtocolsOf xs).
Proof.
  constructor.
  apply distinctProtocolsOfNames0.
  apply distinctProtocolsOfNames1.
Qed.

Lemma nodup_In_cons : forall (A : Type) (xs : list A) f (x y : A),
  In x (nodup f xs) -> In x (nodup f (y :: xs)).
Proof.
  intros A xs f x y H_in.
  simpl.
  destruct (in_dec f y xs) as [H0|H1]. {
    exact H_in.
  } {
    simpl.
    right; exact H_in.
  }
Qed.

Lemma distinctProtocolsInCons : forall xs x y,
  In (prName x) (distinctProtocolsOf xs) ->
    In (prName x) (distinctProtocolsOf (y :: xs)).
Proof.
  intros xs x y H_in.
  induction xs as [|q qs]. {
    inversion H_in.
  } {
    rewrite <- distinctProtocolsOfNames in *.
    destruct H_in as [H0|H1]. {
      rewrite <- H0 in *.
      simpl.
      right.
      left.
      reflexivity.
    } {
      simpl.
      right.
      right.
      exact H1.
    }
  }
Qed.

Theorem distinctProtocolsOfIn : forall xs x,
  In x xs -> In (prName x) (distinctProtocolsOf xs).
Proof.
  unfold distinctProtocolsOf in *.
  unfold protocolsOf in *.
  induction xs as [|z zs]. {
    intros x H_in.
    inversion H_in.
  } {
    intros x H_in.
    rewrite nodup_In.
    rewrite map_cons.
    destruct H_in as [Heq|Hrest]. {
      subst z.
      constructor.
      reflexivity.
    } {
      simpl.
      pose proof (IHzs x Hrest) as Hin_zs.
      right.
      rewrite <- nodup_In.
      exact Hin_zs.
    }
  }
Qed.

Theorem distinctProtocolsOfInExists : forall xs x,
  In x xs -> exists y, In y (distinctProtocolsOf xs) /\ y = prName x.
Proof.
  intros xs x H_in.
  induction xs as [|z zs]. {
    contradict H_in.
  } {
    simpl in *.
    destruct H_in as [Heq|Hin]. {
      subst x.
      exists (prName z).
      constructor. {
        unfold distinctProtocolsOf.
        unfold protocolsOf.
        rewrite map_cons.
        rewrite nodup_In.
        constructor.
        reflexivity.
      } {
        reflexivity.
      }
    } {
      pose proof (IHzs Hin) as Hex.
      destruct Hex as [q [Hq0 Hq1]].
      rewrite Hq1 in *.
      exists (prName x).
      constructor.
      apply (distinctProtocolsInCons zs x z Hq0).
      reflexivity.
    }
  }
Qed.

Theorem distinctProtocolsOfForall : forall xs,
  Forall (fun name => exists k, In k xs /\ prName k = name) (distinctProtocolsOf xs).
Proof.
  intros xs.
  unfold distinctProtocolsOf.
Abort.

Definition identifiersWithProtocol
  (identifiers : list ProtoIdentifier)
  (name        : ProtoName)
: list ProtoIdentifier :=
  filter (fun i => match string_dec (prName i) name with
    | left _  => true
    | right _ => false
    end) identifiers.

Lemma identifiersWithProtocolFilterForall : forall xs n,
  Forall (fun k => prName k = n)
    (filter (fun i => match string_dec (prName i) n with
             | left _  => true
             | right _ => false
             end) xs).
Proof.
  intros xs.
  induction xs as [|y ys]. {
    intros n.
    apply Forall_nil.
  } {
    intros n.
    simpl.
    destruct (string_dec (prName y) n) as [Hs|Hns]. {
      constructor.
      exact Hs.
      apply IHys.
    } {
      apply IHys.
    }
  }
Qed.

Theorem identifiersWithProtocolSpec : forall xs n,
  Forall (fun k => prName k = n) (identifiersWithProtocol xs n).
Proof.
  unfold identifiersWithProtocol.
  intros xs n.
  destruct (filter (fun i : ProtoIdentifier => if string_dec (prName i) n then true else false) xs) as [|t ts] eqn:Hfilt. {
    constructor.
  } {
    pose proof (identifiersWithProtocolFilterForall xs n) as Hfa.
    rewrite Hfilt in Hfa.
    exact Hfa.
  }
Qed.

Theorem identifiersNonEmpty : forall xs x,
  In x xs -> (identifiersWithProtocol xs (prName x)) <> [].
Proof.
  intros xs x H_in.
  pose proof (identifiersWithProtocolSpec xs (prName x)) as H_wfa.
  induction xs as [|y ys]. {
    inversion H_in.
  } {
    simpl in *.
    destruct H_in as [H_eq|H_rest]. {
      subst x.
      simpl in H_wfa.
      destruct (string_dec (prName y) (prName y)) as [H_sdt|H_sdf]. {
        discriminate.
      } {
        contradict H_sdf; reflexivity.
      }
    } {
      destruct (string_dec (prName y) (prName x)) as [H_sdt|H_sdf]. {
        discriminate.
      } {
        apply (IHys H_rest H_wfa).
      }
    }
  }
Qed.

Theorem identifiersWithProtocolIn : forall xs x n,
  In x xs ->
    prName x = n -> 
      In x (identifiersWithProtocol xs n).
Proof.
  unfold identifiersWithProtocol.
  intros xs x n H_in H_eq.
  induction xs as [|y ys]. {
    inversion H_in.
  } {
    destruct H_in as [HinL|HinR]. {
      subst x.
      simpl.
      destruct (string_dec (prName y) n) as [HdecL|HdecR]. {
        constructor; reflexivity.
      } {
        contradict H_eq; exact HdecR.
      }
    } {
      subst n.
      simpl.
      destruct (string_dec (prName y) (prName x)) as [HdecL|HdecR]. {
        simpl.
        right.
        apply (IHys HinR).
      } {
        apply (IHys HinR).
      }
    }
  }
Qed.

Theorem identifiersWithProtocolInInv : forall xs x n,
  In x (identifiersWithProtocol xs n) -> In x xs.
Proof.
  unfold identifiersWithProtocol.
  intros xs x n H_in.
  rewrite filter_In in H_in.
  destruct H_in as [H0 _].
  exact H0.
Qed.

Definition versionsOf
  (identifiers : list ProtoIdentifier)
: list ProtoVersion :=
  map prVersion identifiers.

Definition toIdentifiers
  (versions : list ProtoVersion)
  (name     : ProtoName)
: list ProtoIdentifier :=
  map (fun v => Build_ProtoIdentifier name v) versions.

Theorem toIdentifiersIdentity : forall xs n,
  toIdentifiers (versionsOf (identifiersWithProtocol xs n)) n = (identifiersWithProtocol xs n).
Proof.
  intros xs n.
  pose proof (identifiersWithProtocolSpec xs n) as Hps.
  induction (identifiersWithProtocol xs n) as [|y ys]. {
    reflexivity.
  } {
    pose proof (Forall_inv Hps) as H0.
    pose proof (Forall_inv_tail Hps) as H1.
    pose proof (IHys H1) as H2.
    simpl.
    rewrite H2.
    assert (prName y = n) as Hyn. {
      rewrite H0.
      reflexivity.
    }
    subst n.
    destruct y as [yn yv].
    reflexivity.
  }
Qed.

Module MaxProtoVersion := 
  Max ProtoVersionOrd.
Module MaxListsProtoVersion :=
  MaxLists ProtoVersionOrd MaxProtoVersion.

Lemma filter_not_empty : forall {A : Type} (f : A -> bool) xs,
  [] <> filter f xs -> [] <> xs.
Proof.
  intros A f xs H_ne.
  induction xs as [|y ys]. {
    contradict H_ne; reflexivity.
  } {
    discriminate.
  }
Qed.

Lemma map_not_empty_r : forall {A B : Type} (f : A -> B) xs,
  xs <> [] <-> map f xs <> [].
Proof.
  intros A B f xs.
  constructor.
  intros Hxs.
  destruct xs as [|y ys]. {
    contradict Hxs; reflexivity.
  } {
    rewrite map_cons.
    discriminate.
  }
  intros Hmxs.
  destruct xs as [|y ys]. {
    contradict Hmxs; reflexivity.
  } {
    discriminate.
  }
Qed.

Lemma map_not_empty_l : forall {A B : Type} (f : A -> B) xs,
  [] <> xs <-> [] <> map f xs.
Proof.
  intros A B f xs.
  constructor.
  intros Hxs.
  destruct xs as [|y ys]. {
    contradict Hxs; reflexivity.
  } {
    rewrite map_cons.
    discriminate.
  }
  intros Hmxs.
  destruct xs as [|y ys]. {
    contradict Hmxs; reflexivity.
  } {
    discriminate.
  }
Qed.

Definition bestVersionOf
  (identifiers : list ProtoIdentifier)
  (name        : ProtoName)
: option ProtoVersion :=
  let withId   := identifiersWithProtocol identifiers name in
  let versions := versionsOf withId in
    MaxListsProtoVersion.maxList versions.

Theorem bestVersionOfMax : forall identifiers v n,
  bestVersionOf identifiers n = Some v ->
    Forall (fun i => prName i = n -> ProtoVersionOrd.le (prVersion i) v) identifiers.
Proof.
  unfold bestVersionOf.
  unfold versionsOf.
  intros identifiers v n H_some.

  rewrite Forall_forall.
  intros i H_in H_nameeq.

  pose proof (identifiersWithProtocolIn _ _ _ H_in H_nameeq) as H_iinp.
  pose proof (MaxListsProtoVersion.maxSpec _ _ H_some) as H_vfa.
  rewrite Forall_forall in *.

  assert ((In (prVersion i) (map prVersion (identifiersWithProtocol identifiers n)))) as H_inver. {
    apply in_map.
    exact H_iinp.
  }

  apply H_vfa.
  exact H_inver.
Qed.

Theorem bestVersionOfInSome : forall xs x,
  In x xs -> exists (v : ProtoVersion), bestVersionOf xs (prName x) = Some v.
Proof.
  unfold bestVersionOf.
  intros xs x H_in.
  assert (versionsOf (identifiersWithProtocol xs (prName x)) <> []) as Hv_nempty. {
    pose proof (identifiersNonEmpty _ _ H_in) as Hw_nempty.
    unfold versionsOf.
    apply map_not_empty_r.
    exact Hw_nempty.
  }
  rewrite <- MaxListsProtoVersion.maxListExists.
  exact Hv_nempty.
Qed.

Theorem bestVersionOfInNonEmpty : forall identifiers n v,
  bestVersionOf identifiers n = Some v ->
    [] <> identifiers.
Proof.
  intros identifiers n v H_best.
  unfold bestVersionOf in H_best.
  assert ([] <> versionsOf (identifiersWithProtocol identifiers n)) as Hvne. {
    assert (exists y : ProtoVersion, ((MaxListsProtoVersion.maxList (versionsOf (identifiersWithProtocol identifiers n))) = (Some y))) as Hex. {
      exists v. exact H_best.
    }
    rewrite <- MaxListsProtoVersion.maxListExists in Hex.
    intuition.
  }
  assert ([] <> identifiersWithProtocol identifiers n) as Hine. {
    unfold versionsOf in Hvne.
    rewrite <- map_not_empty_l in Hvne.
    exact Hvne.
  }
  unfold identifiersWithProtocol in Hine.
  apply (filter_not_empty _ identifiers Hine).
Qed.

Theorem bestVersionOfInSomeAlt : forall xs n x,
  In x xs ->
    prName x = n ->
      exists v, bestVersionOf xs n = Some v.
Proof.
  unfold bestVersionOf.
  induction xs as [|z zs]. {
    intros n x Hin _.
    inversion Hin.
  } {
    intros n x Hin Heq.
    destruct Hin as [Hxeq|Hxrest]. {
      subst z.
      assert (In x (x :: zs)) as Hobvious by (left; reflexivity).
      pose proof (identifiersNonEmpty _ _ Hobvious) as H_nempty.
      unfold versionsOf.
      rewrite (map_not_empty_r prVersion) in H_nempty.
      rewrite Heq in H_nempty.
      rewrite <- MaxListsProtoVersion.maxListExists.
      exact H_nempty.
    } {
      pose proof (IHzs n x Hxrest Heq) as Hind.
      unfold versionsOf in *.
      destruct Hind as [q Hq].
      simpl.
      destruct (string_dec (prName z) n) as [Hzn|Hnzn]. {
        simpl.
        destruct (MaxListsProtoVersion.maxList (map prVersion (identifiersWithProtocol zs n))). {
          exists (MaxProtoVersion.max (prVersion z) p).
          reflexivity.
        }
        contradict Hq; discriminate.
      } {
        destruct (MaxListsProtoVersion.maxList (map prVersion (identifiersWithProtocol zs n))). {
          exists p.
          reflexivity.
        }
        contradict Hq; discriminate.
      }
    }
  }
Qed.

Theorem bestVersionOfInSomeAlt2 : forall xs x n v,
  prName x = n ->
    prVersion x = v ->
      bestVersionOf xs n = Some v ->
        In x xs.
Proof.
  unfold bestVersionOf.
  intros identifiers i n v H_name H_ver H_best.
  unfold versionsOf in H_best.

  (* We can demonstrate that there's an identifier `j` that must be in
     the set of identifiers returned by identifiersWithProtocol. *)
  assert (In v (map prVersion (identifiersWithProtocol identifiers n))) as H0
    by (apply (MaxListsProtoVersion.maxListIn _ _ H_best)).
  rewrite in_map_iff in H0.
  destruct H0 as [j [Hj0 Hj1]].

  (* We can also prove that `j` has the name `n` *)
  pose proof (identifiersWithProtocolSpec identifiers n) as H_idfa.
  rewrite Forall_forall in H_idfa.
  pose proof (H_idfa _ Hj1) as H_jname.

  (* Therefore, we can prove that i = j, and eliminate j. *)
  assert (i = j) as H_eq_ij. {
    destruct i as [i_n i_v].
    destruct j as [j_n j_v].
    simpl in *.
    subst j_n.
    subst j_v.
    subst i_n.
    subst i_v.
    reflexivity.
  }
  subst j.
  clear Hj0.
  clear H_jname.

  (* Because we now know that `i` is in the list of identifiers
     returned by identifiersWithProtocol, we can prove that `i`
     must have been in the original list of identifiers. *)

  apply (identifiersWithProtocolInInv _ _ _ Hj1).
Qed.

Definition bestVersionsOfAllOpt
  (identifiers : list ProtoIdentifier)
: list (option ProtoIdentifier) :=
  let distincts := distinctProtocolsOf identifiers in
    map (fun name =>
      match bestVersionOf identifiers name with
      | Some v => Some (Build_ProtoIdentifier name v)
      | None   => None
      end) distincts.

Definition isSome
  {A : Type}
  (o : option A)
: Prop :=
  match o with
  | Some _ => True
  | None   => False
  end.

Theorem bestVersionsOfAllOptSome : forall xs,
  Forall isSome (bestVersionsOfAllOpt xs).
Proof.
  intros xs.
  unfold bestVersionsOfAllOpt.
  pose proof (distinctProtocolsOfForallNames xs) as H_dfa.
  rewrite Forall_map.
  rewrite Forall_forall in *.
  intros x H_inx.
  pose proof (H_dfa x H_inx) as [i [Hi0 Hi1]].
  pose proof (bestVersionOfInSomeAlt _ _ _ Hi1 Hi0) as [v Hv].
  rewrite Hv.
  constructor.
Qed.

Theorem bestVersionsOfAllOptNonEmpty : forall xs,
  [] <> xs -> [] <> bestVersionsOfAllOpt xs.
Proof.
  intros xs H_nonempty.
  unfold bestVersionsOfAllOpt.
  destruct xs as [|y ys]. {
    contradict H_nonempty; reflexivity.
  } {
    assert ([] <> distinctProtocolsOf (y :: ys)) as Hdne. {
      assert (In y (y :: ys)) as H_obvious by (left; reflexivity).
      pose proof (distinctProtocolsOfInExists _ _ H_obvious) as [w [Hw0 Hw1]].
      destruct (distinctProtocolsOf (y :: ys)). {
        contradict Hw0.
      } {
        discriminate.
      }
    }
    apply map_not_empty_l.
    exact Hdne.
  }
Qed.

Theorem bestVersionsOfAllOptIn : forall identifiers i,
  In (Some i) (bestVersionsOfAllOpt identifiers) -> In i identifiers.
Proof.
  unfold bestVersionsOfAllOpt.
  intros identifiers.

  induction (distinctProtocolsOf identifiers) as [|dname dnames]. {
    intros i H_in.
    contradict H_in.
  } {
    intros j H_in.
    destruct H_in as [HL|HR]. {
      destruct (bestVersionOf identifiers dname) eqn:Hbv. {
        assert (j = {| prName := dname; prVersion := p |}) as H_rec by congruence.
        clear HL.
        apply (bestVersionOfInSomeAlt2 identifiers j dname p). {
          subst j; reflexivity.
        } {
          subst j; reflexivity.
        }
        exact Hbv.
      } {
        contradict HL; discriminate.
      }
    } {
      apply (IHdnames _ HR).
    }
  }
Qed.

Theorem bestVersionsOfAllOptLe : forall identifiers i,
  In (Some i) (bestVersionsOfAllOpt identifiers) ->
    Forall (fun k => prName k = prName i -> ProtoVersionOrd.le (prVersion k) (prVersion i)) identifiers.
Proof.
  unfold bestVersionsOfAllOpt.
  intros identifiers.

  induction (distinctProtocolsOf identifiers) as [|dname dnames]. {
    intros i H_in.
    contradict H_in.
  } {
    intros j H_in.
    destruct H_in as [HL|HR]. {
      destruct (bestVersionOf identifiers dname) eqn:Hbv. {
        assert (j = {| prName := dname; prVersion := p |}) as H_rec by congruence.
        clear HL.
        pose proof (bestVersionOfMax _ _ _ Hbv) as Hbvmax.
        assert (dname = prName j) as H_jname. {
          destruct j. simpl in *. congruence.
        }
        assert (p = prVersion j) as H_pver. {
          destruct j. simpl in *. congruence.
        }
        rewrite <- H_jname.
        rewrite <- H_pver.
        exact Hbvmax.
      } {
        contradict HL; discriminate.
      }
    } {
      apply IHdnames.
      exact HR.
    }
  }
Qed.

Fixpoint withoutOptions
  {A  : Type}
  (xs : list (option A))
: list A :=
  match xs with
  | []             => []
  | (Some y) :: ys => y :: (withoutOptions ys)
  | None :: ys     => withoutOptions ys
  end.

Definition withSome
  {A  : Type}
  (xs : list A)
: list (option A) :=
  map Some xs.

Theorem withoutOptionsId : forall A (xs : list (option A)),
  Forall isSome xs -> withSome (withoutOptions xs) = xs.
Proof.
  intros A xs Hfa.

  induction xs as [|y ys]. {
    reflexivity.
  } {
    simpl.
    destruct y as [s|]. {
      simpl.
      f_equal.
      apply IHys.
      apply (Forall_inv_tail Hfa).
    } {
      pose proof (Forall_inv Hfa) as H_contra.
      inversion H_contra.
    }
  }
Qed.

Theorem withoutOptionsNonEmpty : forall A (xs : list (option A)),
  [] <> xs -> Forall isSome xs -> [] <> (withoutOptions xs).
Proof.
  intros A xs H_ne H_fa.
  induction xs as [|y ys]. {
    contradict H_ne; reflexivity.
  } {
    simpl.
    destruct y as [s|]. {
      discriminate.
    } {
      pose proof (Forall_inv H_fa) as Hcontra.
      contradict Hcontra.
    }
  }
Qed.

Theorem withoutOptionsIn : forall A (xs : list (option A)) x,
  Forall isSome xs -> In x (withoutOptions xs) <-> In (Some x) xs.
Proof.
  intros A xs x H_fa.
  constructor. {
    intros H_in.
    induction xs as [|y ys]. {
      contradict H_in.
    } {
      simpl in *.
      pose proof (Forall_inv H_fa) as H_some.
      pose proof (Forall_inv_tail H_fa) as H_some_tail.

      destruct y as [s|]. {
        destruct H_in as [HL|HR]. {
          subst x.
          left. f_equal.
        } {
          right. apply (IHys H_some_tail HR).
        }
      } {
        contradict H_some.
      }
    }
  } {
    intros H_in.
    induction xs as [|y ys]. {
      contradict H_in.
    } {
      simpl in *.
      pose proof (Forall_inv H_fa) as H_some.
      pose proof (Forall_inv_tail H_fa) as H_some_tail.

      destruct y as [s|]. {
        destruct H_in as [HL|HR]. {
          assert (s = x) as Heq by congruence.
          subst x.
          left; reflexivity.
        } {
          right. apply (IHys H_some_tail HR).
        }
      } {
        contradict H_some.
      }
    }
  }
Qed.

Definition bestVersionsOfAll
  (identifiers : list ProtoIdentifier)
: list ProtoIdentifier :=
  withoutOptions (bestVersionsOfAllOpt identifiers).

Theorem bestVersionsOfAllNonEmpty : forall xs,
  [] <> xs -> [] <> bestVersionsOfAll xs.
Proof.
  intros xs H_notempty.
  unfold bestVersionsOfAll.
  pose proof (bestVersionsOfAllOptSome xs) as Hfa.
  pose proof (bestVersionsOfAllOptNonEmpty xs H_notempty) as Hne.
  apply (withoutOptionsNonEmpty _ _ Hne Hfa).
Qed.

Theorem bestVersionsOfIn : forall xs x,
  In x (bestVersionsOfAll xs) -> In x xs.
Proof.
  unfold bestVersionsOfAll.
  intros xs x H_in.
  pose proof (bestVersionsOfAllOptSome xs) as H_fa.
  rewrite (withoutOptionsIn _ _ x H_fa) in H_in.
  apply (bestVersionsOfAllOptIn _ _ H_in).
Qed.

Theorem bestVersionsOfAllLe : forall identifiers i,
  In i (bestVersionsOfAll identifiers) ->
    Forall (fun k => prName k = prName i -> ProtoVersionOrd.le (prVersion k) (prVersion i)) identifiers.
Proof.
  unfold bestVersionsOfAll.
  intros identifiers i H_in.
  pose proof (bestVersionsOfAllOptLe identifiers) as H_fa.
  rewrite withoutOptionsIn in H_in.
  apply (H_fa _ H_in).
  apply bestVersionsOfAllOptSome.
Qed.

Theorem bestVersionsOfWithoutUnsupportedClient : forall ss cs rs,
  withoutUnsupported ss cs = Success _ rs ->
      Forall (fun i => isSupportedByAny i cs) (bestVersionsOfAll rs).
Proof.
  intros ss cs rs H_succ.
  pose proof (bestVersionsOfIn rs) as H_in_fa.
  rewrite <- Forall_forall in H_in_fa.
  pose proof (withoutUnsupportedSuccessForAllClient _ _ _ H_succ) as H_supp.

  induction H_in_fa as [|y ys Hy Hys]. {
    constructor.
  } {
    constructor.
    rewrite Forall_forall in H_supp.
    apply H_supp.
    exact Hy.
    apply IHHys.
  }
Qed.

Theorem bestVersionsOfWithoutUnsupportedServer : forall ss cs rs,
  withoutUnsupported ss cs = Success _ rs ->
      Forall (fun i => isSupportedByAny i ss) (bestVersionsOfAll rs).
Proof.
  intros ss cs rs H_succ.
  pose proof (bestVersionsOfIn rs) as H_in_fa.
  rewrite <- Forall_forall in H_in_fa.
  pose proof (withoutUnsupportedSuccessForAllServer _ _ _ H_succ) as H_supp.

  induction H_in_fa as [|y ys Hy Hys]. {
    constructor.
  } {
    constructor.
    rewrite Forall_forall in H_supp.
    apply H_supp.
    exact Hy.
    apply IHHys.
  }
Qed.

Definition solveWithoutDisambiguation
  (serverSupports : list ProtoIdentifier)
  (clientSupports : list ProtoIdentifier)
: Result ProtoIdentifier :=
  match withoutUnsupported serverSupports clientSupports with
  | Failure _ f         => Failure _ f
  | Success _ supported =>
    let bestVersions := bestVersionsOfAll supported in
      match bestVersions with
      | []  => Failure _ ErrorNoSolution
      | [x] => Success _ x
      | xs  => Failure _ (ErrorAmbiguous xs)
      end
  end.

Theorem solveWithoutDisambiguationNoServerSupport : forall cs,
  solveWithoutDisambiguation [] cs = Failure _ ErrorNoSolution.
Proof. reflexivity. Qed.

Theorem solveWithoutDisambiguationNoClientSupport : forall ss,
  solveWithoutDisambiguation ss [] = Failure _ ErrorNoSolution.
Proof.
  intros ss.
  unfold solveWithoutDisambiguation.
  rewrite withoutUnsupportedNoClient.
  reflexivity.
Qed.

Theorem solveWithoutDisambiguationSuccessClientHas : forall ss cs r,
  solveWithoutDisambiguation ss cs = Success _ r ->
    isSupportedByAny r cs.
Proof.
  intros ss cs r H_succ.
  unfold solveWithoutDisambiguation in H_succ.

  destruct (withoutUnsupported ss cs) as [supported|] eqn:Hwu. {
    destruct (bestVersionsOfAll supported) as [|v0 vs] eqn:Hbv. {
      pose proof (withoutUnsupportedSuccessNonEmpty _ _ _ Hwu) as H_wune.
      pose proof (bestVersionsOfAllNonEmpty _ H_wune) as H_bs_ne.
      rewrite Hbv in H_bs_ne.
      contradict H_bs_ne; reflexivity.
    } {
      destruct vs as [|v1 vs]. {
        assert (v0 = r) as Hvreq by congruence.
        subst r.
        clear H_succ.
        pose proof (withoutUnsupportedSuccessForAllClient _ _ _ Hwu) as H_wusfa.
        rewrite Forall_forall in H_wusfa.
        apply H_wusfa.
        apply (bestVersionsOfIn supported v0).
        rewrite Hbv.
        left; reflexivity.
      } {
        contradict H_succ; discriminate.
      }
    }
  } {
    contradict H_succ; discriminate.
  }
Qed.

Theorem solveWithoutDisambiguationSuccessServerHas : forall ss cs r,
  solveWithoutDisambiguation ss cs = Success _ r ->
    isSupportedByAny r ss.
Proof.
  intros ss cs r H_succ.
  unfold solveWithoutDisambiguation in H_succ.

  destruct (withoutUnsupported ss cs) as [supported|] eqn:Hwu. {
    destruct (bestVersionsOfAll supported) as [|v0 vs] eqn:Hbv. {
      pose proof (withoutUnsupportedSuccessNonEmpty _ _ _ Hwu) as H_wune.
      pose proof (bestVersionsOfAllNonEmpty _ H_wune) as H_bs_ne.
      rewrite Hbv in H_bs_ne.
      contradict H_bs_ne; reflexivity.
    } {
      destruct vs as [|v1 vs]. {
        assert (v0 = r) as Hvreq by congruence.
        subst r.
        clear H_succ.
        pose proof (withoutUnsupportedSuccessForAllServer _ _ _ Hwu) as H_wusfa.
        rewrite Forall_forall in H_wusfa.
        apply H_wusfa.
        apply (bestVersionsOfIn supported v0).
        rewrite Hbv.
        left; reflexivity.
      } {
        contradict H_succ; discriminate.
      }
    }
  } {
    contradict H_succ; discriminate.
  }
Qed.

Theorem solveWithoutDisambiguationSuccessBothHave : forall ss cs r,
  solveWithoutDisambiguation ss cs = Success _ r ->
    isSupportedByAny r cs /\ isSupportedByAny r ss.
Proof.
  intros ss cs r Heq.
  constructor.
  apply (solveWithoutDisambiguationSuccessClientHas _ _ _ Heq).
  apply (solveWithoutDisambiguationSuccessServerHas _ _ _ Heq).
Qed.

Theorem solveWithoutDisambiguationAmbiguousClientHas : forall ss cs rs,
  solveWithoutDisambiguation ss cs = Failure _ (ErrorAmbiguous rs) ->
    Forall (fun r => isSupportedByAny r cs) rs.
Proof.
  intros ss cs rs H_succ.
  unfold solveWithoutDisambiguation in H_succ.
  destruct (withoutUnsupported ss cs) as [supported|f] eqn:Hwu. {
    destruct (bestVersionsOfAll supported) as [|v0 vs] eqn:Hbv. {
      contradict H_succ; discriminate.
    } {
      destruct vs as [|v1 vs]. {
        contradict H_succ; discriminate.
      } {
        assert (rs = (v0 :: (v1 :: vs))) as H_eq_rs by congruence.
        rewrite <- H_eq_rs in *.
        clear H_eq_rs.
        clear H_succ.
        subst rs.
        apply (bestVersionsOfWithoutUnsupportedClient _ _ _ Hwu).
      }
    }
  } {
    pose proof (withoutUnsupportedErrorIsNoSolution _ _ _ Hwu) as H_ns.
    subst f.
    contradict H_succ; discriminate.
  }
Qed.

Theorem solveWithoutDisambiguationAmbiguousServerHas : forall ss cs rs,
  solveWithoutDisambiguation ss cs = Failure _ (ErrorAmbiguous rs) ->
    Forall (fun r => isSupportedByAny r ss) rs.
Proof.
  intros ss cs rs H_succ.
  unfold solveWithoutDisambiguation in H_succ.
  destruct (withoutUnsupported ss cs) as [supported|f] eqn:Hwu. {
    destruct (bestVersionsOfAll supported) as [|v0 vs] eqn:Hbv. {
      contradict H_succ; discriminate.
    } {
      destruct vs as [|v1 vs]. {
        contradict H_succ; discriminate.
      } {
        assert (rs = (v0 :: (v1 :: vs))) as H_eq_rs by congruence.
        rewrite <- H_eq_rs in *.
        clear H_eq_rs.
        clear H_succ.
        subst rs.
        apply (bestVersionsOfWithoutUnsupportedServer _ _ _ Hwu).
      }
    }
  } {
    pose proof (withoutUnsupportedErrorIsNoSolution _ _ _ Hwu) as H_ns.
    subst f.
    contradict H_succ; discriminate.
  }
Qed.

Theorem solveWithoutDisambiguationAmbiguousBothHave : forall ss cs rs,
  solveWithoutDisambiguation ss cs = Failure _ (ErrorAmbiguous rs) ->
    Forall (fun r => isSupportedByAny r ss /\ isSupportedByAny r cs) rs.
Proof.
  intros ss cs rs H_succ.
  pose proof (solveWithoutDisambiguationAmbiguousClientHas _ _ _ H_succ) as HC.
  pose proof (solveWithoutDisambiguationAmbiguousServerHas _ _ _ H_succ) as HS.
  apply (Forall_and HS HC).
Qed.

Fixpoint findWithName
  (xs   : list ProtoIdentifier)
  (name : ProtoName)
: option ProtoIdentifier :=
  match xs with
  | []      => None
  | y :: ys =>
    match string_dec (prName y) name with
    | left _  => Some y
    | right _ => findWithName ys name
    end
  end.

Theorem findWithNameSome : forall xs name x,
  (findWithName xs name) = Some x -> In x xs.
Proof.
  induction xs as [|y ys]. {
    intros name x H_find.
    contradict H_find; discriminate.
  } {
    intros name x H_find.
    simpl in *.
    destruct (string_dec (prName y) name) as [HL|HR]. {
      left; congruence.
    } {
      right.
      apply (IHys _ _ H_find).
    }
  }
Qed.

Fixpoint disambiguate
  (xs          : list ProtoIdentifier)
  (preferences : list ProtoName)
: Result ProtoIdentifier :=
  match preferences with
  | []      => Failure _ (ErrorAmbiguous xs)
  | p :: ps => 
    match findWithName xs p with
    | Some r => Success _ r
    | None   => disambiguate xs ps
    end
  end.

Theorem disambiguateSuccessIn : forall p xs r,
  disambiguate xs p = Success _ r -> In r xs.
Proof.
  induction p as [|q qs]. {
    intros xs r Heq.
    contradict Heq; discriminate.
  } {
    intros xs r Heq.
    simpl in *.
    destruct (findWithName xs q) as [s|] eqn:Hfind. {
      pose proof (findWithNameSome _ _ _ Hfind) as Hf.
      assert (r = s) as Hrs by congruence.
      subst s.
      exact Hf.
    } {
      apply (IHqs _ _ Heq).
    }
  }
Qed.

Definition solve
  (serverSupports : list ProtoIdentifier)
  (clientSupports : list ProtoIdentifier)
  (preferences    : list ProtoName)
: Result ProtoIdentifier :=
  match solveWithoutDisambiguation serverSupports clientSupports with
  | Success _ r                   => Success _ r
  | Failure _ ErrorNoSolution     => Failure _ ErrorNoSolution
  | Failure _ (ErrorAmbiguous xs) => disambiguate xs preferences
  end.

Theorem solveClientHas : forall ss cs p r,
  solve ss cs p = Success _ r -> isSupportedByAny r cs.
Proof.
  intros ss cs p r Heq.
  unfold solve in Heq.
  destruct (solveWithoutDisambiguation ss cs) as [id|er] eqn:Hswd. {
    pose proof (solveWithoutDisambiguationSuccessClientHas _ _ _ Hswd) as H_succ.
    assert (r = id) as H_eq by congruence.
    subst id.
    exact H_succ.
  } {
    destruct er as [|ids]. {
      contradict Heq; discriminate.
    } {
      pose proof (solveWithoutDisambiguationAmbiguousClientHas _ _ _ Hswd) as H_amb.
      rewrite Forall_forall in H_amb.
      apply (H_amb r).
      apply (disambiguateSuccessIn _ _ _ Heq).
    }
  }
Qed.

Theorem solveServerHas : forall ss cs p r,
  solve ss cs p = Success _ r -> isSupportedByAny r ss.
Proof.
  intros ss cs p r Heq.
  unfold solve in Heq.
  destruct (solveWithoutDisambiguation ss cs) as [id|er] eqn:Hswd. {
    pose proof (solveWithoutDisambiguationSuccessServerHas _ _ _ Hswd) as H_succ.
    assert (r = id) as H_eq by congruence.
    subst id.
    exact H_succ.
  } {
    destruct er as [|ids]. {
      contradict Heq; discriminate.
    } {
      pose proof (solveWithoutDisambiguationAmbiguousServerHas _ _ _ Hswd) as H_amb.
      rewrite Forall_forall in H_amb.
      apply (H_amb r).
      apply (disambiguateSuccessIn _ _ _ Heq).
    }
  }
Qed.

Theorem solveBothHave : forall ss cs p r,
  solve ss cs p = Success _ r ->
    isSupportedByAny r ss /\ isSupportedByAny r cs.
Proof.
  intros ss cs p r Heq.
  constructor.
  apply (solveServerHas _ _ _ _ Heq).
  apply (solveClientHas _ _ _ _ Heq).
Qed.

