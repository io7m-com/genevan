Require Coq.Structures.Equalities.
Require Coq.FSets.FSetAVL.
Require Coq.FSets.FSetWeakList.
Require Coq.FSets.FMapFacts.
Require Coq.Lists.List.

Require Genevan.ProtoIdentifier.
Require Genevan.ProtoName.
Require Genevan.ListExts.
Require Genevan.ProtoPeer.Peer.
Require Genevan.ProtoPeer.CollectionT.
Require Genevan.ProtoPeer.CollectionOfProtocolsT.

(** A concrete implementation of the _CollectionOfProtocolsT_ interface. *)

Module CollectionOfProtocols
  (A     : Peer.T)
  (ASets : Peer.SetsT A)
  (AC    : CollectionT.S A ASets)
  (B     : Peer.T)
  (BSets : Peer.SetsT B)
  (BC    : CollectionT.S B BSets)
: CollectionOfProtocolsT.S A ASets AC B BSets BC.

  Module AF := FSetFacts.WFacts ASets.
  Module BF := FSetFacts.WFacts BSets.

  Record t := {
    peersA : ASets.t;
    peersB : BSets.t
  }.

  Definition setsHaveName (ps : t) (n : ProtoName.t) : Prop :=
    AC.setsHaveName (peersA ps) n /\ BC.setsHaveName (peersB ps) n.

  Definition setsEitherNonEmpty (ps : t) : Prop :=
    AC.setsNonEmpty (peersA ps) \/ BC.setsNonEmpty (peersB ps).

  Definition setsWF (ps : t) (n : ProtoName.t) : Prop :=
    setsHaveName ps n /\ setsEitherNonEmpty ps.

  Module ByName      := ProtoName.Maps.
  Module ByNameFacts := ProtoName.MapsFacts.

  Definition mapWF (m : ByName.t t) : Prop :=
    forall s n, ByName.MapsTo n s m -> setsWF s n.

  Definition mapInA (e : A.t) (m : ByName.t t) : Prop :=
    exists s, ByName.MapsTo (ProtoIdentifier.name (A.supports e)) s m /\ ASets.In e (peersA s).

  Definition mapInB (e : B.t) (m : ByName.t t) : Prop :=
    exists s, ByName.MapsTo (ProtoIdentifier.name (B.supports e)) s m /\ BSets.In e (peersB s).

  Theorem mapWFEmpty : mapWF (ByName.empty t).
  Proof.
    unfold mapWF.
    intros s n H_m.
    rewrite ProtoName.MapsFacts.empty_mapsto_iff in H_m.
    contradiction.
  Qed.

  Theorem mapInAEmptyFalse : forall a, ~mapInA a (ByName.empty t).
  Proof.
    unfold mapInA.
    intros a.
    unfold not; intro H_contra.
    destruct H_contra as [x [Hc0 Hc1]].
    rewrite ProtoName.MapsFacts.empty_mapsto_iff in Hc0.
    exact Hc0.
  Qed.

  Theorem mapInBEmptyFalse : forall a, ~mapInB a (ByName.empty t).
  Proof.
    unfold mapInB.
    intros b.
    unfold not; intro H_contra.
    destruct H_contra as [x [Hc0 Hc1]].
    rewrite ProtoName.MapsFacts.empty_mapsto_iff in Hc0.
    exact Hc0.
  Qed.

  Definition singletonAT (a : A.t) : t :=
    Build_t (ASets.singleton a) BSets.empty.

  Theorem setsHaveNameSingletonAT : forall a,
    setsHaveName (singletonAT a) (ProtoIdentifier.name (A.supports a)).
  Proof.
    intros a.
    constructor. {
      apply AC.setsHaveNameSingleton.
    } {
      hnf.
      unfold singletonAT.
      intros x H_false.
      simpl in H_false.
      rewrite BF.empty_iff in H_false.
      contradiction.
    }
  Qed.

  Theorem setsEitherNonEmptySingletonAT : forall a,
    setsEitherNonEmpty (singletonAT a).
  Proof.
    intros a.
    unfold singletonAT.
    unfold setsEitherNonEmpty.
    unfold AC.setsNonEmpty.
    left.
    simpl.
    unfold not; intro H_contra.
    unfold ASets.Empty in H_contra.
    assert (ASets.In a (ASets.singleton a)) as H_in
      by (apply ASets.singleton_2; reflexivity).
    pose proof (H_contra a).
    contradiction.
  Qed.

  Theorem setsWFSingletonAT : forall a,
    setsWF (singletonAT a) (ProtoIdentifier.name (A.supports a)).
  Proof.
    constructor.
    apply setsHaveNameSingletonAT.
    apply setsEitherNonEmptySingletonAT.
  Qed.

  Definition singletonBT (b : B.t) : t :=
    Build_t ASets.empty (BSets.singleton b).

  Theorem setsHaveNameSingletonBT : forall b,
    setsHaveName (singletonBT b) (ProtoIdentifier.name (B.supports b)).
  Proof.
    intros b.
    constructor. {
      hnf.
      unfold singletonAT.
      intros x H_false.
      simpl in H_false.
      rewrite AF.empty_iff in H_false.
      contradiction.
    } {
      apply BC.setsHaveNameSingleton.
    }
  Qed.

  Theorem setsEitherNonEmptySingletonBT : forall b,
    setsEitherNonEmpty (singletonBT b).
  Proof.
    intros b.
    unfold singletonBT.
    unfold setsEitherNonEmpty.
    unfold BC.setsNonEmpty.
    right.
    simpl.
    unfold not; intro H_contra.
    unfold BSets.Empty in H_contra.
    assert (BSets.In b (BSets.singleton b)) as H_in
      by (apply BSets.singleton_2; reflexivity).
    pose proof (H_contra b).
    contradiction.
  Qed.

  Theorem setsWFSingletonBT : forall b,
    setsWF (singletonBT b) (ProtoIdentifier.name (B.supports b)).
  Proof.
    constructor.
    apply setsHaveNameSingletonBT.
    apply setsEitherNonEmptySingletonBT.
  Qed.

  Definition addPeerAT (ps : t) (a : A.t) : t :=
    Build_t (ASets.add a (peersA ps)) (peersB ps).

  Theorem setsHaveNameAddPeerAT : forall ps a n,
    setsHaveName ps n ->
      ProtoIdentifier.name (A.supports a) = n ->
        setsHaveName (addPeerAT ps a) n.
  Proof.
    unfold setsHaveName.
    unfold AC.setsHaveName.
    unfold ASets.For_all.
    unfold addPeerAT.
    simpl in *.
    intros ps a n [H_hnL H_hnR] H_neq.
    constructor. {
      intros x H_inX.
      destruct (A.eq_dec a x) as [H_eqax|H_neqax]. {
        subst x.
        exact H_neq.
      } {
        rewrite AF.add_neq_iff in H_inX.
        apply (H_hnL x H_inX).
        unfold not; intro H_contra.
        rewrite H_contra in H_neqax.
        contradict H_neqax; reflexivity.
      }
    } {
      exact H_hnR.
    }
  Qed.

  Theorem setsEitherNonEmptyAddPeerAT : forall ps a,
    setsEitherNonEmpty ps -> setsEitherNonEmpty (addPeerAT ps a).
  Proof.
    unfold setsEitherNonEmpty.
    unfold AC.setsNonEmpty.
    unfold BC.setsNonEmpty.
    unfold ASets.Empty.
    simpl.
    intros ps a [H_ane|H_bne]. {
      left.
      unfold not; intro H_contra.
      pose proof (H_contra a) as H_contra2.
      apply H_contra2.
      apply ASets.add_1.
      reflexivity.
    } {
      right; trivial.
    }
  Qed.

  Theorem setsWFAddPeerAT : forall ps a n,
    setsWF ps n ->
      ProtoIdentifier.name (A.supports a) = n ->
        setsWF (addPeerAT ps a) n.
  Proof.
    intros ps a n [H_wf0L H_wf0R] H_neq.
    constructor. {
      apply setsHaveNameAddPeerAT.
      exact H_wf0L.
      exact H_neq.
    } {
      apply setsEitherNonEmptyAddPeerAT.
      exact H_wf0R.
    }
  Qed.

  Definition addPeerBT (ps : t) (b : B.t) : t :=
    Build_t (peersA ps) (BSets.add b (peersB ps)).

  Theorem setsHaveNameAddPeerBT : forall ps b n,
    setsHaveName ps n ->
      ProtoIdentifier.name (B.supports b) = n ->
        setsHaveName (addPeerBT ps b) n.
  Proof.
    unfold setsHaveName.
    unfold BC.setsHaveName.
    unfold BSets.For_all.
    unfold addPeerBT.
    simpl in *.
    intros ps b n [H_hnL H_hnR] H_neq.
    constructor. {
      exact H_hnL.
    } {
      intros x H_inX.
      destruct (B.eq_dec b x) as [H_eqax|H_neqax]. {
        subst x.
        exact H_neq.
      } {
        rewrite BF.add_neq_iff in H_inX.
        apply (H_hnR x H_inX).
        unfold not; intro H_contra.
        rewrite H_contra in H_neqax.
        contradict H_neqax; reflexivity.
      }
    }
  Qed.

  Theorem setsEitherNonEmptyAddPeerBT : forall ps b,
    setsEitherNonEmpty ps -> setsEitherNonEmpty (addPeerBT ps b).
  Proof.
    unfold setsEitherNonEmpty.
    unfold AC.setsNonEmpty.
    unfold BC.setsNonEmpty.
    unfold ASets.Empty.
    simpl.
    intros ps b [H_ane|H_bne]. {
      left; trivial.
    } {
      right.
      unfold not; intro H_contra.
      pose proof (H_contra b) as H_contra2.
      apply H_contra2.
      apply BSets.add_1.
      reflexivity.
    }
  Qed.

  Theorem setsWFAddPeerBT : forall ps b n,
    setsWF ps n ->
      ProtoIdentifier.name (B.supports b) = n ->
        setsWF (addPeerBT ps b) n.
  Proof.
    intros ps b n [H_wf0L H_wf0R] H_neq.
    constructor. {
      apply setsHaveNameAddPeerBT.
      exact H_wf0L.
      exact H_neq.
    } {
      apply setsEitherNonEmptyAddPeerBT.
      exact H_wf0R.
    }
  Qed.

  Theorem addBPreservesA : forall ps a b,
    ASets.In a (peersA ps) -> ASets.In a (peersA (addPeerBT ps b)).
  Proof. intros; auto. Qed.

  Theorem addAPreservesB : forall ps a b,
    BSets.In b (peersB ps) -> BSets.In b (peersB (addPeerAT ps a)).
  Proof. intros; auto. Qed.

  Definition addPeerA
    (e : A.t)
    (m : ByName.t t)
  : ByName.t t :=
    let name := ProtoIdentifier.name (A.supports e) in
      match ByName.find name m with
      | Some ex => ByName.add name (addPeerAT ex e) m
      | None    => ByName.add name (singletonAT e) m
      end.

  Theorem mapWFAddPeerA : forall (m : ByName.t t) (e : A.t),
    mapWF m -> mapWF (addPeerA e m).
  Proof.
    unfold mapWF.
    unfold addPeerA.
    intros m e H_wf.
    remember (ProtoIdentifier.name (A.supports e)) as e_name.
    intros s n H_mapsA.

    destruct (ByName.find e_name m) as [ex|] eqn:H_find. {
      rewrite <- ByNameFacts.find_mapsto_iff in H_find.
      rewrite ByNameFacts.add_mapsto_iff in H_mapsA.
      destruct H_mapsA as [[HL0 HL1]|[HR0 HR1]]. {
        rewrite <- HL0 in *.
        rewrite <- HL1.
        pose proof (H_wf _ _ H_find) as H_prevWF.
        symmetry in Heqe_name.
        apply (setsWFAddPeerAT _ _ _ H_prevWF Heqe_name).
      } {
        apply (H_wf _ _ HR1).
      }
    } {
      rewrite ByNameFacts.add_mapsto_iff in H_mapsA.
      destruct H_mapsA as [[HL0 HL1]|[HR0 HR1]]. {
        rewrite <- HL0 in *.
        rewrite <- HL1.
        rewrite Heqe_name.
        apply (setsWFSingletonAT e).
      } {
        apply (H_wf _ _ HR1).
      }
    }
  Qed.

  Theorem mapInAddPeerA : forall (m : ByName.t t) (e : A.t),
    mapInA e (addPeerA e m).
  Proof.
    unfold mapInA.
    unfold addPeerA.
    intros m e.
    remember (ProtoIdentifier.name (A.supports e)) as e_name.
    destruct (ByName.find e_name m) as [ex|] eqn:H_find. {
      rewrite <- ByNameFacts.find_mapsto_iff in H_find.
      unfold addPeerAT.
      simpl.
      exists (Build_t (ASets.add e (peersA ex)) (peersB ex)).
      constructor. {
        apply ByName.add_1; reflexivity.
      } {
        apply ASets.add_1.
        reflexivity.
      }
    } {
      unfold singletonAT.
      exists (Build_t (ASets.singleton e) BSets.empty).
      constructor. {
        apply ByName.add_1; reflexivity.
      } {
        apply ASets.singleton_2; reflexivity.
      }
    }
  Qed.

  Theorem mapAddPeerAPreservesA : forall (m : ByName.t t) (e f : A.t),
    mapInA f m -> mapInA f (addPeerA e m).
  Proof.
    intros m e f H_m.
    remember (ProtoIdentifier.name (A.supports f)) as f_name.
    remember (ProtoIdentifier.name (A.supports e)) as e_name.

    destruct (A.eq_dec e f) as [H_efEq|H_efNeq]. {
      subst f.
      apply mapInAddPeerA.
    } {
      destruct (String.string_dec e_name f_name) as [H_efnEq|H_efnNeq]. {
        unfold mapInA in *.
        unfold addPeerA.
        rewrite <- Heqf_name in *.
        rewrite <- Heqe_name in *.
        rewrite <- H_efnEq in *.
        destruct (ByName.find e_name m) as [sBefore|] eqn:H_find. {
          rewrite <- ByNameFacts.find_mapsto_iff in H_find.
          destruct H_m as [sx [H_sx0 H_sx1]].
          pose proof (ByNameFacts.MapsTo_fun H_find H_sx0) as H_same.
          subst sx.
          exists (addPeerAT sBefore e).
          constructor. {
            rewrite ByNameFacts.add_mapsto_iff.
            constructor. {
              constructor; reflexivity.
            }
          } {
            unfold addPeerAT.
            apply ASets.add_2.
            exact H_sx1.
          }
        } {
          destruct H_m as [sx [H_sx0 H_sx1]].
          pose proof (ByName.find_1 H_sx0) as H_contra.
          rewrite H_find in H_contra.
          inversion H_contra.
        }
      } {
        unfold mapInA in *.
        unfold addPeerA.
        rewrite <- Heqf_name in *.
        rewrite <- Heqe_name in *.
        destruct H_m as [sx [H_sx0 H_sx1]].
        exists sx.

        constructor. {
          destruct (ByName.find e_name m) as [sBefore|] eqn:H_find. {
            apply ByName.add_2.
            exact H_efnNeq.
            exact H_sx0.
          } {
            apply ByName.add_2.
            exact H_efnNeq.
            exact H_sx0.
          }
        } {
          exact H_sx1.
        }
      }
    }
  Qed.

  Definition addPeerB
    (e : B.t)
    (m : ByName.t t)
  : ByName.t t :=
    let name := ProtoIdentifier.name (B.supports e) in
      match ByName.find name m with
      | Some ex => ByName.add name (addPeerBT ex e) m
      | None    => ByName.add name (singletonBT e) m
      end.

  Theorem mapInAddPeerB : forall (m : ByName.t t) (e : B.t),
    mapInB e (addPeerB e m).
  Proof.
    unfold mapInB.
    unfold addPeerB.
    intros m e.
    remember (ProtoIdentifier.name (B.supports e)) as e_name.
    destruct (ByName.find e_name m) as [ex|] eqn:H_find. {
      rewrite <- ByNameFacts.find_mapsto_iff in H_find.
      unfold addPeerBT.
      simpl.
      exists (Build_t (peersA ex) (BSets.add e (peersB ex))).
      constructor. {
        apply ByName.add_1; reflexivity.
      } {
        apply BSets.add_1.
        reflexivity.
      }
    } {
      unfold singletonBT.
      exists (Build_t ASets.empty (BSets.singleton e)).
      constructor. {
        apply ByName.add_1; reflexivity.
      } {
        apply BSets.singleton_2; reflexivity.
      }
    }
  Qed.

  Theorem mapAddPeerBPreservesB : forall (m : ByName.t t) (e f : B.t),
    mapInB f m -> mapInB f (addPeerB e m).
  Proof.
    intros m e f H_m.
    remember (ProtoIdentifier.name (B.supports f)) as f_name.
    remember (ProtoIdentifier.name (B.supports e)) as e_name.

    destruct (B.eq_dec e f) as [H_efEq|H_efNeq]. {
      subst f.
      apply mapInAddPeerB.
    } {
      destruct (String.string_dec e_name f_name) as [H_efnEq|H_efnNeq]. {
        unfold mapInB in *.
        unfold addPeerB.
        rewrite <- Heqf_name in *.
        rewrite <- Heqe_name in *.
        rewrite <- H_efnEq in *.
        destruct (ByName.find e_name m) as [sBefore|] eqn:H_find. {
          rewrite <- ByNameFacts.find_mapsto_iff in H_find.
          destruct H_m as [sx [H_sx0 H_sx1]].
          pose proof (ByNameFacts.MapsTo_fun H_find H_sx0) as H_same.
          subst sx.
          exists (addPeerBT sBefore e).
          constructor. {
            rewrite ByNameFacts.add_mapsto_iff.
            constructor. {
              constructor; reflexivity.
            }
          } {
            unfold addPeerBT.
            apply BSets.add_2.
            exact H_sx1.
          }
        } {
          destruct H_m as [sx [H_sx0 H_sx1]].
          pose proof (ByName.find_1 H_sx0) as H_contra.
          rewrite H_find in H_contra.
          inversion H_contra.
        }
      } {
        unfold mapInB in *.
        unfold addPeerB.
        rewrite <- Heqf_name in *.
        rewrite <- Heqe_name in *.
        destruct H_m as [sx [H_sx0 H_sx1]].
        exists sx.

        constructor. {
          destruct (ByName.find e_name m) as [sBefore|] eqn:H_find. {
            apply ByName.add_2.
            exact H_efnNeq.
            exact H_sx0.
          } {
            apply ByName.add_2.
            exact H_efnNeq.
            exact H_sx0.
          }
        } {
          exact H_sx1.
        }
      }
    }
  Qed.

  Theorem mapWFAddPeerB : forall (m : ByName.t t) (e : B.t),
    mapWF m -> mapWF (addPeerB e m).
  Proof.
    unfold mapWF.
    unfold addPeerB.
    intros m e H_wf.
    remember (ProtoIdentifier.name (B.supports e)) as e_name.
    intros s n H_mapsA.

    destruct (ByName.find e_name m) as [ex|] eqn:H_find. {
      rewrite <- ByNameFacts.find_mapsto_iff in H_find.
      rewrite ByNameFacts.add_mapsto_iff in H_mapsA.
      destruct H_mapsA as [[HL0 HL1]|[HR0 HR1]]. {
        rewrite <- HL0 in *.
        rewrite <- HL1.
        pose proof (H_wf _ _ H_find) as H_prevWF.
        symmetry in Heqe_name.
        apply (setsWFAddPeerBT _ _ _ H_prevWF Heqe_name).
      } {
        apply (H_wf _ _ HR1).
      }
    } {
      rewrite ByNameFacts.add_mapsto_iff in H_mapsA.
      destruct H_mapsA as [[HL0 HL1]|[HR0 HR1]]. {
        rewrite <- HL0 in *.
        rewrite <- HL1.
        rewrite Heqe_name.
        apply (setsWFSingletonBT e).
      } {
        apply (H_wf _ _ HR1).
      }
    }
  Qed.

  Theorem mapAddPeerAPreservesB : forall (m : ByName.t t) (e : A.t) (f : B.t),
    mapInB f m -> mapInB f (addPeerA e m).
  Proof.
    intros m e f H_in.
    unfold addPeerA.
    remember (ProtoIdentifier.name (A.supports e)) as e_name.
    remember (ProtoIdentifier.name (B.supports f)) as f_name.

    destruct (String.string_dec e_name f_name) as [H_nameEq|H_nameNeq]. {
      destruct H_in as [s [H_inL H_inR]].
      unfold mapInB.
      subst f_name.
      rewrite <- H_nameEq in *.
      destruct (ByName.find e_name m) as [ex|] eqn:H_find. {
        rewrite <- ByNameFacts.find_mapsto_iff in H_find.
        assert (s = ex) as H_exs by (apply (ByNameFacts.MapsTo_fun H_inL H_find)).
        subst ex.
        exists (addPeerAT s e).
        constructor. {
          apply ByName.add_1; reflexivity.
        } {
          exact H_inR.
        }
      } {
        rewrite ByNameFacts.find_mapsto_iff in H_inL.
        rewrite H_inL in H_find.
        inversion H_find.
      }
    } {
      destruct H_in as [s [H_inL H_inR]].
      exists s.
      destruct (ByName.find e_name m) as [ex|] eqn:H_find. {
        constructor. {
          apply ByName.add_2.
          rewrite <- Heqf_name.
          auto.
          auto.
        } {
          exact H_inR.
        }
      } {
        constructor. {
          apply ByName.add_2.
          rewrite <- Heqf_name.
          auto.
          auto.
        } {
          exact H_inR.
        }
      }
    }
  Qed.

  Theorem mapAddPeerBPreservesA : forall (m : ByName.t t) (e : B.t) (f : A.t),
    mapInA f m -> mapInA f (addPeerB e m).
  Proof.
    intros m e f H_in.
    unfold addPeerB.
    remember (ProtoIdentifier.name (B.supports e)) as e_name.
    remember (ProtoIdentifier.name (A.supports f)) as f_name.

    destruct (String.string_dec e_name f_name) as [H_nameEq|H_nameNeq]. {
      destruct H_in as [s [H_inL H_inR]].
      unfold mapInA.
      subst f_name.
      rewrite <- H_nameEq in *.
      destruct (ByName.find e_name m) as [ex|] eqn:H_find. {
        rewrite <- ByNameFacts.find_mapsto_iff in H_find.
        assert (s = ex) as H_exs by (apply (ByNameFacts.MapsTo_fun H_inL H_find)).
        subst ex.
        exists (addPeerBT s e).
        constructor. {
          apply ByName.add_1; reflexivity.
        } {
          exact H_inR.
        }
      } {
        rewrite ByNameFacts.find_mapsto_iff in H_inL.
        rewrite H_inL in H_find.
        inversion H_find.
      }
    } {
      destruct H_in as [s [H_inL H_inR]].
      exists s.
      destruct (ByName.find e_name m) as [ex|] eqn:H_find. {
        constructor. {
          apply ByName.add_2.
          rewrite <- Heqf_name.
          auto.
          auto.
        } {
          exact H_inR.
        }
      } {
        constructor. {
          apply ByName.add_2.
          rewrite <- Heqf_name.
          auto.
          auto.
        } {
          exact H_inR.
        }
      }
    }
  Qed.

  Definition addPeersA
    (es : list A.t)
    (m  : ByName.t t)
  : ByName.t t :=
    List.fold_right addPeerA m es.

  Theorem mapWFAddPeersA : forall (m : ByName.t t) (es : list A.t),
    mapWF m -> mapWF (addPeersA es m).
  Proof.
    intros m es.
    induction es as [|x xs]. {
      auto.
    } {
      intro H_m.
      simpl.
      apply mapWFAddPeerA.
      apply IHxs.
      exact H_m.
    }
  Qed.

  Theorem mapInAddPeersA : forall (m : ByName.t t) (es : list A.t),
    forall e, List.In e es -> mapInA e (addPeersA es m).
  Proof.
    intros m es.
    induction es as [|x xs]. {
      intros e H_nil.
      inversion H_nil.
    } {
      intros e H_in.
      simpl.
      destruct H_in as [H_inL|H_inR]. {
        subst x.
        apply mapInAddPeerA.
      } {
        apply mapAddPeerAPreservesA.
        apply (IHxs e H_inR).
      }
    }
  Qed.

  Definition addPeersB
    (es : list B.t)
    (m  : ByName.t t)
  : ByName.t t :=
    List.fold_right addPeerB m es.

  Theorem mapWFAddPeersB : forall (m : ByName.t t) (es : list B.t),
    mapWF m -> mapWF (addPeersB es m).
  Proof.
    intros m es.
    induction es as [|x xs]. {
      auto.
    } {
      intro H_m.
      simpl.
      apply mapWFAddPeerB.
      apply IHxs.
      exact H_m.
    }
  Qed.

  Theorem mapInAddPeersB : forall (m : ByName.t t) (es : list B.t),
    forall e, List.In e es -> mapInB e (addPeersB es m).
  Proof.
    intros m es.
    induction es as [|x xs]. {
      intros e H_nil.
      inversion H_nil.
    } {
      intros e H_in.
      simpl.
      destruct H_in as [H_inL|H_inR]. {
        subst x.
        apply mapInAddPeerB.
      } {
        apply mapAddPeerBPreservesB.
        apply (IHxs e H_inR).
      }
    }
  Qed.

  Theorem mapAddPeersAPreservesB : forall (m : ByName.t t) (es : list A.t) f,
    mapInB f m -> mapInB f (addPeersA es m).
  Proof.
    intros m es.
    induction es as [|x xs]. {
      intros f H_mIn.
      exact H_mIn.
    } {
      intros f H_mIn.
      simpl.
      apply mapAddPeerAPreservesB.
      apply IHxs.
      exact H_mIn.
    }
  Qed.

  Theorem mapAddPeersBPreservesA : forall (m : ByName.t t) (es : list B.t) f,
    mapInA f m -> mapInA f (addPeersB es m).
  Proof.
    intros m es.
    induction es as [|x xs]. {
      intros f H_mIn.
      exact H_mIn.
    } {
      intros f H_mIn.
      simpl.
      apply mapAddPeerBPreservesA.
      apply IHxs.
      exact H_mIn.
    }
  Qed.

  Theorem mapAddPeersAPreservesA : forall (m : ByName.t t) (es : list A.t) e,
    mapInA e m -> mapInA e (addPeersA es m).
  Proof.
    intros m es.
    induction es as [|x xs]. {
      intros f H_mIn.
      exact H_mIn.
    } {
      intros f H_mIn.
      simpl.
      apply mapAddPeerAPreservesA.
      apply IHxs.
      exact H_mIn.
    }
  Qed.

  Theorem mapAddPeersBPreservesB : forall (m : ByName.t t) (es : list B.t) e,
    mapInB e m -> mapInB e (addPeersB es m).
  Proof.
    intros m es.
    induction es as [|x xs]. {
      intros f H_mIn.
      exact H_mIn.
    } {
      intros f H_mIn.
      simpl.
      apply mapAddPeerBPreservesB.
      apply IHxs.
      exact H_mIn.
    }
  Qed.

  Definition addPeersSA
    (es : ASets.t)
    (m  : ByName.t t)
  : ByName.t t :=
    addPeersA (ASets.elements es) m.

  Theorem mapWFAddPeersSA : forall (m : ByName.t t) (es : ASets.t),
    mapWF m -> mapWF (addPeersSA es m).
  Proof.
    unfold addPeersSA.
    intros m es H_m.
    apply (mapWFAddPeersA _ _ H_m).
  Qed.

  Theorem mapInAddPeersSA : forall (m : ByName.t t) (es : ASets.t),
    forall e, ASets.In e es -> mapInA e (addPeersSA es m).
  Proof.
    intros m es e H_in.
    pose proof (ASets.elements_1 H_in) as H_sL.
    apply mapInAddPeersA.
    apply ListExts.InA_In.
    exact H_sL.
  Qed.

  Definition addPeersSB
    (es : BSets.t)
    (m  : ByName.t t)
  : ByName.t t :=
    addPeersB (BSets.elements es) m.

  Theorem mapWFAddPeersSB : forall (m : ByName.t t) (es : BSets.t),
    mapWF m -> mapWF (addPeersSB es m).
  Proof.
    unfold addPeersSB.
    intros m es H_m.
    apply (mapWFAddPeersB _ _ H_m).
  Qed.

  Theorem mapInAddPeersSB : forall (m : ByName.t t) (es : BSets.t),
    forall e, BSets.In e es -> mapInB e (addPeersSB es m).
  Proof.
    intros m es e H_in.
    pose proof (BSets.elements_1 H_in) as H_sL.
    apply mapInAddPeersB.
    apply ListExts.InA_In.
    exact H_sL.
  Qed.

  Theorem mapInAddPeersSAPreservesB : forall (m : ByName.t t) es f,
    mapInB f m -> mapInB f (addPeersSA es m).
  Proof.
    intros m es f H_minB.
    unfold addPeersSA.
    apply mapAddPeersAPreservesB.
    exact H_minB.
  Qed.

  Theorem mapInAddPeersSBPreservesA : forall (m : ByName.t t) es f,
    mapInA f m -> mapInA f (addPeersSB es m).
  Proof.
    intros m es f H_minA.
    unfold addPeersSB.
    apply mapAddPeersBPreservesA.
    exact H_minA.
  Qed.

  Lemma mapsToIn : forall (A : Type) (v : A) m k,
    ByName.MapsTo k v m -> List.In (k, v) (ByName.elements m).
  Proof.
    intros A v m k H_maps.
    rewrite ByNameFacts.elements_mapsto_iff in H_maps.
    induction H_maps as [p ps [HK0 HK1]|p ps HR]. {
      left.
      assert (fst p = k) as H_eqK
        by (rewrite HK0; reflexivity).
      assert (snd p = v) as H_eqV
        by (rewrite <- HK1; reflexivity).
      rewrite <- H_eqK.
      rewrite <- H_eqV.
      destruct p; reflexivity.
    } {
      right.
      exact IHHR.
    }
  Qed.

  Theorem mapAddPeersSAPreservesA : forall (m : ByName.t t) oSet f,
    mapInA f m -> mapInA f (addPeersSA oSet m).
  Proof.
    intros m oSet f H_minA.
    unfold addPeersSA.
    apply mapAddPeersAPreservesA.
    exact H_minA.
  Qed.

  Theorem mapInAddPeersSBPreservesB : forall (m : ByName.t t) oSet f,
    mapInB f m -> mapInB f (addPeersSB oSet m).
  Proof.
    intros m oSet f H_minB.
    unfold addPeersSB.
    apply mapAddPeersBPreservesB.
    exact H_minB.
  Qed.

  Definition collectProtocols
    (ma : ByName.t ASets.t)
    (mb : ByName.t BSets.t)
  : ByName.t t :=
    let init := ByName.empty t                    in
    let aes  := List.map snd (ByName.elements ma) in
    let bes  := List.map snd (ByName.elements mb) in
    let mwa  := List.fold_right addPeersSA init aes in
      List.fold_right addPeersSB mwa bes.

  Lemma collectProtocolsAL : forall (ma : ByName.t ASets.t) es,
    mapWF (List.fold_right addPeersSA (ByName.empty t) es).
  Proof.
    intros ma.
    induction es as [|y ys]. {
      apply mapWFEmpty.
    } {
      simpl.
      apply mapWFAddPeersSA.
      auto.
    }
  Qed.

  Lemma collectProtocolsBL : forall es m (ma : ByName.t BSets.t),
    mapWF m -> mapWF (List.fold_right addPeersSB m es).
  Proof.
    intros es.
    induction es as [|y ys]. {
      intros m mb H_mwf.
      exact H_mwf.
    } {
      intros m mb H_mwf.
      simpl.
      apply mapWFAddPeersSB.
      auto.
    }
  Qed.

  Theorem collectProtocolsWF : forall ma mb, mapWF (collectProtocols ma mb).
  Proof.
    intros ma mb.
    unfold collectProtocols.
    apply collectProtocolsBL; auto.
    apply collectProtocolsAL; auto.
  Qed.

  Theorem collectProtocolsInAL : forall ma a m,
    AC.mapIn a ma ->
      mapInA a (List.fold_right addPeersSA m (List.map snd (ByName.elements ma))).
  Proof.
    intros ma a m H_min.
    destruct H_min as [xSet [H_min0 H_min1]].
    pose proof (mapsToIn _ _ _ _ H_min0) as H_in0.
    pose proof (ListExts.InMapPair _ _ _ _ _ H_in0) as [H_in1 H_in2].
    clear H_in0.
    clear H_in1.

    induction (List.map snd (ByName.elements ma)) as [|ySet rSets]. {
      inversion H_in2.
    } {
      destruct H_in2 as [H_in0|H_in1]. {
        subst.
        apply mapInAddPeersSA.
        exact H_min1.
      } {
        pose proof (IHrSets H_in1) as H_inRsets.
        apply mapAddPeersSAPreservesA.
        exact H_inRsets.
      }
    }
  Qed.

  Theorem collectProtocolsInBL : forall mb b m,
    BC.mapIn b mb ->
      mapInB b (List.fold_right addPeersSB m (List.map snd (ByName.elements mb))).
  Proof.
    intros mb b m H_min.
    destruct H_min as [xSet [H_min0 H_min1]].
    pose proof (mapsToIn _ _ _ _ H_min0) as H_in0.
    pose proof (ListExts.InMapPair _ _ _ _ _ H_in0) as [H_in1 H_in2].
    clear H_in0.
    clear H_in1.

    induction (List.map snd (ByName.elements mb)) as [|ySet rSets]. {
      inversion H_in2.
    } {
      destruct H_in2 as [H_in0|H_in1]. {
        subst.
        apply mapInAddPeersSB.
        exact H_min1.
      } {
        pose proof (IHrSets H_in1) as H_inRsets.
        apply mapInAddPeersSBPreservesB.
        exact H_inRsets.
      }
    }
  Qed.

  Theorem collectProtocolsInALPB : forall m a es,
    mapInA a m -> mapInA a (List.fold_right addPeersSB m es).
  Proof.
    induction es as [|y ys]. {
      intros H_in; exact H_in.
    } {
      intros H_in.
      simpl.
      apply mapInAddPeersSBPreservesA.
      apply IHys.
      exact H_in.
    }
  Qed.

  Theorem collectProtocolsInA : forall ma mb (a : A.t),
    AC.mapIn a ma -> mapInA a (collectProtocols ma mb).
  Proof.
    intros ma mb a H_inA.
    destruct H_inA as [s [H_in0 H_in1]].
    unfold collectProtocols.
    apply collectProtocolsInALPB.
    apply collectProtocolsInAL.
    exists s; auto.
  Qed.

  Theorem collectProtocolsInB : forall ma mb (b : B.t),
    BC.mapIn b mb -> mapInB b (collectProtocols ma mb).
  Proof.
    intros ma mb b H_inB.
    destruct H_inB as [s [H_in0 H_in1]].
    unfold collectProtocols.
    apply collectProtocolsInBL.
    exists s; auto.
  Qed.

End CollectionOfProtocols.
