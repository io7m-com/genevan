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

(** A concrete implementation of the _CollectionT_ interface. *)

Module Make (P : Peer.T) (S : Peer.SetsT P) : CollectionT.S P S.

  Module F := FSetFacts.WFacts S.

  Definition setsHaveName
    (s : S.t)
    (n : ProtoName.t)
  : Prop :=
    S.For_all (fun h => ProtoIdentifier.name (P.supports h) = n) s.

  Theorem setsHaveNameAdd : forall s n e,
    setsHaveName s n ->
      ProtoIdentifier.name (P.supports e) = n ->
        setsHaveName (S.add e s) n.
  Proof.
    intros s n e H_before H_nameEq.
    unfold setsHaveName in *.
    unfold S.For_all in *.
    intros f H_inF.
    rewrite F.add_iff in H_inF.
    destruct H_inF as [HL|HR]. {
      rewrite HL in *.
      exact H_nameEq.
    } {
      apply (H_before _ HR).
    }
  Qed.

  Theorem setsHaveNameSingleton : forall e,
    setsHaveName (S.singleton e) (ProtoIdentifier.name (P.supports e)).
  Proof.
    intros e.
    unfold setsHaveName in *.
    unfold S.For_all in *.
    intros f H_inF.
    rewrite F.singleton_iff in H_inF.
    rewrite H_inF in *.
    reflexivity.
  Qed.

  Definition setsNonEmpty (s : S.t) : Prop :=
    ~S.Empty s.

  Definition setsWF
    (s : S.t)
    (n : ProtoName.t)
  : Prop :=
    (setsHaveName s n) /\ setsNonEmpty s.

  Module ByName      := ProtoName.Maps.
  Module ByNameFacts := ProtoName.MapsFacts.

  Definition mapSetsNonEmpty (m : ByName.t S.t) : Prop :=
    forall s n, ByName.MapsTo n s m -> setsNonEmpty s.

  Definition mapSetsHaveNames (m : ByName.t S.t) : Prop :=
    forall s n, ByName.MapsTo n s m -> setsHaveName s n.

  Definition mapSetsWF (m : ByName.t S.t) : Prop :=
    mapSetsNonEmpty m /\ mapSetsHaveNames m.

  Definition mapIn (e : P.t) (m : ByName.t S.t) : Prop :=
    exists s, ByName.MapsTo (ProtoIdentifier.name (P.supports e)) s m /\ S.In e s.

  Definition addPeer
    (e : P.t)
    (m : ByName.t S.t)
  : ByName.t S.t :=
    let name := ProtoIdentifier.name (P.supports e) in
      match ByName.find name m with
      | Some existingEndpoints => ByName.add name (S.add e existingEndpoints) m
      | None                   => ByName.add name (S.singleton e) m
      end.

  Theorem addPeerSetsNonEmpty : forall m e,
    mapSetsNonEmpty m -> mapSetsNonEmpty (addPeer e m).
  Proof.
    intros m e.
    intros H_correctB.
    intros sAfter n H_mapsA.

    unfold mapSetsNonEmpty in *.
    unfold setsNonEmpty in *.
    unfold addPeer in H_mapsA.

    remember (ProtoIdentifier.name (P.supports e)) as e_name.

    destruct (ByName.find e_name m) as [sBefore|] eqn:H_find. {
      rewrite <- ByNameFacts.find_mapsto_iff in H_find.
      rewrite ByNameFacts.add_mapsto_iff in H_mapsA.
      destruct H_mapsA as [[H0L H0R]|[H1L H1R]]. {
        assert (S.In e (S.add e sBefore)) as H_in
          by (apply S.add_1; reflexivity).
        rewrite H0R in H_in.
        unfold S.Empty.
        unfold not; intro H_contra.
        apply (H_contra e H_in).
      } {
        apply (H_correctB _ _ H1R).
      }
    } {
      rewrite ByNameFacts.add_mapsto_iff in H_mapsA.
      destruct H_mapsA as [[H0L H0R]|[H1L H1R]]. {
        assert (S.In e (S.singleton e)) as H_in
          by (apply S.singleton_2; reflexivity).
        rewrite H0R in H_in.
        unfold S.Empty.
        unfold not; intro H_contra.
        apply (H_contra e H_in).
      } {
        apply (H_correctB _ _ H1R).
      }
    }
  Qed.

  Theorem addPeerSetsHaveName : forall m e,
    mapSetsHaveNames m -> mapSetsHaveNames (addPeer e m).
  Proof.
    intros m e.
    intros H_correctB.
    intros sAfter n H_mapsA.
    unfold addPeer in H_mapsA.

    remember (ProtoIdentifier.name (P.supports e)) as e_name.

    destruct (ByName.find e_name m) as [sBefore|] eqn:H_find. {
      rewrite <- ByNameFacts.find_mapsto_iff in H_find.
      rewrite ByNameFacts.add_mapsto_iff in H_mapsA.
      destruct H_mapsA as [[H0L H0R]|[H1L H1R]]. {
        unfold mapSetsHaveNames in H_correctB.
        pose proof (H_correctB _ _ H_find) as H_namesBefore.
        rewrite <- H0R.
        apply setsHaveNameAdd.
        rewrite <- H0L.
        exact H_namesBefore.
        rewrite <- Heqe_name.
        rewrite H0L.
        reflexivity.
      } {
        apply (H_correctB _ _ H1R).
      }
    } {
      rewrite ByNameFacts.add_mapsto_iff in H_mapsA.
      destruct H_mapsA as [[H0L H0R]|[H1L H1R]]. {
        rewrite <- H0R.
        rewrite <- H0L.
        rewrite Heqe_name.
        apply setsHaveNameSingleton.
      } {
        apply (H_correctB _ _ H1R).
      }
    }
  Qed.

  Theorem addPeerIn : forall m e,
    mapIn e (addPeer e m).
  Proof.
    intros m e.
    unfold mapIn.
    unfold addPeer.
    remember (ProtoIdentifier.name (P.supports e)) as e_name.

    destruct (ByName.find e_name m) as [sBefore|] eqn:H_find. {
      rewrite <- ByNameFacts.find_mapsto_iff in H_find.
      exists (S.add e sBefore).
      rewrite ByNameFacts.add_mapsto_iff.
      constructor. {
        left; constructor; reflexivity.
      } {
        apply S.add_1; reflexivity.
      }
    } {
      exists (S.singleton e).
      rewrite ByNameFacts.add_mapsto_iff.
      constructor. {
        left; constructor; reflexivity.
      } {
        apply S.singleton_2; reflexivity.
      }
    }
  Qed.

  Theorem addPeerInPreserve : forall m e f,
    mapIn f m -> mapIn f (addPeer e m).
  Proof.
    intros m e f H_fIn.
    remember (ProtoIdentifier.name (P.supports f)) as f_name.
    remember (ProtoIdentifier.name (P.supports e)) as e_name.

    destruct (P.eq_dec e f) as [H_efEq|H_efNeq]. {
      subst f.
      apply addPeerIn.
    } {
      destruct (String.string_dec e_name f_name) as [H_efnEq|H_efnNeq]. {
        unfold mapIn in *.
        unfold addPeer.
        rewrite <- Heqf_name in *.
        rewrite <- Heqe_name in *.
        rewrite <- H_efnEq in *.
        destruct (ByName.find e_name m) as [sBefore|] eqn:H_find. {
          rewrite <- ByNameFacts.find_mapsto_iff in H_find.
          destruct H_fIn as [sx [H_sx0 H_sx1]].
          pose proof (ProtoName.MapsFacts.MapsTo_fun H_find H_sx0) as H_same.
          subst sx.
          exists (S.add e sBefore).
          constructor. {
            rewrite ProtoName.MapsFacts.add_mapsto_iff.
            constructor. {
              constructor; reflexivity.
            }
          } {
            apply S.add_2.
            exact H_sx1.
          }
        } {
          destruct H_fIn as [sx [H_sx0 H_sx1]].
          pose proof (ProtoName.Maps.find_1 H_sx0) as H_contra.
          rewrite H_find in H_contra.
          inversion H_contra.
        }
      } {
        unfold mapIn in *.
        unfold addPeer.
        rewrite <- Heqf_name in *.
        rewrite <- Heqe_name in *.
        destruct H_fIn as [sx [H_sx0 H_sx1]].
        exists sx.

        constructor. {
          destruct (ByName.find e_name m) as [sBefore|] eqn:H_find. {
            apply ProtoName.Maps.add_2.
            exact H_efnNeq.
            exact H_sx0.
          } {
            apply ProtoName.Maps.add_2.
            exact H_efnNeq.
            exact H_sx0.
          }
        } {
          exact H_sx1.
        }
      }
    }
  Qed.

  Theorem addPeerSetsWF : forall m e,
    mapSetsWF m -> mapSetsWF (addPeer e m).
  Proof.
    intros m e H_correctB.
    destruct H_correctB as [Hc0 Hc1].

    constructor. {
      apply (addPeerSetsNonEmpty m e).
      exact Hc0.
    } {
      apply (addPeerSetsHaveName m e).
      exact Hc1.
    }
  Qed.

  Theorem addPeerSetsWFEmpty : mapSetsWF (ByName.empty S.t).
  Proof.
    constructor;
    (hnf; intros; rewrite ByNameFacts.empty_mapsto_iff in *; contradiction).
  Qed.

  Definition addPeers (peers : list P.t) : ByName.t S.t :=
    List.fold_right addPeer (ByName.empty S.t) peers.

  Theorem addPeersWF : forall es,
    mapSetsWF (addPeers es).
  Proof.
    induction es as [|e e_rest]. {
      apply addPeerSetsWFEmpty.
    } {
      apply (addPeerSetsWF _ e IHe_rest).
    }
  Qed.

  Theorem addPeersIn : forall es e,
    List.In e es -> mapIn e (addPeers es).
  Proof.
    induction es as [|f fs]. {
      intros e H_in.
      inversion H_in.
    } {
      intros x H_inx.
      simpl.
      destruct H_inx as [H_inL|H_inR]. {
        subst x.
        apply addPeerIn.
      } {
        pose proof (IHfs x H_inR) as H_mInX.
        apply addPeerInPreserve.
        exact H_mInX.
      }
    }
  Qed.

  Definition collect := addPeers.

End Make.
