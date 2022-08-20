Require Coq.Structures.Equalities.
Require Coq.FSets.FSetAVL.
Require Coq.FSets.FSetWeakList.
Require Coq.FSets.FMapFacts.
Require Coq.Lists.List.

Require Genevan.ProtoIdentifier.
Require Genevan.ProtoName.
Require Genevan.ListExts.

(** * Peers

  The type of peers. A peer has decidable equality, and exposes a single 
  protocol identifier that represents the protocol the peer supports. *)

Module Type T.
  Include Equalities.UsualDecidableTypeOrig.

  (** The protocol the peer supports. *)

  Parameter supports : t -> ProtoIdentifier.t.
End T.

(** * Peer Sets

  The type of weak (unordered) sets of peers. *)

Module Type SetsT (P : T) :=
  FSetInterface.WS
    with Definition E.t  := P.t
    with Definition E.eq := P.eq.

(** * Collection 

    The types, functions, and theorems associated with the _collection_
    operation. 

    The _collection_ operation takes a list of peers and organizes them into a 
    map indexed by protocol names. For any given peer _p_ supporting a protocol
    with name _n_ in a set of peers _s_, the _collection_ operation will result
    in a map containing a mapping from _n_ to a set _t_ such that _p_ ∈ _t_. *)

Module Type CollectionT (P : T) (S : SetsT P).

  (** A proposition that says that all peers within a set have the
      name _n_. *)

  Definition setsHaveName
    (s : S.t)
    (n : ProtoName.t)
  : Prop :=
    S.For_all (fun h => ProtoIdentifier.name (P.supports h) = n) s.

  (** Adding a peer with name _n_ to a set of peers that have name _n_ means
      that all peers in the set have name _n_. *)

  Parameter setsHaveNameAdd : forall s n e,
    setsHaveName s n ->
      ProtoIdentifier.name (P.supports e) = n ->
        setsHaveName (S.add e s) n.

  (** A singleton set containing a peer with name _n_ implies that all peers in
     the set have name _n_. *)

  Parameter setsHaveNameSingleton : forall e,
    setsHaveName (S.singleton e) (ProtoIdentifier.name (P.supports e)).

  (** A proposition that states that a set is not empty. *)

  Definition setsNonEmpty (s : S.t) : Prop :=
    ~S.Empty s.

  (** The combination of propositions that indicate that a set of peers is 
      well-formed. *)

  Definition setsWF
    (s : S.t)
    (n : ProtoName.t)
  : Prop :=
    (setsHaveName s n) /\ setsNonEmpty s.

  (** An abbreviation for the _ProtoName_ maps. *)

  Module ByName := ProtoName.Maps.

  (** A proposition that says that if a set of peers exists in a map, then
      the set of peers is non-empty. *)

  Definition mapSetsNonEmpty (m : ByName.t S.t) : Prop :=
    forall s n, ByName.MapsTo n s m -> setsNonEmpty s.

  (** A proposition that says that if a set of peers exists in a map at key _n_,
      then all peers in the set have name _n_. *)

  Definition mapSetsHaveNames (m : ByName.t S.t) : Prop :=
    forall s n, ByName.MapsTo n s m -> setsHaveName s n.

  (** A proposition that says that if a set of peers exists in a map at key _n_,
      then the set is well-formed. *)

  Definition mapSetsWF (m : ByName.t S.t) : Prop :=
    mapSetsNonEmpty m /\ mapSetsHaveNames m.

  (** A proposition that says that a peer exists in the set in a map at key 
      _n_. *)

  Definition mapIn (e : P.t) (m : ByName.t S.t) : Prop :=
    exists s, ByName.MapsTo (ProtoIdentifier.name (P.supports e)) s m /\ S.In e s.

  (** A function that adds a peer to a map. *)

  Parameter addPeer : forall (e : P.t) (m : ByName.t S.t), ByName.t S.t.

  (** A proof that _addPeer_ preserves _mapSetsNonEmpty_. *)

  Parameter addPeerSetsNonEmpty : forall m e,
    mapSetsNonEmpty m -> mapSetsNonEmpty (addPeer e m).

  (** A proof that _addPeer_ preserves _mapSetsHaveNames_. *)

  Parameter addPeerSetsHaveName : forall m e,
    mapSetsHaveNames m -> mapSetsHaveNames (addPeer e m).

  (** A proof that _addPeer_ implies _mapIn_. *)

  Parameter addPeerIn : forall m e,
    mapIn e (addPeer e m).

  (** A proof that _addPeer_ preserves _mapIn_ for all peers in a map. *)

  Parameter addPeerInPreserve : forall m e f,
    mapIn f m -> mapIn f (addPeer e m).

  (** A proof that _addPeer_ preserves _mapSetsWF_. *)

  Parameter addPeerSetsWF : forall m e,
    mapSetsWF m -> mapSetsWF (addPeer e m).

  (** A proof that the empty map vacuously has well-formed peer sets. *)

  Parameter addPeerSetsWFEmpty : mapSetsWF (ByName.empty S.t).

  (** A function to produce a map from a list of peers. *)

  Parameter addPeers : forall (peers : list P.t), ByName.t S.t.

  (** A proof that every element in the input list is in the map produced
      by _addPeers_. *)

  Parameter addPeersIn : forall es e,
    List.In e es -> mapIn e (addPeers es).

  (** The actual _collect_ function that implements the collection algorithm. *)

  Definition collect := addPeers.

End CollectionT.

(** A concrete implementation of the _CollectionT_ interface. *)

Module Collection (P : T) (S : SetsT P) : CollectionT P S.

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

End Collection.

(** * CollectionOfProtocols

    The types, functions, and theorems associated with the
    _collectionOfProtocols_ operation. 

    The _collectionOfProtocols_ operation associates the protocols supported by
    a collection of peers of type _A_ with the protocols supported by a
    collection of peers of type _B_. It aims to produce a map where each key
    is a protocol name _n_, and the associated value is a pair of sets of peers
    that all support protocol _n_. Note that it is possible and entirely
    reasonable for one set of peers in a pair to be empty; if the peers in
    one set represent client protocol handlers, and the peers in the other set
    represent server endpoints, then there may be support for a protocol on
    client side, but not on the server side, and vice versa. It is _not_
    reasonable, however, for both sets to be empty: If there are no peers at
    all that support a given protocol, then the name of the protocol could not
    have reasonably been introduced in the first place.
*)

Module Type CollectionOfProtocolsT
  (A     : T)
  (ASets : SetsT A)
  (AC    : CollectionT A ASets)
  (B     : T)
  (BSets : SetsT B)
  (BC    : CollectionT B BSets).

  (** A pair of sets of peers. *)

  Record t := {
    peersA : ASets.t;
    peersB : BSets.t
  }.

  (** A proposition that says that all peers within both sets have the
      name _n_. *)

  Definition setsHaveName (p : t) (n : ProtoName.t) : Prop :=
    AC.setsHaveName (peersA p) n /\ BC.setsHaveName (peersB p) n.

  (** A proposition that says that either one of the sets of peers must be
      non-empty. *)

  Definition setsEitherNonEmpty (p : t) : Prop :=
    AC.setsNonEmpty (peersA p) \/ BC.setsNonEmpty (peersB p).

  (** The combination of propositions that indicate that a pair of sets of 
      peers is well-formed. *)

  Definition setsWF (p : t) (n : ProtoName.t) : Prop :=
    setsHaveName p n /\ setsEitherNonEmpty p.

  Module ByName := ProtoName.Maps.

  (** A proposition that states that all pairs of sets of peers in a given are
      well-formed. *)

  Definition mapWF (m : ByName.t t) : Prop :=
    forall s n, ByName.MapsTo n s m -> setsWF s n.

  (** A proposition that states that a given peer is in the A-side set of
      peers within the map. *)

  Definition mapInA (e : A.t) (m : ByName.t t) : Prop :=
    exists s, ByName.MapsTo (ProtoIdentifier.name (A.supports e)) s m /\ ASets.In e (peersA s).

  (** A proposition that states that a given peer is in the B-side set of
      peers within the map. *)

  Definition mapInB (e : B.t) (m : ByName.t t) : Prop :=
    exists s, ByName.MapsTo (ProtoIdentifier.name (B.supports e)) s m /\ BSets.In e (peersB s).

  (** The empty map is well-formed. *)

  Parameter mapWFEmpty : mapWF (ByName.empty t).

  (** No peer is in the empty map on the A-side. *)

  Parameter mapInAEmptyFalse : forall a, ~mapInA a (ByName.empty t).

  (** No peer is in the empty map on the B-side. *)

  Parameter mapInBEmptyFalse : forall a, ~mapInB a (ByName.empty t).

  (** A function to add a peer to the A-side of the map. *)

  Parameter addPeerA : forall (e : A.t) (m : ByName.t t), ByName.t t.

  (** _addPeerA_ preserves well-formedness. *)

  Parameter mapWFAddPeerA : forall (m : ByName.t t) (e : A.t),
    mapWF m -> mapWF (addPeerA e m).

  (** _addPeerA_ preserves the presence of other peers in the map. *)

  Parameter mapInPreservesAddPeerA : forall (m : ByName.t t) (e f : A.t),
    mapInA f m -> mapInA f (addPeerA e m).

  (** A function to add a peer to the B-side of the map. *)

  Parameter addPeerB : forall (e : B.t) (m : ByName.t t), ByName.t t.

  (** _addPeerB_ preserves well-formedness. *)

  Parameter mapWFAddPeerB : forall (m : ByName.t t) (e : B.t),
    mapWF m -> mapWF (addPeerB e m).

  (** _addPeerB_ preserves the presence of other peers in the map. *)

  Parameter mapInPreservesAddPeerB : forall (m : ByName.t t) (e f : B.t),
    mapInB f m -> mapInB f (addPeerB e m).

  (** _addPeerA_ preserves the presence of other peers on the B-side. *)

  Parameter mapAddPeerAPreservesB : forall m e f,
    mapInB f m -> mapInB f (addPeerA e m).

  (** _addPeerB_ preserves the presence of other peers on the A-side. *)

  Parameter mapAddPeerBPreservesA : forall m e f,
    mapInA f m -> mapInA f (addPeerB e m).

  (** A function to add a list of peers to the A-side of the map. *)

  Parameter addPeersA : forall (es : list A.t) (m : ByName.t t), ByName.t t.

  (** _addPeersA_ preserves well-formedness. *)

  Parameter mapWFAddPeersA : forall (m : ByName.t t) (es : list A.t),
    mapWF m -> mapWF (addPeersA es m).

  (** A function to add a list of peers to the B-side of the map. *)

  Parameter addPeersB : forall (es : list B.t) (m : ByName.t t), ByName.t t.

  (** _addPeersB_ preserves well-formedness. *)

  Parameter mapWFAddPeersB : forall (m : ByName.t t) (es : list B.t),
    mapWF m -> mapWF (addPeersB es m).

  (** _addPeersA_ preserves peers on the B-side. *)

  Parameter mapInAddPeersAPreservesB : forall m es f,
    mapInB f m -> mapInB f (addPeersA es m).

  (** _addPeersB_ preserves peers on the A-side. *)

  Parameter mapInAddPeersBPreservesA : forall m es f,
    mapInA f m -> mapInA f (addPeersB es m).

  (** A function to add a set of peers to the A-side of the map. *)

  Parameter addPeersSA : forall (es : ASets.t) (m : ByName.t t), ByName.t t.

  (** _addPeersSA_ preserves well-formedness. *)

  Parameter mapWFAddPeersSA : forall (m : ByName.t t) (es : ASets.t),
    mapWF m -> mapWF (addPeersSA es m).

  (** _addPeersSA_ preserves the presence of other peers in the map. *)

  Parameter mapInAddPeersSA : forall (m : ByName.t t) (es : ASets.t),
    forall e, ASets.In e es -> mapInA e (addPeersSA es m).

  (** A function to add a set of peers to the B-side of the map. *)

  Parameter addPeersSB : forall (es : BSets.t) (m : ByName.t t), ByName.t t.

  (** _addPeersSB_ preserves well-formedness. *)

  Parameter mapWFAddPeersSB : forall (m : ByName.t t) (es : BSets.t),
    mapWF m -> mapWF (addPeersSB es m).

  (** _addPeersSB_ preserves the presence of other peers in the map. *)

  Parameter mapInAddPeersSB : forall (m : ByName.t t) (es : BSets.t),
    forall e, BSets.In e es -> mapInB e (addPeersSB es m).

  (** The actual function that collects pairs of sets of peers into a single
      map. *)

  Parameter collectProtocols : forall
    (ma : ByName.t ASets.t)
    (mb : ByName.t BSets.t), ByName.t t.

  (** A proof that the collection function produces maps of sets that are
      well-formed. *)

  Parameter collectProtocolsWF : forall ma mb,
    mapWF (collectProtocols ma mb).

End CollectionOfProtocolsT.

(** A concrete implementation of the _CollectionOfProtocolsT_ interface. *)

Module CollectionOfProtocols
  (A     : T)
  (ASets : SetsT A)
  (AC    : CollectionT A ASets)
  (B     : T)
  (BSets : SetsT B)
  (BC    : CollectionT B BSets)
: CollectionOfProtocolsT A ASets AC B BSets BC.

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

  Theorem mapInPreservesAddPeerA : forall (m : ByName.t t) (e f : A.t),
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

  Theorem mapInPreservesAddPeerB : forall (m : ByName.t t) (e f : B.t),
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
        apply mapInPreservesAddPeerA.
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
        apply mapInPreservesAddPeerB.
        apply (IHxs e H_inR).
      }
    }
  Qed.

  Theorem mapInAddPeersAPreservesB : forall (m : ByName.t t) (es : list A.t) f,
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

  Theorem mapInAddPeersBPreservesA : forall (m : ByName.t t) (es : list B.t) f,
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

  Theorem mapInAddPeersAPreservesA : forall (m : ByName.t t) (es : list A.t) e,
    mapInA e m -> mapInA e (addPeersA es m).
  Proof.
    intros m es.
    induction es as [|x xs]. {
      intros f H_mIn.
      exact H_mIn.
    } {
      intros f H_mIn.
      simpl.
      apply mapInPreservesAddPeerA.
      apply IHxs.
      exact H_mIn.
    }
  Qed.

  Theorem mapInAddPeersBPreservesB : forall (m : ByName.t t) (es : list B.t) e,
    mapInB e m -> mapInB e (addPeersB es m).
  Proof.
    intros m es.
    induction es as [|x xs]. {
      intros f H_mIn.
      exact H_mIn.
    } {
      intros f H_mIn.
      simpl.
      apply mapInPreservesAddPeerB.
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
    apply mapInAddPeersAPreservesB.
    exact H_minB.
  Qed.

  Theorem mapInAddPeersSBPreservesA : forall (m : ByName.t t) es f,
    mapInA f m -> mapInA f (addPeersSB es m).
  Proof.
    intros m es f H_minA.
    unfold addPeersSB.
    apply mapInAddPeersBPreservesA.
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

  Theorem mapInAddPeersSAPreservesA : forall (m : ByName.t t) oSet f,
    mapInA f m -> mapInA f (addPeersSA oSet m).
  Proof.
    intros m oSet f H_minA.
    unfold addPeersSA.
    apply mapInAddPeersAPreservesA.
    exact H_minA.
  Qed.

  Theorem mapInAddPeersSBPreservesB : forall (m : ByName.t t) oSet f,
    mapInB f m -> mapInB f (addPeersSB oSet m).
  Proof.
    intros m oSet f H_minB.
    unfold addPeersSB.
    apply mapInAddPeersBPreservesB.
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
        apply mapInAddPeersSAPreservesA.
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
