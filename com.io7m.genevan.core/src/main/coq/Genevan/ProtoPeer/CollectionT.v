Require Coq.Structures.Equalities.
Require Coq.FSets.FSetAVL.
Require Coq.FSets.FSetWeakList.
Require Coq.FSets.FMapFacts.
Require Coq.Lists.List.

Require Genevan.ProtoIdentifier.
Require Genevan.ProtoName.
Require Genevan.ListExts.
Require Genevan.ProtoPeer.Peer.

(** * Collection

    The types, functions, and theorems associated with the _collection_
    operation.

    The _collection_ operation takes a list of peers and organizes them into a
    map indexed by protocol names. For any given peer _p_ supporting a protocol
    with name _n_ in a set of peers _s_, the _collection_ operation will result
    in a map containing a mapping from _n_ to a set _t_ such that _p_ ∈ _t_. *)

Module Type S (P : Peer.T) (S : Peer.SetsT P).

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

End S.
