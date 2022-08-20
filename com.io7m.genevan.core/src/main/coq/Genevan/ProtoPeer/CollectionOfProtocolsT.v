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

(** * CollectionOfProtocols

    The types, functions, and theorems associated with the
    _collectionOfProtocols_ operation.

    The _collectionOfProtocols_ operation associates the protocols supported
    by a collection of peers of type _A_ with the protocols supported by
    a collection of peers of type _B_. It aims to produce a map where each
    key is a protocol name _n_, and the associated value is a pair of sets
    of peers that all support protocol _n_.

    Note that it is possible and entirely reasonable for one set of peers
    in a pair to be empty; if the peers in one set represent client protocol
    handlers, and the peers in the other set represent server endpoints, then
    there may be support for a protocol on client side, but not on the server
    side, and vice versa. It is _not_ reasonable, however, for both sets to
    be empty: If there are no peers at all that support a given protocol,
    then the name of the protocol could not have reasonably been introduced
    in the first place.
*)

Module Type S
  (A     : Peer.T)
  (ASets : Peer.SetsT A)
  (AC    : CollectionT.S A ASets)
  (B     : Peer.T)
  (BSets : Peer.SetsT B)
  (BC    : CollectionT.S B BSets).

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

  (** An abbreviation for the ProtoName maps module. *)

  Module ByName := ProtoName.Maps.

  (** A proposition that states that all pairs of sets of peers in a given are
      well-formed. *)

  Definition mapWF (m : ByName.t t) : Prop :=
    forall s n, ByName.MapsTo n s m -> setsWF s n.

  (** A proposition that states that a given peer is in the A-side set of
      peers within the map. *)

  Definition mapInA (e : A.t) (m : ByName.t t) : Prop :=
    exists s, ByName.MapsTo (ProtoIdentifier.name (A.supports e)) s m 
      /\ ASets.In e (peersA s).

  (** A proposition that states that a given peer is in the B-side set of
      peers within the map. *)

  Definition mapInB (e : B.t) (m : ByName.t t) : Prop :=
    exists s, ByName.MapsTo (ProtoIdentifier.name (B.supports e)) s m 
      /\ BSets.In e (peersB s).

  (** The empty map is well-formed. *)

  Parameter mapWFEmpty : mapWF (ByName.empty t).

  (** No peer is in the empty map on the A-side. *)

  Parameter mapInAEmptyFalse : forall a, ~mapInA a (ByName.empty t).

  (** No peer is in the empty map on the B-side. *)

  Parameter mapInBEmptyFalse : forall a, ~mapInB a (ByName.empty t).

  (** ** addPeerA *)

  (** A function to add a peer to the A-side of the map. *)

  Parameter addPeerA : forall (e : A.t) (m : ByName.t t), ByName.t t.

  (** _addPeerA_ preserves well-formedness. *)

  Parameter mapWFAddPeerA : forall (m : ByName.t t) (e : A.t),
    mapWF m -> mapWF (addPeerA e m).

  (** _addPeerA_ adds peers to a map. *)

  Parameter mapInAddPeerA : forall (m : ByName.t t) (e : A.t),
    mapInA e (addPeerA e m).

  (** _addPeerA_ preserves the presence of other peers in the map. *)

  Parameter mapAddPeerAPreservesA : forall (m : ByName.t t) (e f : A.t),
    mapInA f m -> mapInA f (addPeerA e m).

  (** _addPeerA_ preserves the presence of other peers on the B-side. *)

  Parameter mapAddPeerAPreservesB : forall m e f,
    mapInB f m -> mapInB f (addPeerA e m).

  (** ** addPeerB *)

  (** A function to add a peer to the B-side of the map. *)

  Parameter addPeerB : forall (e : B.t) (m : ByName.t t), ByName.t t.

  (** _addPeerB_ preserves well-formedness. *)

  Parameter mapWFAddPeerB : forall (m : ByName.t t) (e : B.t),
    mapWF m -> mapWF (addPeerB e m).

  (** _addPeerB_ adds peers to a map. *)

  Parameter mapInAddPeerB : forall (m : ByName.t t) (e : B.t),
    mapInB e (addPeerB e m).

  (** _addPeerB_ preserves the presence of other peers in the map. *)

  Parameter mapAddPeerBPreservesB : forall (m : ByName.t t) (e f : B.t),
    mapInB f m -> mapInB f (addPeerB e m).

  (** _addPeerB_ preserves the presence of other peers on the A-side. *)

  Parameter mapAddPeerBPreservesA : forall m e f,
    mapInA f m -> mapInA f (addPeerB e m).

  (** ** addPeersA *)

  (** A function to add a list of peers to the A-side of the map. *)

  Parameter addPeersA : forall (es : list A.t) (m : ByName.t t), ByName.t t.

  (** _addPeersA_ preserves well-formedness. *)

  Parameter mapWFAddPeersA : forall (m : ByName.t t) (es : list A.t),
    mapWF m -> mapWF (addPeersA es m).

  (** _addPeersA_ adds peers to a map. *)

  Parameter mapInAddPeersA : forall (m : ByName.t t) (es : list A.t),
    forall e, List.In e es -> mapInA e (addPeersA es m).

  (** _addPeersA_ preserves peers on the A-side. *)

  Parameter mapAddPeersAPreservesA : forall (m : ByName.t t) (es : list A.t) e,
    mapInA e m -> mapInA e (addPeersA es m).

  (** _addPeersA_ preserves peers on the B-side. *)

  Parameter mapAddPeersAPreservesB : forall m es f,
    mapInB f m -> mapInB f (addPeersA es m).

  (** ** addPeersB *)

  (** A function to add a list of peers to the B-side of the map. *)

  Parameter addPeersB : forall (es : list B.t) (m : ByName.t t), ByName.t t.

  (** _addPeersB_ preserves well-formedness. *)

  Parameter mapWFAddPeersB : forall (m : ByName.t t) (es : list B.t),
    mapWF m -> mapWF (addPeersB es m).

  (** _addPeersB_ adds peers to a map. *)

  Parameter mapInAddPeersB : forall (m : ByName.t t) (es : list B.t),
    forall e, List.In e es -> mapInB e (addPeersB es m).

  (** _addPeersB_ preserves peers on the A-side. *)

  Parameter mapAddPeersBPreservesA : forall m es f,
    mapInA f m -> mapInA f (addPeersB es m).

  (** _addPeersB_ preserves peers on the B-side. *)

  Parameter mapAddPeersBPreservesB : forall (m : ByName.t t) (es : list B.t) e,
    mapInB e m -> mapInB e (addPeersB es m).

  (** ** addPeersSA *)

  (** A function to add a set of peers to the A-side of the map. *)

  Parameter addPeersSA : forall (es : ASets.t) (m : ByName.t t), ByName.t t.

  (** _addPeersSA_ preserves well-formedness. *)

  Parameter mapWFAddPeersSA : forall (m : ByName.t t) (es : ASets.t),
    mapWF m -> mapWF (addPeersSA es m).

  (** _addPeersSA_ preserves the presence of other peers in the map. *)

  Parameter mapInAddPeersSA : forall (m : ByName.t t) (es : ASets.t),
    forall e, ASets.In e es -> mapInA e (addPeersSA es m).

  (** _addPeersSA_ preserves the presence of other peers in the map. *)

  Parameter mapAddPeersSAPreservesA : forall (m : ByName.t t) oSet f,
    mapInA f m -> mapInA f (addPeersSA oSet m).

  (** _addPeersSA_ preserves the presence of other peers in the map. *)

  Parameter mapInAddPeersSAPreservesB : forall (m : ByName.t t) es f,
    mapInB f m -> mapInB f (addPeersSA es m).

  (** ** addPeersSB *)

  (** A function to add a set of peers to the B-side of the map. *)

  Parameter addPeersSB : forall (es : BSets.t) (m : ByName.t t), ByName.t t.

  (** _addPeersSB_ preserves well-formedness. *)

  Parameter mapWFAddPeersSB : forall (m : ByName.t t) (es : BSets.t),
    mapWF m -> mapWF (addPeersSB es m).

  (** _addPeersSB_ preserves the presence of other peers in the map. *)

  Parameter mapInAddPeersSBPreservesB : forall (m : ByName.t t) oSet f,
    mapInB f m -> mapInB f (addPeersSB oSet m).

  (** _addPeersSB_ preserves the presence of other peers in the map. *)

  Parameter mapInAddPeersSBPreservesA : forall (m : ByName.t t) es f,
    mapInA f m -> mapInA f (addPeersSB es m).

  (** _addPeersSB_ preserves the presence of other peers in the map. *)

  Parameter mapInAddPeersSB : forall (m : ByName.t t) (es : BSets.t),
    forall e, BSets.In e es -> mapInB e (addPeersSB es m).

  (** ** collectProtocols *)

  (** The actual function that collects pairs of sets of peers into a single
      map. *)

  Parameter collectProtocols : forall
    (ma : ByName.t ASets.t)
    (mb : ByName.t BSets.t), ByName.t t.

  (** A proof that the collection function produces maps of sets that are
      well-formed. *)

  Parameter collectProtocolsWF : forall ma mb,
    mapWF (collectProtocols ma mb).

  (** A proof that all members of the original collection will be present
      in the resulting by-protocol collection. *)

  Parameter collectProtocolsInA : forall ma mb (a : A.t),
    AC.mapIn a ma -> mapInA a (collectProtocols ma mb).

  (** A proof that all members of the original collection will be present
      in the resulting by-protocol collection. *)

  Parameter collectProtocolsInB : forall ma mb (b : B.t),
    BC.mapIn b mb -> mapInB b (collectProtocols ma mb).

End S.
