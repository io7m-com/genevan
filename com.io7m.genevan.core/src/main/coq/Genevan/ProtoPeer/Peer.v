Require Coq.Structures.Equalities.

Require Genevan.ProtoIdentifier.

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
