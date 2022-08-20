Require Coq.Structures.Equalities.
Require Coq.FSets.FSetAVL.
Require Coq.FSets.FSetWeakList.
Require Coq.FSets.FMapFacts.

Require Genevan.ProtoIdentifier.
Require Genevan.ProtoName.
Require Genevan.ProtoPeer.

Record t := {
  supports : ProtoIdentifier.t
}.

Module ClientHandlerPeer : ProtoPeer.T with Definition t := t.
  Definition t        := t.
  Definition eq       := @Logic.eq t.
  Definition eq_refl  := @Logic.eq_refl t.
  Definition eq_sym   := @Logic.eq_sym t.
  Definition eq_trans := @Logic.eq_trans t.

  #[local]
  Instance eq_equiv : RelationClasses.Equivalence eq := { }.

  Theorem eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros x y.
    destruct x as [xi].
    destruct y as [yi].
    destruct (ProtoIdentifier.Dec.eq_dec xi yi) as [HL|HR]. {
      left; rewrite HL; reflexivity.
    } {
      right.
      intro H_contra.
      assert (xi = yi) by congruence.
      contradiction.
    }
  Qed.

  Definition supports (c : t) : ProtoIdentifier.t := supports c.
End ClientHandlerPeer.

Module Sets : FSetInterface.WS 
  with Definition E.t  := t
  with Definition E.eq := ClientHandlerPeer.eq
:= FSetWeakList.Make ClientHandlerPeer.

Module ClientHandlerCollection :=
  ProtoPeer.Collection ClientHandlerPeer Sets.
