Require Coq.FSets.FMaps.
Require Coq.FSets.FSetInterface.
Require Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.

Require Coq.Strings.String.
Require Coq.Structures.OrderedTypeEx.

(** * Protocol Name *)

(** A protocol name is an arbitrary string. *)

Definition t := String.string.

(** Protocol names are lexicographically ordered. *)

Module Ord : OrderedTypeEx.UsualOrderedType
  with Definition t  := String.string
  with Definition eq := @Logic.eq t.
  Include OrderedTypeEx.String_as_OT.
End Ord.

Module Maps : FMapInterface.S 
  with Definition E.t  := String.string
  with Definition E.eq := Ord.eq
:= FMapAVL.Make Ord.

Module MapsFacts :=
  FMapFacts.WFacts Maps.
