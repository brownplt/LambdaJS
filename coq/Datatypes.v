Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Decidable.
Set Implicit Arguments.

Module Type STRING.

 Parameter string : Set.
 Declare Module String_as_OT : UsualOrderedType with Definition t := string.
 Declare Module Ordered : Coq.Structures.OrderedType.OrderedType
   with Definition t := string.
 Module OrderedTypeFacts := Coq.Structures.OrderedType.OrderedTypeFacts (Ordered).
 Parameter string_eq_dec : forall s1 s2 : string, {s1 = s2} + {~ s1 = s2}.
 Parameter string_dec_eq : forall s1 s2 : string, s1 = s2 \/ ~ s1 = s2.

End STRING.

Module Type ATOM.

  Parameter atom : Set.
  Declare Module Atom_as_OT : UsualOrderedType with Definition t := atom.
  Declare Module Ordered : Coq.Structures.OrderedType.OrderedType 
    with Definition t := atom.
  Module OrderedTypeFacts := Coq.Structures.OrderedType.OrderedTypeFacts (Ordered).
  Parameter atom_fresh_for_list : forall (xs : list atom), 
    exists x : atom, ~ List.In x xs.
  Parameter atom_eq_dec : forall a1 a2 : atom, {a1 = a2} + {~ a1 = a2}.
  Parameter atom_dec_eq : forall a1 a2 : atom, a1 = a2 \/ ~ a1 = a2.

End ATOM.
