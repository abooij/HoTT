Require Import
        HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.interfaces.rationals
        HoTT.Classes.interfaces.orders.

Section archimedean.

  Context (Q : Type) `{Rationals Q}.
  Context (A : Type) `{Lt A} `{Le A} `{Apart A} `{Zero A} `{One A}
          `{Plus A} `{Negate A} `{Mult A} `{Recip A} `{Join A} `{Meet A}.

  (* Eval compute in rationals_to_field Q A 0. *)
  Class ArchimedeanField  :=
    { archimedean_field :> OrderedField A
    ; archimedean_property :> forall x y, x < y -> hexists (fun q => x < (rationals_to_field Q A q) < y)
    }.

End archimedean.
