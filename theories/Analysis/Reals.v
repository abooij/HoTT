Require Import
        HoTT.Basics
        HoTT.Types.Universe
        HoTT.Types.Sum
        HoTT.Spaces.Finite.

Require Import
        HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.implementations.assume_rationals
        HoTT.Classes.implementations.dedekind_reals.

Definition R := RD Q.
Global Instance R_inc_Q : Cast Q R := inc Q.
