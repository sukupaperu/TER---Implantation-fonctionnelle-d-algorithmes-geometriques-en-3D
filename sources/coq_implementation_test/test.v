Require Import trigo_3d other_structures.
Require Import quickhull_3d.

Require Extraction.

Extraction Language Haskell.

(* \x y-> x < y *)
Extract Constant float => "Prelude.Float".
Extract Constant bool => "Prelude.Bool".

Extract Constant mul => "(Prelude.*)".
Extract Constant sub => "(Prelude.-)".
Extract Constant ltb => "\x y-> x Prelude.< y".

Extraction "haskell/Extracted" get_furthest_min_and_max.