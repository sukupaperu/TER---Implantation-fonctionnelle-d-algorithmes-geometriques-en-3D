Require Import trigo_3d other_structures.
Require Import quickhull_3d.

Require Extraction.

Extraction Language Haskell.

(* \x y-> x < y *)
Extract Constant float => "Prelude.Float".
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
(*Extract Inductive nat => int [ "0" "Pervasives.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".*)
Extract Inductive nat => "Prelude.Int" [ "0" "Prelude.succ" ]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".


Extract Constant mul => "(Prelude.*)".
Extract Constant sub => "(Prelude.-)".
Extract Constant ltb => "(Prelude.<)".

Extraction "haskell/Extracted" get_furthest_min_and_max new_ordered_int_list list_length cross.