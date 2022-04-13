Require Import trigo_3d other_structures.
Require Import quickhull_3d.

Require Extraction.
Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive nat => "Prelude.Int" [ "0" "Prelude.succ" ]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Constant float => "Prelude.Float".
Extract Constant mul => "(Prelude.*)".
Extract Constant sub => "(Prelude.-)".
Extract Constant div => "(Prelude./)".
Extract Constant add => "(Prelude.+)".
Extract Constant ltb => "(Prelude.<)".
Extract Constant opp => "\x -> -x".
Extract Constant abs => "abs".

Extraction "haskell/Extracted" get_initial_hull new_ordered_int_list list_length.