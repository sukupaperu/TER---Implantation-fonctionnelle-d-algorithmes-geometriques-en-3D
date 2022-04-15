Require Import trigo_3d other_structures get_initial_hull.

Require Import ExtrHaskellBasic ExtrHaskellNatNum.

Require Extraction.
Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Inductive nat => "Prelude.Int" [ "0" "Prelude.succ" ]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Constant float => "Prelude.Float".
Extract Constant zero => "0.0".
Extract Constant one => "1.0".
Extract Constant mul => "(Prelude.*)".
Extract Constant sub => "(Prelude.-)".
Extract Constant div => "(Prelude./)".
Extract Constant add => "(Prelude.+)".
Extract Constant ltb => "(Prelude.<)".
Extract Constant opp => "\x -> -x".
Extract Constant abs1 => "Prelude.abs".

(* Optimisations *)
Extract Constant valueInListByIndex => "(\l x -> Prelude.Just Prelude.$ l Prelude.!! x)".
Extract Inlined Constant length => "Prelude.length".
Extract Inlined Constant filter => "Prelude.filter".
Extract Inlined Constant map => "Prelude.map".

Extraction "haskell/Extracted" getInitialHull newOrderedIntList getVec3InListFunctor.