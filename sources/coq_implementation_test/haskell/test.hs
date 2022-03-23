module Test where

import qualified Prelude

type Float = Prelude.Float

mul :: Float -> Float -> Float
mul = \x y-> x*y

sub :: Float -> Float -> Float
sub =
  Prelude.error "AXIOM TO BE REALIZED"

data Vec0 =
   Vec3 Float Float Float

cross :: Vec0 -> Vec0 -> Vec0
cross u v =
  case u of {
   Vec3 x1 y1 z1 ->
    case v of {
     Vec3 x2 y2 z2 -> Vec3 (sub (mul y1 z2) (mul z1 y2))
      (sub (mul z1 x2) (mul x1 z2)) (sub (mul x1 y2) (mul y1 x2))}}

