module Extracted where

import qualified Prelude

data List a =
   Nil
 | Cons a (List a)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

add :: Prelude.Int -> Prelude.Int -> Prelude.Int
add n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> m)
    (\p -> Prelude.succ (add p m))
    n

eqb :: Prelude.Int -> Prelude.Int -> Prelude.Bool
eqb n m =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.True)
      (\_ -> Prelude.False)
      m)
    (\n' ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> Prelude.False)
      (\m' -> eqb n' m')
      m)
    n

hd :: a1 -> (List a1) -> a1
hd default0 l =
  case l of {
   Nil -> default0;
   Cons x _ -> x}

type Float = Prelude.Float

ltb :: Float -> Float -> Prelude.Bool
ltb = (Prelude.<)

data Vec0 =
   Vec3 Float Float Float

vec3_x :: Vec0 -> Float
vec3_x v0 =
  case v0 of {
   Vec3 x _ _ -> x}

new_ordered_int_list :: Prelude.Int -> List Prelude.Int
new_ordered_int_list n =
  (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
    (\_ -> Nil)
    (\n0 -> app (new_ordered_int_list n0) (Cons n0 Nil))
    n

list_length :: (List a1) -> Prelude.Int
list_length l =
  case l of {
   Nil -> 0;
   Cons _ m -> Prelude.succ (list_length m)}

value_in_list_by_index_rec :: (List a1) -> Prelude.Int -> a1 -> Prelude.Int
                              -> a1
value_in_list_by_index_rec l index default0 current_index =
  case l of {
   Nil -> default0;
   Cons el m ->
    case eqb index current_index of {
     Prelude.True -> el;
     Prelude.False ->
      value_in_list_by_index_rec m index default0 (Prelude.succ
        current_index)}}

value_in_list_by_index :: (List a1) -> Prelude.Int -> a1 -> a1
value_in_list_by_index l index default0 =
  value_in_list_by_index_rec l index default0 0

first_arg_if_true :: (a1 -> a1 -> Prelude.Bool) -> a1 -> a1 -> a1
first_arg_if_true f a b =
  case f a b of {
   Prelude.True -> a;
   Prelude.False -> b}

reduce_list :: (List a1) -> (a1 -> a2 -> a2) -> a2 -> a2
reduce_list l action_on_reduce default0 =
  case l of {
   Nil -> default0;
   Cons a b -> action_on_reduce a (reduce_list b action_on_reduce default0)}

v :: (List Vec0) -> Prelude.Int -> Vec0
v l index =
  value_in_list_by_index l index (Vec3
    (Prelude.error "EXTRACTION OF FLOAT NOT IMPLEMENTED")
    (Prelude.error "EXTRACTION OF FLOAT NOT IMPLEMENTED")
    (Prelude.error "EXTRACTION OF FLOAT NOT IMPLEMENTED"))

get_furthest_min_and_max :: (List Vec0) -> (List Prelude.Int) -> Prelude.Int
get_furthest_min_and_max gbl vertex_list =
  let {
   min_x = reduce_list vertex_list
             (first_arg_if_true (\a b ->
               ltb (vec3_x (v gbl a)) (vec3_x (v gbl b)))) (hd 0 vertex_list)}
  in
  let {
   max_x = reduce_list vertex_list
             (first_arg_if_true (\b a ->
               ltb (vec3_x (v gbl a)) (vec3_x (v gbl b)))) (hd 0 vertex_list)}
  in
  add max_x min_x

