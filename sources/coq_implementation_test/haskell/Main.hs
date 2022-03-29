module Main where

import Prelude
import Extracted
import VertexList ( globalVertexList )

testt :: List Vec0
testt = Cons (Vec3 0 0 0) (Cons (Vec3 0 0 0) Nil)

test3 :: List Vec0
test3 = map globalVertexList 

main :: IO ()
main =
    print 
    -- (
    --     get_furthest_min_and_max globalVertexList
    --     (new_ordered_int_list (list_length globalVertexList))
    -- )
        (vec3_x (
            Extracted.cross
            (last globalVertexList)
            (head globalVertexList)
        ))
