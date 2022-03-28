module Main where

import Prelude
import Extracted
import VertexList ( globalVertexList )

main :: IO ()
main =
    print 
        (vec3_x (
            cross
            (last globalVertexList)
            (head globalVertexList)
        ))
