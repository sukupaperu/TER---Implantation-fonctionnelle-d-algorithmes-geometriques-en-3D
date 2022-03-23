module Main where

import Prelude
import Extracted
import VertexList

main :: IO ()
main =
    putStrLn (
        show (vec3_x
        (
            cross
            (last global_vertex_list)
            (head global_vertex_list)
        ))
    )