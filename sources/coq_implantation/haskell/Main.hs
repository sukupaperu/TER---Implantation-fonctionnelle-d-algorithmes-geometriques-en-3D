module Main where

import Extracted

parseVertexEntry :: [String] -> Maybe Vec0
parseVertexEntry (x:y:z:_) = Just $ Vec3 (read x :: Prelude.Float) (read y :: Prelude.Float) (read z :: Prelude.Float)
parseVertexEntry _ = Nothing

haskelMaybeVecListToCoqVecList :: [Maybe Vec0] -> [] Vec0
haskelMaybeVecListToCoqVecList l = case l of {
    [] -> [];
    [Just a] -> [a];
    (Just a:b) -> a: haskelMaybeVecListToCoqVecList b;
    (Nothing:b) -> [];
}

printDcel :: Dcel0 -> IO ()
printDcel d = case d of {
        Dcel heList _ ->
            mapM_
            (\(He _ _ vertex_index) -> print vertex_index)
            heList
    }

main :: IO ()
main = do
    haskelMaybeVecList <- Prelude.map (parseVertexEntry . words) . lines <$> readFile "haskell/VertexList.txt"
    let globalVertexList = haskelMaybeVecListToCoqVecList haskelMaybeVecList
    case getInitialHull (getVec3InListFunctor globalVertexList) $ newOrderedIntList $ Prelude.length globalVertexList of {
        Prelude.Just dcel_result -> printDcel dcel_result;
        Prelude.Nothing -> print "Error :(";
    }
    -- print $ distFrom3dSegment (globalVertexList!!299) (globalVertexList!!298) (globalVertexList!!297) 
