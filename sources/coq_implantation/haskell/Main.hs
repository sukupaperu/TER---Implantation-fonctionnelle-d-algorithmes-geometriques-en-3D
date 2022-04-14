module Main where

import Extracted

parseVertexEntry :: [String] -> Maybe Vec0
parseVertexEntry (x:y:z:_) = Just $ Vec3 (read x :: Prelude.Float) (read y :: Prelude.Float) (read z :: Prelude.Float)
parseVertexEntry _ = Nothing

haskelMaybeVecListToCoqVecList :: [Maybe Vec0] -> List Vec0
haskelMaybeVecListToCoqVecList l = case l of {
    [] -> Nil;
    [Just a] -> Cons a Nil;
    (Just a:b) -> Cons a (haskelMaybeVecListToCoqVecList b);
    (Nothing:b) -> Nil;
}

-- printVec3 v = case v of {
--     Vec3 x y z -> print [x,y,z]
-- }
-- printCoqVecList l = case l of {
--     Nil -> putStr "";
--     Cons a b -> do
--         printVec3 a;
--         printCoqVecList b;
-- }

main = do
    haskelMaybeVecList <- map (parseVertexEntry . words) . lines <$> readFile "haskell/VertexList.txt"
    let globalVertexList = haskelMaybeVecListToCoqVecList haskelMaybeVecList
    -- printCoqVecList globalVertexList
    print $ getInitialHull globalVertexList $ newOrderedIntList $ listLength globalVertexList
