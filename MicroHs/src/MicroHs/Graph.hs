{-# OPTIONS_GHC -Wno-unused-imports #-}
-----------------------------------------------------------------------------
-- Loosely based on:
--
-- Module      :  Data.Graph
-- Copyright   :  (c) The University of Glasgow 2002
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-----------------------------------------------------------------------------

module MicroHs.Graph (
  stronglyConnComp,
  SCC(..)
  ) where
import Data.List
import Data.Maybe
import MHSPrelude
import MicroHs.IntMap qualified as IM
import MicroHs.IntSet qualified as IS
import MicroHs.List
import Prelude qualified ()

data Tree a = Node a [Tree a]
  --deriving (Eq, Ord, Show)

type Forest a = [Tree a]

-- | Strongly connected component.
data SCC vertex = AcyclicSCC vertex     -- ^ A single vertex that is not
                                        -- in any cycle.
                | CyclicSCC  [vertex]   -- ^ A maximal set of mutually
                                        -- reachable vertices.
--  deriving (Show)

stronglyConnComp
        :: forall key node .
           Ord key
        => [(node, key, [key])]
                -- ^ The graph: a list of nodes uniquely identified by keys,
                -- with a list of keys of nodes this node has edges to.
                -- The out-list may contain keys that don't correspond to
                -- nodes of the graph; such edges are ignored.
        -> [SCC node]
stronglyConnComp edges0
  = map get_node (stronglyConnCompR (<=) edges0)
  where
    get_node (AcyclicSCC (n, _, _)) = AcyclicSCC n
    get_node (CyclicSCC triples)    = CyclicSCC [n | (n,_,_) <- triples]

stronglyConnCompR
        :: forall key node .
           (key -> key -> Bool)
        -> [(node, key, [key])]
                -- ^ The graph: a list of nodes uniquely identified by keys,
                -- with a list of keys of nodes this node has edges to.
                -- The out-list may contain keys that don't correspond to
                -- nodes of the graph; such edges are ignored.
        -> [SCC (node, key, [key])]     -- ^ Reverse topologically sorted
stronglyConnCompR _ [] = []
stronglyConnCompR le edges0
  = map decode forest
  where
    (graph, vertex_fn) = graphFromEdges le edges0
    forest             = scc graph
    mentions_itself v = v `elem` (graph IM.! v)
    decode (Node v []) | mentions_itself v = CyclicSCC [vertex_fn v]
                       | otherwise         = AcyclicSCC (vertex_fn v)
    decode other = CyclicSCC (dec other [])
                 where
                   dec (Node v ts) vs = vertex_fn v : foldr dec vs ts

type Vertex = Int
type Graph  = IM.IntMap [Vertex]
type Edge   = (Vertex, Vertex)

vertices :: Graph -> [Vertex]
vertices  = IM.keys

edges  :: Graph -> [Edge]
edges g = [ (v, w) | v <- vertices g, w <- g IM.! v ]

buildG :: [Vertex] -> [Edge] -> Graph
buildG vs es =
  let mt = IM.fromList (map (\ x -> (x, [])) vs)
  in  foldr (\ (v, w) -> IM.insertWith (++) v [w]) mt es

transposeG  :: Graph -> Graph
transposeG g = buildG (vertices g) (reverseE g)

reverseE  :: Graph -> [Edge]
reverseE g = [ (w, v) | (v, w) <- edges g ]

graphFromEdges
        :: forall key node .
           (key -> key -> Bool)
        -> [(node, key, [key])]
        -> (Graph, Vertex -> (node, key, [key]))
graphFromEdges le edges0
  = (graph, (vertex_map IM.!))
  where
    lek (_,k1,_) (_,k2,_) = le k1 k2

    max_v           = length edges0 - 1
    sorted_edges    = sortLE lek edges0
    edges1          = zip [0..] sorted_edges

    key_map         = IM.fromList [(v, k)                      | (v, (_,    k, _ )) <- edges1]

    -- key_vertex :: key -> Maybe Vertex
    --  returns Nothing for non-interesting vertices
    key_vertex k   = findVertex 0 max_v
                   where
                     findVertex a b | a > b
                              = Nothing
                     findVertex a b =
                         if k `le` m then
                           if m `le` k then
                             Just mid
                           else
                             findVertex a (mid - 1)
                         else
                           findVertex (mid + 1) b
                       where
                         mid = a + (b - a) `quot` 2
                         m = key_map IM.! mid

    graph           = IM.fromList [(v, mapMaybe key_vertex ks) | (v, (_,    _, ks)) <- edges1]
    vertex_map      = IM.fromList edges1

dff   :: Graph -> [Tree Vertex]
dff g = dfs g (vertices g)

dfs :: Graph -> [Vertex] -> Forest Vertex
dfs g vs0 = snd $ go IS.empty vs0
  where
    go :: IS.IntSet -> [Vertex] -> (IS.IntSet, Forest Vertex)
    go done [] = (done, [])
    go done (v:vs) =
      if IS.member v done
      then go done vs
      else
        let (done', as) = go (IS.insert v done) (g IM.! v)
            (done'', bs) = go done' vs
        in  (done'', Node v as : bs)


postorder :: forall a . Tree a -> [a] -> [a]
postorder (Node a ts) = postorderF ts . (a :)

postorderF :: forall a . [Tree a] -> [a] -> [a]
postorderF = foldr ((.) . postorder) id

postOrd :: Graph -> [Vertex]
postOrd g = postorderF (dff g) []

scc  :: Graph -> [Tree Vertex]
scc g = dfs g (reverse (postOrd (transposeG g)))
