import           Data.List         as List
import           Data.Map.Internal as Map

-- Some test data:

--  A path -> edge-connectivity = 1, vertex-connectivity = 1
--  [(1,2),(2,3),(3,4)]
--
--  A cycle -> edge-connectivity = 2, vertex-connectivity = 2
--  [(1,2),(2,3),(3,4),(4,1)]
--
--  A complete graph K_4 -> edge-connectivity = 3, vertex-connectivity = 3
--  [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
--
--  Two complete graphs K_4 intersecting at a single vertex -> edge-connectivity = 3, vertex-connectivity = 1
--  [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
--
--  A disconnected graph -> edge-connectivity = 0, vertex-connectivity = 0
--  [(1,2),(3,4)]

-- Usage:
--  Functions vconn or econn followed by an input graph.
-- Note:
--  The input graph should be specified as a list of edges
--  The input graph is treated as undirected
-- Examples:
--  > vertexConnectivity [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
--  > edgeConnectivity [(1,2),(2,3),(3,4),(4,1)]

-- Queue data structure with (amortized) constant time push operation, using inbox and outbox method.
data Queue = Queue {
  inbox  :: [Int],
  outbox :: [Int]
} deriving Eq

-- Enqueue an element
push :: Int -> Queue -> Queue
push e (Queue inb out) = Queue (e:inb) out

-- Returns queue head and the rest of the queue
pop :: Queue -> (Int, Queue)
-- If outbox is empty, move everything from inbox to outbox
pop (Queue inb [])   = pop $ Queue [] (reverse inb)
pop (Queue inb outb) = (head outb, Queue inb (tail outb))

-- Returns True if e is already an element of the input queue
queued :: Int -> Queue -> Bool
queued e (Queue inb out)
    | elem e inb || elem e out = True
    | otherwise = False

-- Unweighted, simple, directed graph data structure
data Graph = Graph {
  children :: Map Int [Int],
  parents  :: Map Int [Int],
  edges    :: [(Int,Int)],
  vertices :: [Int]
} deriving Eq

-- Construct a bidirected graph from a list of undirected edges
fromEdges :: [(Int,Int)] -> Graph
fromEdges edges = Graph children parents allEdges vertices
 where
  -- Remove multi edges and loops
  parsedEdges = List.foldl (\acc (u,v) -> if u == v || elem (u,v) acc || elem (v,u) acc then acc else ((u,v):acc)) [] edges
  allEdges = parsedEdges ++ List.map (\(u,v) -> (v,u)) parsedEdges
  (children,parents) = List.foldl (\(map1,map2) (u,v) -> (addNeighbour u v map1, addNeighbour v u map2)) (Map.empty,Map.empty) allEdges
  vertices = Map.keys children



-- Computes the edge-connectivity of the input graph
-- By Menger's theorem, the size of the minimum edge/vertex cut for s and t is equal to the maximum number of
-- pairwise edge/vertex-independent paths from s to t. The edge/vertex-connectivity is the smallest size of these
-- minimum sized edge/vertex cuts among all pairs s and t.
-- The maximum number of pairwise edge-independent paths from s to t is calculated for each pair using
-- Goldberg's push-relabel algorithm by setting edge capacities to 1 on the input graph.
edgeConnectivity :: [(Int,Int)] -> Int
edgeConnectivity inputEdges = minimum [initGoldberg (Graph children Map.empty edges vertices) s t|(s,t)<-pairs vertices]
 where
 (Graph children parents edges vertices) = fromEdges inputEdges

-- Computes the vertex-connectivity of the input graph by splitting each vertex into two: a vertex v that inherits
-- the outgoing edges and a vertex (-v) with incoming edges. An edge (-v) -> v is also added. This is equivalent to
-- setting vertex capacities to 1 and as a result the algorithm now computes vertex independent paths in the original graph.
vertexConnectivity :: [(Int,Int)] -> Int
vertexConnectivity inputEdges = minimum [initGoldberg (Graph newAdjMap newInvMap newEdges newVertices) s (-t)|(s,t)<-pairs vertices]
 where
 (Graph children parents edges vertices) = fromEdges inputEdges
 newAdjMap = List.foldl (\acc v -> Map.insert (-v) [v] (Map.insert v (List.map (*(-1)) (acc!v)) acc)) children vertices
 newVertices = vertices ++ (List.map (*(-1)) vertices)
 newInvMap = List.foldl (\acc v -> Map.insert (-v) (List.map (*(-1)) (newAdjMap!v)) acc) Map.empty newVertices
 newEdges = List.map (\x -> (-x,x)) vertices ++ (List.map (\(u,v) -> (u,-v)) edges)

-- Performs initialization of the algorithm:
-- 1) A zero flow is constructed
-- 2) Source vertex is assigned height n (where n is the number of vertices)
-- 3) All out-edges from the source are saturated and their endpoints enqueued
-- The main part of the algorithm is then called
initGoldberg :: Graph -> Int -> Int -> Int
initGoldberg graph s t = goldberg children parents flow heights initQueue s t
 where
 (Graph children parents edges vertices) = graph
 zeroFlow = fromList [(e,0)|e<-edges]
 zeroHeights = fromList [(v,0)|v<-vertices]
 flow = List.foldl (\acc (s,v) -> Map.insert (s,v) 1 acc) zeroFlow [(s,v)|v<-(children!s)]
 heights = Map.insert s (length vertices) zeroHeights
 excludeST = List.delete t (List.delete s vertices)
 initQueue = Queue [] $ List.filter (\u -> (excess u children flow) > 0) excludeST

goldberg :: Map Int [Int] -> Map Int [Int] -> Map (Int,Int) Int -> Map Int Int -> Queue -> Int -> Int -> Int
-- Base case: The queue is empty, all internal vertices have excess = 0, flow conservation is satisfied
-- meaning the preflow is now a feasible flow. The target's inflow is returned
goldberg children parents flow heights (Queue [] []) s t = excess t children flow
goldberg children parents flow heights q s t =
 if (length pushableEdges) > 0
 then
 -- Perform push
  let
   v = head pushableEdges
   updatedFlow
        -- Push flow along forward edge
        | (if member (v,u) flow then flow!(v,u) else 0) == 1 = Map.insert (v,u) 0 flow
        -- Reverse flow along backward edge
        | otherwise = Map.insert (u,v) 1 flow
   updatedQueue
        | v /= s && v /= t && (excess v children updatedFlow) > 0 && not (queued v poppedQueue) &&
         (excess u children updatedFlow) > 0 && not (queued u poppedQueue) = push v (push u poppedQueue)
        | v /= s && v /= t && (excess v children updatedFlow) > 0 && not (queued v poppedQueue) = push v poppedQueue
        | (excess u children updatedFlow) > 0 && not (queued u poppedQueue) = push u poppedQueue
        | otherwise = poppedQueue
  in goldberg children parents updatedFlow heights updatedQueue s t
 -- Relabel
 else goldberg children parents flow (Map.insert u (1+(heights!u)) heights) q s t
 where
 (u,poppedQueue) = pop q
 -- Flow may be pushed along outgoing edges or flow may be pushed back into incoming edges
 -- A bit is used to determine the direction of the edge {u,v} so we know what kind of push to perform along the edge
 pushableEdges = List.filter (\v -> (residual (u,v) flow > 0) && (heights!u > heights!v)) $ (children!u) ++ (if member u parents then (parents!u) else [])

-- Add v to the neighbourhood of u in the adjacency map
addNeighbour :: Int -> Int -> Map Int [Int] -> Map Int [Int]
addNeighbour u v children | Map.member u children = Map.insert u (v:(children!u)) children
                        | otherwise = Map.insert u [v] children

-- Computes residual capacity along the edge (u,v)
residual :: (Int,Int) -> Map (Int,Int) Int -> Int
residual (u,v) flow = 1 - (if member (u,v) flow then flow!(u,v) else 0)
                        + (if member (v,u) flow then flow!(v,u) else 0)

-- Computes the excess flow in vertex u
excess :: Int -> Map Int [Int] -> Map (Int,Int) Int -> Int
excess u children flow = sum [if elem u (children!v) then flow!(v,u) else 0|v<-Map.keys children] - sum [flow!(u,v)|v<-(children!u)]

-- Returns all combinations of input list of size 2
pairs :: [Int] -> [(Int,Int)]
pairs []     = []
pairs (x:xs) = [(x,y)|y<-xs] ++ pairs xs