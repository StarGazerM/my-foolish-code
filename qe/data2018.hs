-- SU 2018 qe's data structure and programming part
-- Yihao Sun
-- 2021 Syracuse

data CTree = Empty | Node Char Int CTree CTree deriving (Show)

t1 = Node 'g' 3 (Node 'c' 1 (Node 'a' 0 Empty Empty) (Node 'e' 0 Empty Empty)) (Node 'j' 0 Empty Empty)
t2 = Node 't' 3 (Node 'r' 1 (Node 'q' 0 Empty Empty) (Node 's' 0 Empty Empty)) (Node 'w' 0 Empty Empty)
t0 = Node 'p' 5 t1 t2

add Empty newC = Node newC 0 Empty Empty
add (Node c i left right) newC
    | c == newC = error "new node must be different from existed"
    | newC < c  = Node c (i + 1) (add left newC) right 
    | newC > c  = Node c i left (add right newC)

index Empty c = error "not found"
index (Node c i Empty Empty) targetC
    | c == targetC = i
    | otherwise    = error "not found"
index (Node c i left right) targetC
    | c == targetC = i
    | c < targetC  = index right targetC + i + 1
    | c > targetC  = index left targetC

fetch t i
    | i < 0 = error "index must > 0"
fetch Empty 0 = error "can't fecth from a Empty Tree"
fetch (Node c i Empty Empty) targetI
    | i == targetI = c
    | otherwise    = error "index not found"
fetch (Node c i left right) targetI
    | targetI == i = c
    | targetI < i  = fetch left targetI
    | targetI > i  = fetch right (targetI - i - 1)

rightRotate Empty = Empty
rightRotate (Node c i Empty Empty) = Node c i Empty Empty
rightRotate (Node q qi (Node p pi at bt) ct) = Node p pi at (Node q qi bt ct)

leftRotate Empty = Empty
leftRotate (Node c i Empty Empty) = Node c i Empty Empty
leftRotate (Node p pi at (Node q qi bt ct)) = Node q qi (Node p pi at bt) ct

reroot Empty c = error "empty Node can't be rerooted"
reroot t@(Node c i Empty Empty) newRoot
    | c == newRoot = Node c i Empty Empty
    | otherwise    = error "new root is not in tree"
reroot t@(Node c i left right) newRoot
    | newRoot == c = Node c i left right
    | newRoot < c  = reroot (rightRotate t) newRoot
    | newRoot > c  = reroot (leftRotate t) newRoot