
data BST = BEmpty | BLeaf Int | BNode Int BST BST deriving (Show)

t1 = BNode 20 (BNode 11 (BLeaf 5) (BLeaf 17)) (BNode 38 (BLeaf 34) (BLeaf 42))

postOrder BEmpty            = []
postOrder (BLeaf t)         = [t]
postOrder (BNode t bl br)   = postOrder bl ++ postOrder br ++ [t]

addBST i BEmpty = BLeaf i
addBST i (BLeaf n)
    | i <= n = BNode n (BLeaf i) BEmpty
    | otherwise =  BNode n BEmpty (BLeaf i)
addBST i (BNode n bl br)
    | i <= n    = BNode n (addBST i bl) br
    | otherwise = BNode n bl (addBST i br)

topV (BLeaf i) = i
topV (BNode i _ _) = i

checkBST BEmpty = True 
checkBST (BLeaf n) = True 
checkBST (BNode n BEmpty BEmpty) = True 
checkBST (BNode n bl BEmpty)
    | topV bl <= n = True 
    | otherwise = False 
checkBST (BNode n BEmpty br)
    | topV br >= n = True 
    | otherwise = False 
checkBST (BNode n bl br)
    | topV bl <= n && topV br >= n = True 
    | otherwise  = False 

rebuild [] = BEmpty
rebuild [x] = BLeaf x
rebuild xs = BNode lastOne (rebuild leftV) (rebuild rightV)
    where
        lastOne = last xs
        leftV = [x | x <- xs , x < lastOne]
        rightV = [x | x <- xs , x > lastOne]