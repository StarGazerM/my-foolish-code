-- https://eng-cs.syr.edu/wp-content/uploads/2017/11/QE1_CISE_Jan16.pdf

data MultiTree = Leaf Char | Branch Char [MultiTree] deriving (Show)

t0 = Branch 'y' [
    Branch 's' [Leaf 'z', Leaf 'x'],
    Branch 'f' [Leaf 'c'],
    Leaf 'h',
    Branch 'k' [Leaf 'b', Leaf 'n', Leaf 'm']]

traversal :: MultiTree -> [Char]
traversal (Leaf c) = [c]
traversal (Branch c bs) = concatMap traversal bs ++ [c] 

stringAtLevel :: (Eq a, Num a) => a -> MultiTree  -> [Char]
stringAtLevel 0 (Leaf c) = [c]
stringAtLevel n (Leaf c) = ""
stringAtLevel 0 (Branch c bs) = [c]
stringAtLevel n (Branch c bs) = concatMap (stringAtLevel (n - 1)) bs

data BinTree = BEmpty | BLeaf Char | BNode Char BinTree BinTree deriving (Show)

-- create a symetrical binary tree with given node number and label name


-- multiToBin (Leaf c) = BLeaf c
-- multiToBin (Branch c bs) = mlistToBinSym c bs
--     where
--         mlistToBinSym c [] = BEmpty
--         mlistToBinSym c [m] = multiToBin m
--         mlistToBinSym c ms = BNode c (mlistToBinSym c lms) (mlistToBinSym c rms)
--             where (lms, rms) = splitAt (length ms `div` 2) ms

-- binToMulti (BLeaf b) = Leaf b
-- binToMulti (BNode c bleft bright) = Branch c (binToMlist c bleft ++ binToMlist c bright)
--     where
--         binToMlist pc BEmpty           = []
--         binToMlist pc (BLeaf b)        = [Leaf b] 
--         binToMlist pc bt@(BNode c bl br)
--             | c == pc   = binToMlist pc bl ++ binToMlist pc br
--             | otherwise = [binToMulti bt]