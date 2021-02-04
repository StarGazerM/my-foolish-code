-- https://eng-cs.syr.edu/wp-content/uploads/2019/06/CISE-QE-1-Exam-Jan-7-2019.pdf

data NodeColor = Grey | Black deriving (Show)

-- char of a node is the char on income edge
-- char in root is '\0' will never be used to compare
data CTrie = Node NodeColor Char [CTrie] deriving (Show) 

t1 = Node Grey '\0' [
    Node Black 'a' [
        Node Black 't' [
            Node Black 'e' []]],
    Node Grey 'o' [
        Node Black 'n' [Node Black 'e' []], 
        Node Grey 'u' [Node Black 't' []]],
    Node Grey 'm' [
        Node Black 'e' [],
        Node Grey 'u' [Node Black 'd' []],
        Node Black 'y'[]]
    ]

search :: [Char] -> CTrie -> Bool
search "" (Node Grey _ [])  = True 
search str (Node Grey _ []) = False 
search [m] (Node Black c childs)
    | c == m    = True
    | otherwise = False
search (m:ms) (Node Black c childs)
    | c == m    = any (search ms) childs
    | otherwise = False
search str (Node Grey '\0' childs) = any (search str) childs
search [m] (Node Grey c childs) = False
search (m:ms) (Node Grey c childs)
    | c == m    = any (search ms) childs
    | otherwise = False 

findChildByChar tc [] = Nothing 
findChildByChar tc (headC@(Node color c cs):restC)
    | c == tc = Just headC
    | otherwise = findChildByChar c restC

-- can't add empty str to child
addToChildren [m] [] = [Node Black m []]
addToChildren (m:ms) [] = [Node Grey m (addToChildren ms [])]
addToChildren str@(m:ms) (ht@(Node color c children):cs)
    | m == c    =
        case ms of
            []      -> Node Black c children : cs
            (_:_)   -> Node color c (addToChildren ms children) : cs
    | otherwise = ht : addToChildren str cs

add "" t = t
add str (Node Grey '\0' children) = Node Grey '\0' (addToChildren str children)

count (Node Black c children) = 1 + sum (map count children)
count (Node Grey c children) = sum (map count children)

allString :: CTrie -> [[Char]]
allString (Node Grey '\0' children) = concatMap allString children
allString (Node Grey c children)    = map (c:) (concatMap allString children)
allString (Node Black c children)   = [c] : map (c:) (concatMap allString children)
