-- https://eng-cs.syr.edu/wp-content/uploads/2017/11/QE1_CISE_Jan17.pdf

data Rope = Empty | Str [Char] | Node Int Rope Rope deriving (Show)

r1 = Node 22 (Node 9 (Str "hello_") (Str "my_")) (Node 13 (Node 6 (Str "na") (Str "me")) (Node 7 (Str "s") (Str "_Simon")))
r2 = Node 11 (Node 9 (Str "hello_") (Str "my_")) (Str "ma")
r3 = Node 11 (Str "me_i") (Node 7 (Str "s") (Str "_Simon"))

concatRope :: Rope -> Rope -> Rope
concatRope (Node 0 (Str "")  Empty) r = r
concatRope r (Node 0 (Str "")  Empty) = r
concatRope rope1@(Node a r1 l1) rope2@(Node b r2 l2) = Node (a + b) rope1 rope2

lengthRope :: Rope -> Int
lengthRope Empty = 0
lengthRope (Str s) = length s
lengthRope (Node len l r) = len

indexRope :: Rope -> Int -> Char
indexRope Empty n = error "out of index"
indexRope (Str s) n = s !! n
indexRope (Node len cl cr) n
    | n < lengthRope cl = indexRope cl n
    | n >= lengthRope cl = indexRope cr (n - lengthRope cl)

-- more precise, should clean empty Node
splitRope :: Rope -> Int -> (Rope, Rope)
splitRope Empty n = error "can't split an empty"
splitRope (Str s) n =
    case splitAt n s of
        (s1, s2) -> (Node (length s1) (Str s1) Empty, Node (length s2) Empty (Str s2))
splitRope (Node len l r) n
    | n == lengthRope l = (l, r)
    | n < lengthRope l = 
        case splitRope l n of
            (newl1, newl2) -> (newl1, Node (lengthRope newl2 + lengthRope r) newl2 r)
    | n > lengthRope l =
        case splitRope r (n - lengthRope l) of
            (newr1, newr2) -> (Node (lengthRope l + lengthRope newr1) l newr1, newr2)

insertRope :: Rope -> [Char] -> Int -> Rope
insertRope r s i =
    case splitRope r i of
        (new1, new2) -> concatRope (concatRope new1 (Node (length s) (Str s) Empty)) new2

deleteRope :: Rope -> Int -> Int -> Rope
deleteRope r i j =
    case splitRope r i of
        (newl1, newl2) ->
            case splitRope r j of
                (newr1, newr2) -> concatRope newl1 newr2
