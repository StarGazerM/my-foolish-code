(* a ocaml version 
   Yihao Sun
   Syracuse
   2021 *)

type int_bst = 
  | BEmpty
  | BLeaf of int
  | BNode of int * int_bst * int_bst;;


let t1 = BNode (20, BNode (11, BLeaf 5, BLeaf 17), BNode (38, BLeaf 34, BLeaf 42));;


let rec post_order t =
  match t with
  | BEmpty -> []
  | BLeaf v -> [v]
  | BNode (v, left, right) -> (post_order left) @ (post_order right) @ [v]

let rec add_bst t insert_v =
  match t with
  | BEmpty -> BLeaf insert_v
  | BLeaf v -> 
    if insert_v > v 
    then BNode (v, (BLeaf insert_v), BEmpty) 
    else BNode (v, BEmpty, (BLeaf insert_v))
  | BNode (v, left, right) ->
    if insert_v > v
    then BNode (v, (add_bst left insert_v), right)
    else BNode (v, left, (add_bst right insert_v));;

let last lst = List.nth lst ((List.length lst) - 1);;

let rec rebuild lst =
    match lst with
    | [] ->  BEmpty
    | [x] -> BLeaf x
    | x :: xs ->
    let last_one = (last lst) in
    let left = rebuild (List.filter ((>) last_one) lst) in
    let right = rebuild (List.filter ((<) last_one) lst) in
    BNode (last_one, left, right);;

rebuild (post_order t1)
