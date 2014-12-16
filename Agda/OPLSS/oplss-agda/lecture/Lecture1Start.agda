
open import Preliminaries 

module lecture.Lecture1Start where

  module RBT (Key : Set) (compare : Key → Key → Order) (Value : Set) where 

    data Color : Set where
      Red : Color
      Black : Color
  
    data Tree : Set where
      Empty : Tree
      Node : Tree → Color → (Key × Value) → Tree → Tree

    balance : Tree → Color → (Key × Value) → Tree → Tree
    balance (Node (Node a Red x b) Red y c) Black z d =  
            Node (Node a Black x b) Red y (Node c Black z d)
    balance (Node a Red x (Node b Red y c)) Black z d = 
            Node (Node a Black x b) Red y (Node c Black z d)
    balance a Black x (Node (Node b Red y c) Red z d) = 
            Node (Node a Black x b) Red y (Node c Black z d)
    balance a Black x (Node b Red y (Node c Red z d)) =
            Node (Node a Black x b) Red y (Node c Black z d)
    balance l c kv r = Node l c kv r

    ins : Tree → (Key × Value) → Tree
    ins Empty kv = Node Empty Red kv Empty
    ins (Node l c (k' , v') r) (k , v) with compare k k'
    ... | Equal = Node l c (k , v) r
    ... | Less = balance (ins l (k , v)) c (k' , v') r
    ... | Greater = balance l c (k' , v') (ins r (k , v))

    blackenRoot : Tree → Tree
    blackenRoot Empty = Empty
    blackenRoot (Node l _ kv r) = Node l Black kv r

    insert : Tree → Key × Value → Tree
    insert t kv = blackenRoot (ins t kv)

    module ExplicitArgs where

      module Example (k1 k2 : Key) (v1 v2 : Value) where
        t : Tree
        t = Node (Node Empty Red (k1 , v1) Empty) Black (k2 , v2) Empty


    module ImplicitArgs where

