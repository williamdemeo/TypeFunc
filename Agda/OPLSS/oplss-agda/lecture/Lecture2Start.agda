open import Preliminaries

module lecture.Lecture2Start where

  module Map where

    map : {A B : Set} → (f : A → B) → List A → List B
    map f [] = []
    map f (x :: xs) = f x :: map f xs

    module ExplicitArgs where
      data Length {A : Set} : List A → Nat → Set where
        L[] : Length [] 0
        L:: : (n : Nat) (x : A) (xs : List A) → Length xs n → Length (x :: xs) (S n)

      map-length : {A B : Set} (f : A → B) (xs : List A) (n : Nat)
                 → Length xs n
                 → Length (map f xs) n
      map-length f xs n h = {!!}

    module ImplicitArgs where
    
      data Length {A : Set} : List A → Nat → Set where
        L[] : Length [] 0
        L:: : {n : Nat} {x : A} {xs : List A} → Length xs n → Length (x :: xs) (S n)

      map-length : {A B : Set} {f : A → B} {xs : List A} {n : Nat} 
                 → Length xs n
                 → Length (map f xs) n
      map-length L[] = L[]
      map-length (L:: lxs) = L:: (map-length lxs)


  module RBT (Key : Set) (compare : Key -> Key -> Order) (Value : Set) where 

    data Color : Set where
      Red : Color
      Black : Color
  
    data Tree : Set where
      Empty : Tree
      Node : Tree -> Color → (Key × Value) -> Tree -> Tree

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

    ins : Tree -> (Key × Value) -> Tree
    ins Empty kv = Node Empty Red kv Empty
    ins (Node l c (k' , v') r) (k , v) with compare k k'
    ... | Equal = Node l c (k , v) r
    ... | Less = balance (ins l (k , v)) c (k' , v') r
    ... | Greater = balance l c (k' , v') (ins r (k , v))

    blackenRoot : Tree -> Tree
    blackenRoot Empty = Empty
    blackenRoot (Node l _ kv r) = Node l Black kv r

    insert : Tree -> Key × Value -> Tree
    insert t kv = blackenRoot (ins t kv)

    data HasBH : Tree → Nat → Set where
      HBH-Empty : HasBH Empty 1
      HBH-Node-Red  : {n : Nat} {l r : Tree} {kv : Key × Value}
                    → HasBH l n 
                    → HasBH r n 
                    → HasBH (Node l Red kv r) n
      HBH-Node-Black  : {n : Nat} {l r : Tree} {kv : Key × Value}
                    → HasBH l n 
                    → HasBH r n 
                    → HasBH (Node l Black kv r) (S n)

    blackenRoot-bh : {t : Tree} {n : Nat} → HasBH t n → Σ \m → (HasBH (blackenRoot t) m)
    blackenRoot-bh HBH-Empty = _ , HBH-Empty
    blackenRoot-bh (HBH-Node-Red hl hr) = _ , (HBH-Node-Black hl hr)
    blackenRoot-bh (HBH-Node-Black hl hr) = _ , HBH-Node-Black hl hr


  module RBTIntrinsic (Key : Set) (compare : Key → Key → Order) (Value : Set) where 

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


