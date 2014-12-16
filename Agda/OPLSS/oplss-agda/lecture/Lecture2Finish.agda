open import Preliminaries

module lecture.Lecture2Finish where

  module Map where

    map : {A B : Set} → (f : A → B) → List A → List B
    map f [] = []
    map f (x :: xs) = f x :: map f xs

    module ExplicitArgs where
      data Length {A : Set} : List A → Nat → Set where
        L[] : Length [] 0
        L:: : (n : Nat) (x : A) (xs : List A) → Length xs n → Length (x :: xs) (S n)

      -- case l then n then len
      map-length-inversion : {A B : Set} (f : A → B) (xs : List A) (n : Nat)
                 → Length xs n
                 → Length (map f xs) n
      map-length-inversion f [] n h = {!!}
      map-length-inversion f (x :: l) (S n) (L:: .n .x .l h) = {!!}

      -- case len
      map-length-specialize2 : {A B : Set} (f : A → B) (xs : List A) (n : Nat)
                 → Length xs n
                 → Length (map f xs) n
      map-length-specialize2 f .[] .0 L[] = {!!}
      map-length-specialize2 f .(x :: xs) .(S n) (L:: n x xs h) = {!!}

      -- case l then len
      map-length-specialize : {A B : Set} (f : A → B) (xs : List A) (n : Nat)
                 → Length xs n
                 → Length (map f xs) n
      map-length-specialize f [] n h = {!!}
      map-length-specialize f (.x :: l) .(S n) (L:: n x .l h) = {!!}

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

    data ColorHeight : Color → Nat → Nat → Set where
      CH-Red   : {n : Nat} → ColorHeight Red n n
      CH-Black : {n : Nat} → ColorHeight Black n (S n)

    data HasBH : Tree -> Nat -> Set where
      HBH-Empty : HasBH Empty 1
      HBH-Node  : {n m : Nat} {c : Color} {l r : Tree} {kv : Key × Value}
                → HasBH l n 
                → ColorHeight c n m 
                → HasBH r n 
                → HasBH (Node l c kv r) m

    blackenRoot-bh : {t : Tree} {n : Nat} → HasBH t n → Σ (\(m : Nat) -> (HasBH (blackenRoot t) m))
    blackenRoot-bh HBH-Empty = _ , HBH-Empty
    blackenRoot-bh (HBH-Node hl ch hr) = _ , (HBH-Node hl CH-Black hr)

    balance-bh : {l : Tree} {c : Color} {kv : (Key × Value)} {r : Tree} {n m : Nat}
               → HasBH l n
               → ColorHeight c n m
               → HasBH r n
               → HasBH (balance l c kv r) m
    balance-bh {(Node (Node a Red x b) Red y c)} {Black} {z} {d} (HBH-Node (HBH-Node ha CH-Red hb) CH-Red hc) CH-Black hd = 
      HBH-Node (HBH-Node ha CH-Black hb) CH-Red (HBH-Node hc CH-Black hd)
    balance-bh {(Node a Red x (Node b Red y c))} {Black} {z} {d} hl ch hr = {!!} 
    balance-bh hl ch hr = {!!} 

    ins-bh : {t : Tree} {kv : Key × Value} {n : Nat} → HasBH t n → HasBH (ins t kv) n
    ins-bh HBH-Empty = HBH-Node HBH-Empty CH-Red HBH-Empty
    ins-bh {._} {k , v} (HBH-Node {n}{m}{c}{l}{r}{k' , v'} hl ch hr) with compare k k'
    ... | Less = balance-bh (ins-bh hl) ch hr 
    ... | Equal = HBH-Node hl ch hr
    ... | Greater = balance-bh hl ch (ins-bh hr)

    insert-bh : {n : Nat} {t : Tree} {kv : (Key × Value)} → HasBH t n → Σ (\(m : Nat) -> (HasBH (insert t kv) m))
    insert-bh h = blackenRoot-bh (ins-bh h)

  module RBTIntrinsic (Key : Set) (compare : Key -> Key -> Order) (Value : Set) where 

    data Color (n : Nat) : Nat → Set where
      Red : Color n n
      Black : Color n (S n)

    data Tree : Nat → Set where
      Empty : Tree 1
      Node : {n m : Nat} → Tree n -> (c : Color n m) → (Key × Value) -> Tree n -> Tree m 

    balance : {n m : Nat} → Tree n → (c : Color n m) (kv : (Key × Value)) → Tree n → Tree m
    balance (Node (Node a Red x b) Red y c) Black z d =  
            Node (Node a Black x b) Red y (Node c Black z d)
    balance (Node a Red x (Node b Red y c)) Black z d = 
            Node (Node a Black x b) Red y (Node c Black z d)
    balance a Black x (Node (Node b Red y c) Red z d) = 
            Node (Node a Black x b) Red y (Node c Black z d)
    balance a Black x (Node b Red y (Node c Red z d)) =
            Node (Node a Black x b) Red y (Node c Black z d)
    balance l c kv r = Node l c kv r

    ins : {n : Nat} → Tree n -> (Key × Value) -> Tree n
    ins Empty kv = Node Empty Red kv Empty
    ins (Node l c (k' , v') r) (k , v) with compare k k'
    ... | Equal = Node l c (k , v) r
    ... | Less = balance (ins l (k , v)) c (k' , v') r
    ... | Greater = balance l c (k' , v') (ins r (k , v))

    blacken-root : {n : Nat} -> Tree n → Σ \ m → Tree m
    blacken-root Empty = _ , Empty
    blacken-root (Node l _ kv r) = _ , Node l Black kv r

    insert : {n : Nat} → Tree n -> Key × Value -> Σ \ m → Tree m
    insert t kv = blacken-root (ins t kv)

  -- see IntrinsicWellRed.agda