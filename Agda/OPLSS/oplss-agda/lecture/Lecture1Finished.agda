
open import Preliminaries

module lecture.Lecture1Finished where

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

      data HasBH : Tree → Nat → Set where
        HBH-Empty : HasBH Empty 1
        HBH-Node-Red  : (n : Nat) (l r : Tree) (kv : Key × Value) 
                      → HasBH l n 
                      → HasBH r n 
                      → HasBH (Node l Red kv r) n
        HBH-Node-Black  : (n : Nat) (l r : Tree) (kv : Key × Value) 
                      → HasBH l n 
                      → HasBH r n 
                      → HasBH (Node l Black kv r) (S n)

      module Example (k1 k2 : Key) (v1 v2 : Value) where
        t : Tree
        t = Node (Node Empty Red (k1 , v1) Empty) Black (k2 , v2) Empty

        t-bh : HasBH t 2
        t-bh = HBH-Node-Black 1 (Node Empty Red (k1 , v1) Empty) Empty (k2 , v2) 
                              (HBH-Node-Red 1 Empty Empty (k1 , v1) HBH-Empty HBH-Empty) HBH-Empty

        -- let unification fill things in
        t-bh' : HasBH t 2
        t-bh' = HBH-Node-Black _ _ _ _ (HBH-Node-Red _ _ _ _ HBH-Empty HBH-Empty) HBH-Empty

      -- Proof 1: case-analyze t, then c, then h
  
      blackenRoot-bh : (t : Tree) (n : Nat) → HasBH t n → Σ \ (m : Nat) → (HasBH (blackenRoot t) m)
      blackenRoot-bh Empty .1 HBH-Empty = 1 , HBH-Empty
      blackenRoot-bh (Node l Red kv r) n (HBH-Node-Red .n .l .r .kv hl hr) = S n , (HBH-Node-Black n l r kv hl hr) 
      blackenRoot-bh (Node l Black kv r) (S n) (HBH-Node-Black .n .l .r .kv hl hr) = S n , (HBH-Node-Black n l r kv hl hr)

      -- Proof 2: case-analyze h
  
      blackenRoot-bh2 : (t : Tree) (n : Nat) → HasBH t n 
                      → Σ \m → (HasBH (blackenRoot t) m)
      blackenRoot-bh2 .Empty .1 HBH-Empty = _ , HBH-Empty
      blackenRoot-bh2 .(Node l Red kv r) .n (HBH-Node-Red n l r kv hl hr) = _ , (HBH-Node-Black n l r kv hl hr)
      blackenRoot-bh2 .(Node l Black kv r) .(S n) (HBH-Node-Black n l r kv hl hr) = S n , HBH-Node-Black n l r kv hl hr


    -- implicit arguments

    module ImplicitArgs where

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

      balance-bh-red : {l : Tree} {kv : Key × Value} {r : Tree} {n : Nat} 
                  → HasBH l n → HasBH r n
                  → HasBH (balance l Red kv r) n
      balance-bh-red = {!!}

      balance-bh-black : {l : Tree} {kv : Key × Value} {r : Tree} {n : Nat} 
                  → HasBH l n → HasBH r n
                  → HasBH (balance l Black kv r) (S n)
      balance-bh-black = {!!}

      ins-bh : {t : Tree} (kv : Key × Value) {n : Nat} → HasBH t n → HasBH (ins t kv) n 
      ins-bh (k , v) HBH-Empty = HBH-Node-Red HBH-Empty HBH-Empty
      ins-bh (k , v) (HBH-Node-Red{n}{l}{r}{(k' , v')} hl hr) with compare k k'
      ins-bh (k , v) (HBH-Node-Red {n} {l} {r} {k' , v'} hl hr) | Less = balance-bh-red (ins-bh _ hl) hr
      ins-bh (k , v) (HBH-Node-Red {n} {l} {r} {k' , v'} hl hr) | Equal = HBH-Node-Red hl hr
      ins-bh (k , v) (HBH-Node-Red {n} {l} {r} {k' , v'} hl hr) | Greater = balance-bh-red hl (ins-bh _ hr)
      ins-bh (k , v) (HBH-Node-Black {n}{l}{r} {k' , v'} hl hr) with compare k k'
      ins-bh (k , v) (HBH-Node-Black {n} {l} {r} {k' , v'} hl hr) | Less = balance-bh-black (ins-bh _ hl) hr
      ins-bh (k , v) (HBH-Node-Black {n} {l} {r} {k' , v'} hl hr) | Equal = HBH-Node-Black hl hr
      ins-bh (k , v) (HBH-Node-Black {n} {l} {r} {k' , v'} hl hr) | Greater = balance-bh-black hl (ins-bh _ hr)

      insert-bh : {t : Tree} {kv : Key × Value} {n : Nat} → HasBH t n → Σ \ m → HasBH (insert t kv) m
      insert-bh h = blackenRoot-bh (ins-bh _ h)

