open import Preliminaries

module handson.Lab2Sol where

  module Intrinsic where

    {- Recall the following code from Lab 1 -}
    module Extrinsic where
      map : {A B : Set} → (f : A → B) → List A → List B
      map f [] = []
      map f (x :: xs) = f x :: map f xs
  
      data Length {A : Set} : List A → Nat → Set where
        L[] : Length [] 0
        L:: : {n : Nat} {x : A} {xs : List A} → Length xs n → Length (x :: xs) (S n)
  
      map-length : {A B : Set} {f : A → B} {xs : List A} {n : Nat} 
                 → Length xs n
                 → Length (map f xs) n
      map-length L[] = L[]
      map-length (L:: lxs) = L:: (map-length lxs)


    {- TASK 1
       Using an inductive family, define a version of lists 
       that will allow you to verify the length invariant intrinsically
    -}
    data Vec (A : Set) : Nat → Set where
      [] : Vec A 0
      _::_ : {n : Nat} → A → Vec A n → Vec A (S n)


    {- TASK 2 
       Give a precise type to map, expressing that it preserves the length of the list.  
       The clauses should be exactly the same as above:

       map f [] = []
       map f (x :: xs) = f x :: map f xs

    -}
    map : {n : Nat} {A B : Set} → (f : A → B) → Vec A n → Vec B n
    map f [] = []
    map f (x :: xs) = f x :: map f xs


    {- TASK 3
       Using Fin n, define an nth function for your datatype.
       The result type should be "A", not "Maybe A".  
       This should look a lot like nth' from last time.
    -}
    
    data Fin : Nat → Set where
      FZ : {n : Nat} → Fin (S n)
      FS : {n : Nat} → Fin n → Fin (S n)

    -- case-analyze Fin n first
    nth : {A : Set} {n : Nat} → Fin n → Vec A n → A
    nth FZ (x :: v) = x
    nth (FS n₁) (x :: v) = nth n₁ v

    -- if you case-analyze the vec first, there's an extra (contradictory) case
    nth2 : {A : Set} {n : Nat} → Fin n → Vec A n → A
    nth2 () []
    nth2 FZ (x :: v) = x
    nth2 (FS n₁) (x :: v) = nth n₁ v


    {- TASK 4 
       This task shows an example of doing extrinsic verification
       about intrinsically verified code: 
       Map fusion is a program optimization that fuses two 
       passes over a vector (map f, and then map g) into one
       (map (g o f)).  Prove that map fusion is correct,
       in the sense that it the optimized and unoptimized code
       has the same behavior.
       
       Hint: use 'ap', the congruence principle for propositional equality:
         ap :  {A : Set} {B : Set} {M N : A} (f : A → B) 
            → M == N → (f M) == (f N)

       Hint 2: there is another solution that uses "2-column-with",
       where you 'with' on two things at once:
       The general syntax for this is
         f p with e1 | e2
         ...    | p1 | p2 = ... 
    -}

    map-fusion' : {A B C : Set} {n : Nat} (g : B → C) (f : A → B) (v : Vec A n) → map g (map f v) == map (g o f) v
    map-fusion' g f [] = Refl
    map-fusion' g f (x :: v) = ap (λ z → g (f x) :: z) (map-fusion' g f v)

    map-fusion : {A B C : Set} {n : Nat} (g : B → C) (f : A → B) (v : Vec A n) → map g (map f v) == map (g o f) v
    map-fusion g f [] = Refl
    map-fusion g f (x :: v) with map (g o f) v | map-fusion g f v
    map-fusion g f (x :: v) | .(map g (map f v)) | Refl = Refl


  {- Next, we'll look at the proof that RBT insert produces a sorted tree. -}

  open FancyOrder
  module IntrinsicSorted (Keys : DecidableOrder) (Value : Set) where 

    open DecidableOrder Keys renaming (A to Key)
    {-
        see Preliminaries.agda, especially the module FancyOrder
        You may want to use the following: 

        ordering on keys, and some operations and lemmas: 
        _≤_     : Key → Key → Set
        ≤-refl  : ∀ {k} → a ≤ a
        ≤-trans : ∀ {k1 k2 k3} → k1 ≤ k2 → k2 ≤ k3 → k1 ≤ k3
        ≤-saturated : ∀ {k1 k2} → k1 ≤ k2 → k2 ≤ k1 → k1 == k2
        compare : (k1 k2 : Key) → FancyOrder k1 k2  where 
              data FancyOrder (a1 a2 : A) : Set where
                Less    : a1 ≤ a2 → (a1 == a2 → Void) → FancyOrder a1 a2
                Equal   : a1 == a2 → FancyOrder a1 a2
                Greater : a2 ≤ a1 → (a1 == a2 → Void) → FancyOrder a1 a2
        ≤-refl' : {k1 k2 : Key} → k1 == k2 → k1 ≤ k2
        min : Key → Key → Key
        min-≤-1 : {k1 k2 : Key} → min k1 k2 ≤ k1
        min-≤-2 : {k1 k2 : Key} → min k1 k2 ≤ k2
        min-sym : {k1 k2 : Key} → min k1 k2 == min k2 k1
        min-≤ : {k1 k2 : Key} → k1 ≤ k2 → (min k1 k2) == k1
        max : Key → Key → Key
        max-≥-1 : {k1 k2 : Key} → k1 ≤ max k1 k2 
        max-≥-2 : {k1 k2 : Key} → k2 ≤ max k1 k2
        max-sym : {k1 k2 : Key} → max k1 k2 == max k2 k1
        max-≤ : {k1 k2 : Key} → k1 ≤ k2 → (max k1 k2) == k2

        symmetry and transitivity of equality:
        ! : {A : Set} {M N : A} → M == N → N == M 
        _∘_  : {A : Set} {M N P : A} → N == P → M == N → M == P
    -}

    data Color : Set where
      Red : Color
      Black : Color

    {- We'll use the following definition of sorted trees,
       where Tree L H is a sorted tree such that L ≤ everything in t ≤ H
    -} 
    data Tree : Key → Key → Set where
      Empty : {L H : Key} -> L ≤ H → Tree L H
      Node : {L H : Key} → (c : Color) (M : Key) (v : Value) (l : Tree L M) (r : Tree M H) -> Tree L H

    {- TASK 6 
       As a sanity-check, prove that Tree L H implies L ≤ H.
       NOTE: You will NOT need to use this function in the remaining code.
    -}
    sanity : {L H : Key} → Tree L H -> L ≤ H
    sanity (Empty L≤H) = L≤H
    sanity (Node c M v l r) = ≤-trans (sanity l) (sanity r)
    

    {- TASK 7
       Show that you can "weaken" the bounds on a tree to something less precise.

       Assuming that the operations on ≤ are constant time,
       (weaken-left _ t) and (weaken-right _ t) should
       each take time proportional to the depth of t.  
    -}
    weaken-left : ∀ {L L' H} → L' ≤ L → Tree L H → Tree L' H
    weaken-left L'≤L (Empty L≤H) = Empty (≤-trans L'≤L L≤H)
    weaken-left L'≤L (Node c M v l r) = Node c M v (weaken-left L'≤L l) r

    weaken-right : ∀ {L H H'} → H ≤ H' → Tree L H → Tree L H'
    weaken-right H≤H' (Empty L≤H) = Empty (≤-trans L≤H H≤H')
    weaken-right H≤H' (Node c M v l r) = Node c M v l (weaken-right H≤H' r)

    {- TASK 8 
       Define insert.  You will need to give appropriate types for,
       and implement balance and ins and blackenRoot.  Try to keep 
       the structure of the code as close to the simply-typed
       version as possible.  

       It's OK if the asymptotic complexity of insert is O(depth-of-t^2)
       rather than O(depth-of-t), due to the calls to weaken.
    -}

    balance : ∀ {L H} → (co : Color) (M : Key) (v : Value) → Tree L M → Tree M H → Tree L H
    balance Black z vz (Node Red y vy (Node Red x vx a b) c) d
      = Node Red y vy (Node Black x vx a b) (Node Black z vz c d)
    balance Black z vz (Node Red x vx a (Node Red y vy b c)) d
      = Node Red y vy (Node Black x vx a b) (Node Black z vz c d)
    balance Black x vx a (Node Red z vz (Node Red y vy b c) d)
      = Node Red y vy (Node Black x vx a b) (Node Black z vz c d)
    balance Black x vx a (Node Red y vy b (Node Red z vz c d))
      = Node Red y vy (Node Black x vx a b) (Node Black z vz c d)
    balance c k v l r = Node c k v l r

    ins : ∀ {L H} → Tree L H -> (k : Key) → Value -> Tree (min L k) (max H k)
    ins (Empty L≤H) k v = Node Red k v (Empty min-≤-2) (Empty max-≥-2)
    ins (Node c k' v' l r) k v with compare k k'
    ... | Equal eq = weaken-left min-≤-1 (weaken-right max-≥-1 (Node c k' v l r))
    ... | Less lt _ = balance c k' v' (weaken-right (≤-refl' (max-≤ lt ∘ max-sym)) (ins l k v)) (weaken-right max-≥-1 r)
    ... | Greater gt _ = balance c k' v' (weaken-left min-≤-1 l) (weaken-left (≤-refl' (! (min-≤ gt))) (ins r k v))

    blackenRoot : ∀ {L H} → Tree L H -> Tree L H
    blackenRoot (Empty L≤H) = Empty L≤H
    blackenRoot (Node c k v l r) = Node Black k v l r

    insert : ∀ {L H} → Tree L H → (k : Key) (v : Value) → Tree (min L k) (max H k)
    insert t k v = blackenRoot (ins t k v)

  {- TASK 9
     Give an alternate definition of Sorted which supports a constant-time 'weaken' function,
     and redo the above code for that definition.  
  -}
  module IntrinsicSortedGoodAsymptotics (Keys : DecidableOrder) (Value : Set) where 

    open DecidableOrder Keys renaming (A to Key)

    data Color : Set where
      Red : Color
      Black : Color
  
    mutual
      data Tree (L H : Key) : Set where
        Empty : L ≤ H → Tree L H
        Node : (c : Color) (k : Key) (v : Value) 
             → WrappedTree L k
             → WrappedTree k H -> Tree L H

      data WrappedTree (L H : Key) : Set where
        Wrap : {L' H' : Key} → (L ≤ L') → Tree L' H' → H' ≤ H → WrappedTree L H


    trivialWrapper : {L H : Key} → Tree L H → WrappedTree L H
    trivialWrapper t = Wrap ≤-refl t ≤-refl

    weaken : {L L' H H' : Key} → L' ≤ L → H ≤ H' → WrappedTree L H → WrappedTree L' H'
    weaken low high (Wrap low' t high') = Wrap (≤-trans low low') t (≤-trans high' high)

    balance : ∀ {L H} → (co : Color) (M : Key) (v : Value) → WrappedTree L M → WrappedTree M H → Tree L H
    balance Black z vz (Wrap lb1 (Node Red y vy (Wrap lb2 (Node Red x vx a b) ub2) c) ub1) d
      = Node Red y vy (Wrap (≤-trans lb1 lb2) (Node Black x vx a b) ub2) (Wrap ≤-refl (Node Black z vz (weaken ≤-refl ub1 c) d) ≤-refl)
    balance Black z vz (Wrap lb1 (Node Red x vx a (Wrap lb2 (Node Red y vy b c) ub2)) ub1) d
      = Node Red y vy (Wrap lb1 (Node Black x vx a (weaken lb2 ≤-refl b)) ≤-refl) (Wrap ≤-refl (Node Black z vz (weaken ≤-refl (≤-trans ub2 ub1) c) d) ≤-refl)
    balance Black x vx a (Wrap lb1 (Node Red z vz (Wrap lb2 (Node Red y vy b c) ub2) d) ub1)
      = Node Red y vy (Wrap ≤-refl (Node Black x vx a (weaken (≤-trans lb1 lb2) ≤-refl b)) ≤-refl) (Wrap ≤-refl (Node Black z vz (weaken ≤-refl ub2 c) d) ub1)
    balance Black x vx a (Wrap lb1 (Node Red y vy b (Wrap lb2 (Node Red z vz c d) ub2)) ub1)
      = Node Red y vy (Wrap ≤-refl (Node Black x vx a (weaken lb1 ≤-refl b)) ≤-refl) (Wrap lb2 (Node Black z vz c d) (≤-trans ub2 ub1)) 
    balance c k v l r = Node c k v l r

    mutual
      ins : ∀ {L H} → Tree L H -> (k : Key) → Value -> Tree (min L k) (max H k)
      ins (Empty L≤H) k v = Node Red k v (trivialWrapper (Empty min-≤-2)) (trivialWrapper (Empty max-≥-2))
      ins (Node c k' v' l r) k v with compare k k'
      ... | Equal eq = Node c k' v (weaken min-≤-1 ≤-refl l) (weaken ≤-refl max-≥-1 r)
      ... | Less lt _ = balance c k' v' (weaken ≤-refl (≤-refl' (max-≤ lt ∘ max-sym)) (ins-wrap l k v)) (weaken ≤-refl max-≥-1 r)
      ... | Greater gt _ = balance c k' v' (weaken min-≤-1 ≤-refl l) (weaken (≤-refl' (! (min-≤ gt))) ≤-refl (ins-wrap r k v))

      ins-wrap : ∀ {L H} → WrappedTree L H -> (k : Key) → Value -> WrappedTree (min L k) (max H k)
      ins-wrap (Wrap bl t bh) k v = Wrap (min-monotone bl ≤-refl) (ins t k v) (max-monotone bh ≤-refl)

    blacken-root : ∀ {L H} → Tree L H -> Tree L H
    blacken-root (Empty L≤H) = Empty L≤H
    blacken-root (Node c k v l r) = Node Black k v l r

    insert : ∀ {L H} → Tree L H → (k : Key) (v : Value) → Tree (min L k) (max H k)
    insert t k v = blacken-root (ins t k v)
