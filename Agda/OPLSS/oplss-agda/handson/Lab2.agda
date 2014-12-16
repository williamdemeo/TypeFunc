open import Preliminaries

module handson.Lab2 where

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


    {- TASK 2 
       Give a precise type to map, expressing that it preserves the length of the list.  
       The clauses for map should be exactly the same.  
    -}
    map : {!!}
    map = {!!}
    {-
    map f [] = []
    map f (x :: xs) = f x :: map f xs
    -}

    {- TASK 3
       Using Fin n, define an nth function for your datatype.
       The result type should be "A", not "Maybe A".  
       This should look a lot like nth' from last time.
    -}
    
    data Fin : Nat → Set where
      FZ : {n : Nat} → Fin (S n)
      FS : {n : Nat} → Fin n → Fin (S n)

    nth : {!!}
    nth = {!!}

    {- TASK 4 
       This task shows an example of doing extrinsic verification
       about intrinsically verified code.

       Map fusion is a program optimization that fuses two 
       passes (map f, and then map g) into one
       (map (g o f)).  Prove that map fusion is correct,
       in the sense that the optimized and unoptimized code
       have the same behavior.
       
       Hint: use 'ap', the congruence principle for propositional equality:
         ap :  {A : Set} {B : Set} {M N : A} (f : A → B) 
            → M == N → (f M) == (f N)

       Hint 2: instead of using 'ap', there is another solution that
       uses "2-column-with", where you 'with' on two things at once:
       The general syntax for this is
         f p with e1 | e2
         ...    | p1 | p2 = ... 
    -}

    -- you'll need to fill in the type of l with the type you defined above
    map-fusion' : {! {A B C : Set} {n : Nat} (g : B → C) (f : A → B) (l : ?) → map g (map f v) == map (g o f) v !}
    map-fusion' = {!!}




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
       where Tree L H is a sorted tree such that L ≤ every key in t ≤ H
    -} 
    data Tree : Key → Key → Set where
      Empty : {L H : Key} -> L ≤ H → Tree L H
      Node : {L H : Key} → (c : Color) (M : Key) (v : Value) (l : Tree L M) (r : Tree M H) -> Tree L H

    {- TASK 6 
       As a sanity-check, prove that Tree L H implies L ≤ H.
       NOTE: You will NOT need to use this function in the remaining code.
    -}
    sanity : {L H : Key} → Tree L H -> L ≤ H
    sanity t = {!!}

    {- TASK 7
       Show that you can "weaken" the bounds on a tree to something less precise.

       Assuming that the operations on ≤ are constant time,
       (weaken-left _ t) and (weaken-right _ t) should
       each take time proportional to the depth of t.  
    -}
    weaken-left : ∀ {L L' H} → L' ≤ L → Tree L H → Tree L' H
    weaken-left L'≤L t = {!!}

    weaken-right : ∀ {L H H'} → H ≤ H' → Tree L H → Tree L H'
    weaken-right H≤H' t = {!!}

    {- TASK 8 
       Define insert.  You will need to give appropriate types for,
       and implement, balance and ins and blackenRoot.  Try to keep 
       the structure of the code as close to the simply-typed
       version as possible.  

       It's OK if the asymptotic complexity of insert is O(depth-of-t^2)
       rather than O(depth-of-t), due to calls to weaken.
    -}

    balance : {!!}
    balance = {!!}

    ins : {!!}
    ins = {!!}

    blackenRoot : {!!}
    blackenRoot = {!!}

    insert : ∀ {L H} → Tree L H → (k : Key) (v : Value) → Tree (min L k) (max H k)
    insert t k v = {!!}

  {- TASK 9
     Give an alternate definition of Sorted which supports a constant-time 'weaken' function,
     and redo the above code for that definition.  
  -}
