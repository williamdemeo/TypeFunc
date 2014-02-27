open import Preliminaries

module handson.Lab1 where

  module Map where

    {- List A is a datatype with constructors
       []   : List A
       _::_ : A → List A → List A
       the _'s mean that :: gets used infix.

       See Preliminaries.agda for the definition (and for other definitions that
       are refered to in this file.
    -}
  
    map : {A B : Set} → (f : A → B) → List A → List B
    map f [] = []
    map f (x :: xs) = f x :: map f xs

    module ExplicitArgs where
      data Length {A : Set} : List A → Nat → Set where
        L[] : Length [] 0
        L:: : (n : Nat) (x : A) (xs : List A) → Length xs n → Length (x :: xs) (S n)

      {- TASK 1 
         Prove that map preserves the length of a list: 
      -}
      map-length : {A B : Set} (f : A → B) (xs : List A) (n : Nat)
                 → Length xs n
                 → Length (map f xs) n
      map-length f xs len = {!!}

    module ImplicitArgs where
      {- TASK 2 
         To practice implicit arguments, define an alternate version of Length 
         that makes use of implicit arguments for the constructors.
         Decide what to make implicit based on what was inferable in the above proof.  
      -}
      data Length {A : Set} : List A → Nat → Set where

      {- TASK 3 
         Prove map-length with implicit arguments:
      -}
      map-length : {A B : Set} {f : A → B} {xs : List A} {n : Nat} 
                 → Length xs n
                 → Length (map f xs) n
      map-length len = {!!}

  module Nth where

    module Wrong where
      {- TASK 4

         'nth n l' takes a natural number n, and a list,
         and returns the n^th element of the list
         (where the first element is number 0).  
  
         In ML and Haskell, nth has the following type.
         What goes wrong if you try to define nth with this type
         in Agda?
      -}
  
      nth : {A : Set} → Nat → List A → A
      nth n xs = {!!} -- nothing to return here, and no exceptions bc Agda is total


    {- TASK 5

       Maybe A (or A option for the ML programmers in the crowd)
       is a datatype with constructors
       None : Maybe A
       Some : A → Maybe A

       Define 'nth' with the following type:
    -}

    nth : {A : Set} → Nat → List A → Maybe A
    nth n xs = {!!}

    {- The type Fin n represents "numbers less than n". -}
    data Fin : Nat → Set where
      FZ : {n : Nat} → Fin (S n)
      FS : {n : Nat} → Fin n → Fin (S n)

    {- for example, the following function maps 
       "each number less than n" to a Nat, forgetting the fact 
       that it's less than n -}
    forget : {n : Nat} → Fin n → Nat
    forget FZ = 0
    forget (FS n) = S (forget n)

    {- Here are some examples: -}
    module Examples where
      three : Fin 4 
      three = FS (FS (FS FZ))

      {- doesn't type check
      four : Fin 4
      four = FS (FS (FS (FS FZ)))
      -}

      three' : Fin 5
      three' = FS (FS (FS FZ))

      four : Fin 5
      four = FS (FS (FS (FS FZ)))


    {- TASK 6 
       Prove the following spec for 'nth', whcih says that it returns
       Some when the index is in bounds.

       The type "M == N" is called propositional equality;
       it is an inductive family with one constructor
         Refl : M == M
    -}
    open Map.ImplicitArgs 
    nth-spec : {A : Set} {n : Nat} {l : List A} → (m : Fin n) → Length l n
             → Σ \(a : A) → nth (forget m) l == Some a
    nth-spec i len = {!!}


    {- TASK 7 
       Define a version of nth that takes an index that is definitely in bounds, 
       and always returns an element of A: 
       We can strengthen the post-condition by imposing a stronger pre-condition.  
    -}
    nth' : {A : Set} (n : Nat) (l : List A) → Fin n → Length l n → A
    nth' n xs i len = {!!}


  {- Next, you'll practice using 'with' 
    
     Either A B is a sum (disjoint union) type, with constructors
       Inl : A → Either A B
       Inr : B → Either A B

     Void is an empty sum type

     A predicate P is decidable if, for all arguments x, either P x holds or P x is false:
       (x : A) → Either (P x) (P x → Void)  
  -}
  module Filter {A : Set} {P : A → Set} (decideP : (x : A) → Either (P x) (P x → Void)) where

    filter : List A → List A
    filter [] = []
    filter (x :: xs) with decideP x 
    ... | Inl _  = x :: filter xs
    ... | Inr _ = filter xs

    {- means that P holds for all elements of the list -}
    data Everywhere : List A → Set where
      E[] : Everywhere []
      E:: : {x : A} {xs : List A} → P x → Everywhere xs → Everywhere (x :: xs)

    {- TASK 8 
       Prove that P holds for all elements of (filter l)
    -}
    filter-invariant : (l : List A) → Everywhere (filter l)
    filter-invariant xs = {!!}


  {- The next task is harder---if you don't get to this, that's fine.
     It uses the same techniques as above, but will ask you to chain
     together more lemmas from a library.
    
     In this task, you will prove that simple tree insert (without balancing)
     returns a sorted tree.  
  -}

  open FancyOrder
  module TreeInsertSorted (Keys : DecidableOrder) (Value : Set) where 

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

    data Tree : Set where
      Empty : Tree 
      Node : Tree → Key → Value → Tree → Tree

    insert : Tree → Key → Value → Tree 
    insert Empty k v = Node Empty k v Empty
    insert (Node l k' v' r) k v with compare k k'
    ... | Equal _ = Node l k v r
    ... | Less _ _ = Node (insert l k v) k' v' r 
    ... | Greater _ _ = Node l k' v' (insert r k v)

    -- means t is sorted and L ≤ everything in t ≤ H
    data Sorted : Key → Tree → Key → Set where
      S-Empty : {L H : Key} → L ≤ H → Sorted L Empty H 
      S-Node  : {L M H : Key} {l r : Tree} {v : Value}
              → Sorted L l M
              → Sorted M r H
              → Sorted L (Node l M v r) H 

    {- TASK 9 
       Prove that you can "weaken" the bounds on a tree, making them less precise.
    -}
    weaken : {L L' H H' : Key} {t : Tree} → L' ≤ L → H ≤ H' → Sorted L t H → Sorted L' t H'
    weaken low high s = {!!}

    {- TASK 10 
       Prove that inserting into a sorted tree returns a sorted tree,
       with updated bounds:
    -}
    insert-sorted : {L H : Key} {t : Tree} {k : Key} {v : Value}
                  → Sorted L t H
                  → Sorted (min L k) (insert t k v) (max H k)
    insert-sorted s = {!!}
