{-# OPTIONS --without-K #-}

open import PreliminariesHoTT
open S¹
{- 
The circle is a "higher-dimensional inductive type"
with constructors

  base : S¹
  loop : base == base

To define functions on the circle, you use circle recursion,

       S¹-rec : {l : Level} {C : Set l} 
              -> (c : C)
              -> (α : c == c)
              -> S¹ -> C

This says that to map the circle into a type C, 
it suffices to find a point c:C and a path α:c==c.
This has the following reduction rules:

  S¹-rec C c α base = c

  βloop/rec : {l : Level} {C : Set l} 
            -> (c : C)
            -> (α : c == c)
            -> (ap (S¹-rec c α) loop) == α

When you apply S¹-rec to the base point, you get c.
When you apply it (in the sense of 'ap') to loop,
you get α.  Note that the former is a definitional equality,
whereas the latter is a propositional equality.

To prove somethng about the circle, you can use

  S¹-induction :  (C : S¹ -> Type)
          -> (c : C base) 
             (α : (transport C loop c) == c)
          -> (x : S¹) -> C x

See the early sections of 
  Calculating the Fundamental Group of the Circle in Homotopy Type Theory
  Licata and Shulman, LICS 2013
for more info.  

The implementation of S¹ is a bit of a hack, so the way Agda displays
base will be pretty ugly.  Use C-u C-c C-, and other C-u-prefixed commands
to see the non-normalized version of a goal.  

-}

module handson.Lab5-Circle where

  {- TASK 
     The following principle, called uniqueness of identity proofs,
     is incompatible with univalence.  Observe that 
  -}
  


  data Positive : Type where
    One : Positive
    S   : (n : Positive) → Positive

  data Int : Type where
    Pos  : (n : Positive) → Int
    Zero : Int
    Neg  : (n : Positive) → Int
 
  succ : Int → Int
  succ Zero = Pos One
  succ (Pos n) = Pos (S n)
  succ (Neg One) = Zero
  succ (Neg (S n)) = Neg n

  pred : Int → Int
  pred = {!!}
 
  {- TASK 1: prove that succ is a bijection -}

  succBij : Bijection Int Int
  succBij = (succ , is-bijection pred {!!} {!!})

  {- The universal cover of the circle.
     See "Calculating the Fundamental Group of the Circle in HoTT"
     for intuition. 

     The rest of this proof starts in Section V.B of that paper.
     Try to invent it on your own before peeking!
  -}
  Cover : S¹ → Type
  Cover x = S¹-rec Int (ua succBij) x
  
  {- TASK -}
  transport-Cover-loop : (transport Cover loop) == succ
  transport-Cover-loop = {!!}
  
  {- TASK -}
  transport-Cover-!loop : (transport Cover (! loop)) == pred
  transport-Cover-!loop = {!!}
  
  encode : {x : S¹} →  base == x  →  Cover x
  encode α = transport Cover α Zero
  
  encode' : base == base → Int
  encode' α = encode {base} α
  
  {- TASK 
  Define a function loop^ n such that
  loop^ 0 = Refl
  loop^ n  = loop ∘ loop ... ∘ loop (n times)
  loop^ -n = !loop ∘ !loop ... ∘ !loop (n times)
  -}
  loop^ : Int → base == base
  loop^ n        = {!!}

  {- TASK 
     Prove this composite is the identity.  
  -}
  abstract
    encode-loop^ : (n : Int) → (encode (loop^ n)) == n
    encode-loop^ n = {!!}

  {- TASK 
     Prove loop^-encode.
     Hint: Generalize the theorem statement so that you can prove it by path induction.
           This will require defining a version of loop^ with a more general type.
  -}

  loop^-encode  : (α : base == base)
                 → (loop^ (encode α)) == α
  loop^-encode α = {!!}

  theorem : Bijection (base == base) Int
  theorem = encode , is-bijection loop^ loop^-encode encode-loop^
