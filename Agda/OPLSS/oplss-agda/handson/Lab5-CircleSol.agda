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

module handson.Lab5-CircleSol where

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
 
  {- TASK 1: prove that succ is a bijection -}

  pred : Int → Int
  pred Zero = Neg One
  pred (Pos (S n)) = Pos n
  pred (Pos One) = Zero
  pred (Neg n) = Neg (S n)

  succ-pred : (n : Int) → (succ (pred n)) == n
  succ-pred (Pos One) = Refl
  succ-pred (Pos (S y)) = Refl
  succ-pred (Zero) = Refl
  succ-pred (Neg y) = Refl
 
  pred-succ : (n : Int) → (pred (succ n)) == n
  pred-succ (Pos y) = Refl
  pred-succ (Zero) = Refl
  pred-succ (Neg One) = Refl
  pred-succ (Neg (S y)) = Refl

  succEquiv : Bijection Int Int
  succEquiv = (succ , is-bijection pred pred-succ succ-pred)

  {- The universal cover of the circle.
     See "Calculating the Fundamental Group of the Circle in HoTT"
     for intuition. 

     The rest of this proof starts in Section V.B of that paper.
     Try to invent it on your own before peeking!
  -}
  Cover : S¹ → Type
  Cover x = S¹-rec Int (ua succEquiv) x
  
  {- TASK -}
  transport-Cover-loop : (transport Cover loop) == succ
  transport-Cover-loop = 
    transport Cover loop                  
      =〈 transport-ap-assoc Cover loop 〉
    transport (λ x → x) (ap Cover loop)
      =〈 ap   (transport (λ x → x))
              (βloop/rec Int (ua succEquiv)) 〉 
    transport (λ x → x) (ua succEquiv)
      =〈 transport-Here _ 〉 
    succ ∎
  
  {- TASK -}
  transport-Cover-!loop : (transport Cover (! loop)) == pred
  transport-Cover-!loop = 
    transport Cover (! loop)                             
      =〈 transport-ap-assoc Cover (! loop) 〉
    transport (λ x → x) (ap Cover (! loop))             
      =〈 ap (transport (λ x → x)) (ap-! Cover loop)〉
    transport (λ x → x) (! (ap Cover loop)) 
      =〈 ap  (λ y → transport (λ x → x) (! y))
             (βloop/rec Int (ua succEquiv)) 〉
    transport (λ x → x) (! (ua succEquiv))                     
      =〈 transport-Here! succEquiv 〉
    pred ∎
  
  encode : {x : S¹} →  base == x  →  Cover x
  encode α = transport Cover α Zero
  
  encode' : base == base → Int
  encode' α = encode {base} α
  
  {- TASK -}
  loop^ : Int → base == base
  loop^ Zero        = Refl
  loop^ (Pos One)   = loop
  loop^ (Pos (S n)) = loop ∘ loop^ (Pos n)
  loop^ (Neg One)   = ! loop
  loop^ (Neg (S n)) = ! loop ∘ loop^ (Neg n)

  {- TASK 
     Prove this composite is the identity.  
  -}
  abstract
    encode-loop^ : (n : Int) → (encode (loop^ n)) == n
    encode-loop^ Zero = Refl
    encode-loop^ (Pos One) = ap= transport-Cover-loop
    encode-loop^ (Pos (S n)) = 
      encode (loop^ (Pos (S n)))
        =〈 Refl 〉 
      transport Cover (loop ∘ loop^ (Pos n)) Zero
        =〈 ap= (transport-∘ Cover loop (loop^ (Pos n))) 〉 
      transport  Cover loop 
                 (transport Cover (loop^ (Pos n)) Zero)      
        =〈 ap= transport-Cover-loop 〉
      succ (transport Cover (loop^ (Pos n)) Zero)                      
        =〈 Refl 〉 
      succ (encode (loop^ (Pos n))) 
        =〈 ap succ (encode-loop^ (Pos n)) 〉 
      succ (Pos n) ∎
    encode-loop^ (Neg One) = ap= transport-Cover-!loop
    encode-loop^ (Neg (S n)) = 
      transport Cover (! loop ∘ loop^ (Neg n)) Zero                    
        =〈 ap= (transport-∘ Cover (! loop) (loop^ (Neg n))) 〉
      transport Cover (! loop) (transport Cover (loop^ (Neg n)) Zero)  
        =〈 ap= transport-Cover-!loop 〉
      pred (transport Cover (loop^ (Neg n)) Zero) 
        =〈 ap pred (encode-loop^ (Neg n)) 〉 
      pred (Neg n) ∎

  {- TASK 
     Prove loop^-encode.
     Hint: Generalize the theorem statement so that you can prove it by path induction.
           This will require defining a version of loop^ with a more general type.
  -}

  loop^-preserves-pred 
    : (n : Int) → (loop^ (pred n)) == (! loop ∘ loop^ n)
  loop^-preserves-pred (Pos One) = ! (!-inv-l loop)
  loop^-preserves-pred (Pos (S y)) = 
       ! (∘-assoc (! loop) loop (loop^ (Pos y))) 
     ∘ (! (ap (λ x → x ∘ loop^ (Pos y)) (!-inv-l loop)) 
     ∘ ! (∘-unit-l (loop^ (Pos y))))
  loop^-preserves-pred Zero = Refl
  loop^-preserves-pred (Neg One) = Refl
  loop^-preserves-pred (Neg (S y)) = Refl

  decode : {x : S¹} → Cover x → base == x
  decode {x} = 
   S¹-induction 
    (λ x' → Cover x' → base == x')
    loop^
    loop^-respects-loop 
    x where
     abstract -- prevent Agda from normalizing
      loop^-respects-loop : transport (λ x' →  Cover x' → base == x') loop loop^ == (λ n → loop^ n) 
      loop^-respects-loop = 
         (transport (λ x' →  Cover x' → base == x') loop loop^  =〈 transport-→ Cover (_==_ base) loop loop^ 〉
        
            transport (λ x' → base == x') loop 
          o loop^ 
          o transport Cover (! loop)                              =〈 λ= (λ y → transport-Path-right loop (loop^ (transport Cover (! loop) y))) 〉
       
            (λ p → loop ∘ p) 
          o loop^ 
          o transport Cover (! loop)                              =〈 λ= (λ y → ap (λ x' → loop ∘ loop^ x') (ap= transport-Cover-!loop)) 〉
       
            (λ p → loop ∘ p)
          o loop^ 
          o pred                                                  =〈 Refl 〉 
       
          (λ n → loop ∘ (loop^ (pred n)))                         =〈 λ= (λ y → move-left-! _ loop (loop^ y) (loop^-preserves-pred y)) 〉 
       
          (λ n → loop^ n)
          ∎)


  decode-encode  : {x : S¹} (α : base == x)
                 → (decode (encode α)) == α
  decode-encode {x} α = path-induction (\ x α → (decode (encode α)) == α) Refl α

  loop^-encode  : (α : base == base)
                 → (loop^ (encode α)) == α
  loop^-encode α = decode-encode α

  theorem : Bijection (base == base) Int
  theorem = encode , is-bijection decode loop^-encode encode-loop^
