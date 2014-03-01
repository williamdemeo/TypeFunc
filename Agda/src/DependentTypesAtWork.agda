module DependentTypesAtWork where

-- Bool is a member of the type Set.
-- Bool is a "small" type and Set is a "large" type.
-- Set cannot be a member of the type Set.
-- If we added Set : Set the system would become inconsistent.

data Bool : Set where  
  true : Bool
  false : Bool

¬ : Bool → Bool
¬ true = false
¬ false = true


-- In Agda we cannot infer types in general, but we can always check whether a certain term
-- has a certain type provided it is normal. The reason for this is that the type-checking 
-- algorithm in Agda uses normalisation (simplification), and without the normality restriction 
-- it may not terminate. We will discuss some aspects of type

-- Agda checks that patterns cover all cases and does not accept functions with missing patterns.  
-- For example if ¬ lacked the last line defining ¬ false, Agda would reject it.
-- All programs in Agda must be total.

_≅_ : Bool → Bool → Bool
true ≅ true = true
true ≅ false = false
false ≅ true = false
false ≅ false = true

_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ false = false
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true ∨ _ = true
_ ∨ true = true
_ ∨ _ = false

_⊃_ : Bool → Bool → Bool
true ⊃ true = true
true ⊃ false = false
false ⊃ _ = true

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
succ n * m = (n * m) + m



