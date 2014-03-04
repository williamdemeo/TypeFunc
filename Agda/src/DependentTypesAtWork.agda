module DependentTypesAtWork where


-- Datatypes are introduced by a data declaration, giving the name and
-- type of the datatype as well as the constructors and their types.
-- For example, Bool is a member of the type Set.
-- (Bool is a "small" type and Set is a "large" type.)

data Bool : Set where  
  true : Bool
  false : Bool

-- Set cannot be a member of the type Set.
-- If we added Set : Set the system would become inconsistent.

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

-- In languages such as Haskell, such data types are usually known as recursive:
-- a natural number is either zero or the successor of another natural number.
-- In constructive type theory, one usually refers to them as inductive types or
-- inductively defined types.

pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

-- NB: in the tutorial, it is claimed that we can leave out the parens in 
-- the expression (n * m).  However, for me this fails to parse.
_*_ : ℕ → ℕ → ℕ
zero * n = zero
succ n * m = (n * m) + m


-- Lambda abstraction is either written 
--    Curry-style: \x → e    (without type label)
-- or
--    Church-style: \(x : A) -> e  (with type label)
id : (A : Set) → A → A
id = \(A : Set) → \(x : A) → x
