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
-- (The symbol ¬ is produced by typing \not.)

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

-- The binary function for equivalence can be defined by pattern matching on both arguments.
-- Note the ≅ symbol is produced by typing \cong.
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

_*_ : ℕ → ℕ → ℕ
zero * n = zero
succ m * n = (m * n) + m

-- NB: in the tutorial, it is claimed that we can leave out the parens in 
-- the expression (n * m).  However, for me this fails to parse.

-- Exercise 1: Write the cut-off subtraction function---the function 
-- on natural numbers, which returns 0 if the second argument is greater 
-- than or equal to the first. Also write some more numerical functions 
-- like < or ≤.

-- cut-off subtraction binary function
_c-_ : ℕ → ℕ → ℕ
zero c- _ = zero
succ m c- zero = succ m
succ m c- succ n = m c- n

-- less than binary function
_<_ : ℕ → ℕ → Bool
_ < zero = false
zero < succ n = true
succ n < succ m = n < m

-- less or equal binary function
_leq_ : ℕ → ℕ → Bool
zero leq _ = true
succ n leq zero = false
succ n leq succ m = n leq m


-- Lambda abstraction is either written 
--    Curry-style: \x → e    (without type label)
-- or
--    Church-style: \(x : A) -> e  (with type label)
id : (A : Set) → A → A
id = \(A : Set) → \(x : A) → x
