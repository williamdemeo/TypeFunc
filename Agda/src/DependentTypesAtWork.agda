module DependentTypesAtWork where

-- This file contains some Agda code I wrote while going through the tutorial
-- "Dependent Types at Work" by Ana Bove and Peter Dybjer, available at
-- http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf

-- For a list of Emacs Agda Mode Key combinations, see
-- http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Docs.EmacsModeKeyCombinations
-- Most frequently used is C-c C-l

-- SECTION 2: Simply Typed Functional Programming in Agda

-- SECTION 2.1: Truth Values

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


-- SECTION 2.2: Natural Numbers

-- The type of natural numbers is defined as the following data type:

data ℕ : Set where
 zero : ℕ
 succ : ℕ → ℕ

-- In languages such as Haskell, such data types are usually known as recursive:
-- a natural number is either zero or the successor of another natural number.
-- In constructive type theory, one usually refers to them as inductive types or
-- inductively defined types.

-- Predecessor
pred : ℕ → ℕ
pred zero = zero
pred (succ n) = n

-- Addition
_+_ : ℕ → ℕ → ℕ
zero + n = n
succ m + n = succ (m + n)

-- Multiplication
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


-- SECTION 2.3: Lambda Notation and Polymorphism

-- Lambda abstraction is either written 
--    Curry-style: \x → e    (without type label)
-- or
--    Church-style: \(x : A) -> e  (with type label)
id : (A : Set) → A → A
id = \(A : Set) → \(x : A) → x

-- Alternatively, the identity could be defined as follows:
id2 : (A : Set) → A → A
id2 A x = x

-- Alternatively, since the type checker can figure out the 
-- type of the argument in this case, we can use a wild card character _.
id3 : (A : Set) → A → A
id3 _ x = x

-- The K combinator manufactures constant functions.
-- The S combinator is a generalized version of application.
-- (See: https://en.wikipedia.org/wiki/Combinatory_logic#Examples_of_combinators)

-- In Agda, the K combinator is defined as follows:
K : (A B : Set) → A → B → A
K _ _ x _ = x
-- Note that we used a wild card not only for the type, but also for 
-- the second variable, y, since the expression does not depend on y.

-- Alternatively, we could specify the types explicitly:
K2 : (A B : Set) → A → B → A
K2 A B x y = x

-- or even more explicitly:
K3 : (A B : Set) → A → B → A
K3 = \(A : Set) → \(B : Set) → \(x : A) → \(y : B) → x

-- In Agda, the S combinator is defined as follows:
S : (A B C : Set) → (A → B → C) → (A → B) → A → C
-- which says, take types A B C, and two functions,
--     f: A → (B → C)  
--     g: A → B
-- and return the function f(x)(g(x)): A → C: 
S A B C f g x = f x (g x)


-- SECTION 2.4: Implicit Arguments

