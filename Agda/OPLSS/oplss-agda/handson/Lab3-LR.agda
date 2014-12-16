open import Preliminaries

module handson.Lab3-LR where

  {- de Bruijn indices are representd as proofs that 
     an element is in a list -}
  data _∈_ {A : Set} : (x : A) (l : List A) → Set where -- type \in
    i0 : {x : A} {xs : List A} → x ∈ x :: xs
    iS : {x y : A} {xs : List A} → x ∈ xs → x ∈ y :: xs

  {- types of the STLC -}
  data Tp : Set where
    b : Tp             -- uninterpreted base type
    _⇒_ : Tp → Tp → Tp -- type \=>

  {- contexts are lists of Tp's -}
  Ctx = List Tp
  _,,_ : Ctx → Tp → Ctx
  Γ ,, τ = τ :: Γ

  infixr 10 _⇒_
  infixr 9 _,,_
  infixr 8 _⊢_ -- type \entails

  {- Γ ⊢ τ represents a term of type τ in context Γ -}
  data _⊢_ (Γ : Ctx) : Tp → Set where
    c   : Γ ⊢ b -- some constant of the base type
    v   : {τ : Tp} 
        → τ ∈ Γ
        → Γ ⊢ τ 
    lam : {τ1 τ2 : Tp} 
        → Γ ,, τ1 ⊢ τ2
        → Γ ⊢ τ1 ⇒ τ2
    app : {τ1 τ2 : Tp} 
        → Γ ⊢ τ1 ⇒ τ2 
        → Γ ⊢ τ1 
        → Γ ⊢ τ2

  module Examples where
    i : [] ⊢ b ⇒ b
    i = lam (v i0) -- \ x -> x
  
    k : [] ⊢ b ⇒ b ⇒ b
    k = lam (lam (v (iS i0))) -- \ x -> \ y -> x
  
    {- TASK 1: Define a term representing  \ x -> \ y -> y -}
    k' : [] ⊢ b ⇒ b ⇒ b
    k' = {!!}
  

  {- The following proof is like a "0-ary" logical relation.
     It gives a semantics of the STLC in Agda.
     This shows that the STLC is sound, relative to Agda.  
  -}
  module Semantics (B : Set) (elB : B) where 
    -- works for any interpretation of the base type b

    -- function mapping STLC types to Agda types
    ⟦_⟧t : Tp → Set  -- type \(0 and \)0
    ⟦ b ⟧t = B
    ⟦ τ1 ⇒ τ2 ⟧t = ⟦ τ1 ⟧t → ⟦ τ2 ⟧t

    -- function mapping STLC contexts to Agda types
    ⟦_⟧c : Ctx → Set
    ⟦ [] ⟧c = Unit
    ⟦ τ :: Γ ⟧c = ⟦ Γ ⟧c × ⟦ τ ⟧t

    {- TASK 2 : Define the interpretation of terms -}
    ⟦_⟧ : {Γ : Ctx} {τ : Tp} → Γ ⊢ τ → ⟦ Γ ⟧c → ⟦ τ ⟧t
    ⟦ e ⟧ γ = {!!}

    {- the following test should pass
    test : ⟦ Examples.k ⟧ == \ γ x y → x
    test = Refl
    -}



  {- you can ignore the implementation of this module.
     the interface for the components you need is listed below
  -}
  module RenamingAndSubstitution where 

    -- renamings = variable for variable substitutions

    infix 9 _⊇_

    _⊇_ : Ctx → Ctx → Set -- type \sup=
    Γ' ⊇ [] = Unit
    Γ' ⊇ (τ :: Γ) = (Γ' ⊇ Γ) × (τ ∈ Γ')

    extend⊇ : {Γ : Ctx} (Γ' : Ctx) {τ : Tp} → Γ ⊇ Γ' → (Γ ,, τ) ⊇ Γ'
    extend⊇ [] ren = <>
    extend⊇ (τ :: Γ') (ρ , x) = extend⊇ Γ' ρ , iS x

    open List using (_++_)
    extend⊇* : {Γ : Ctx} (Γ' : Ctx) (Γ'' : Ctx) → Γ ⊇ Γ' → (Γ'' ++ Γ) ⊇ Γ'
    extend⊇* Γ' [] ρ = ρ
    extend⊇* Γ' (x :: Γ'') ρ = extend⊇ _ (extend⊇* Γ' Γ'' ρ)

    shift : {Γ : Ctx} {τ : Tp} (Γ' : Ctx) (i : τ ∈ Γ) → τ ∈ (Γ' ++ Γ)
    shift [] i = i
    shift (τ :: Γ) i = iS (shift Γ i)

    ⊇-id : (Γ : Ctx) → Γ ⊇ Γ
    ⊇-id [] = <>
    ⊇-id (τ :: Γ) = extend⊇ Γ (⊇-id Γ) , i0

    ⊇-single : {Γ : Ctx} {τ : Tp} → (Γ ,, τ ⊇ Γ) 
    ⊇-single = extend⊇ _ (⊇-id _)

    -- you can rename a term

    rename : {Γ Γ' : Ctx} {τ : Tp} → Γ' ⊇ Γ → Γ ⊢ τ → Γ' ⊢ τ
    rename ρ c = c
    rename (_ , x') (v i0) = v x'
    rename (ρ , _) (v (iS x)) = rename ρ (v x)
    rename ρ (lam e) = lam (rename (extend⊇ _ ρ , i0) e)
    rename ρ (app e e') = app (rename ρ e) (rename ρ e')


    -- expression-for-variable substitutions

    _⊢c_ : Ctx → Ctx → Set
    Γ' ⊢c [] = Unit
    Γ' ⊢c (τ :: Γ) = (Γ' ⊢c Γ) × (Γ' ⊢ τ) 

    rename-subst : {Γ1 Γ2 Γ3 : Ctx} →  Γ1 ⊇ Γ2 → Γ2 ⊢c Γ3 → Γ1 ⊢c Γ3
    rename-subst {Γ1} {Γ2} {[]} ρ θ = <>
    rename-subst {Γ1} {Γ2} {τ3 :: Γ3} ρ (θ , e) = rename-subst ρ θ , rename ρ e
  
    addvar : {Γ Γ' : Ctx} {τ : Tp} → Γ ⊢c Γ' → (Γ ,, τ) ⊢c (Γ' ,, τ)
    addvar θ = rename-subst ⊇-single θ , v i0

    id-subst : {Γ : Ctx} → Γ ⊢c Γ
    id-subst {[]} = <>
    id-subst {τ :: Γ} = rename-subst ⊇-single (id-subst {Γ}) , v i0

    subst : {Γ Γ' : Ctx}{τ : Tp} → Γ ⊢c Γ' → Γ' ⊢ τ  → Γ ⊢ τ
    subst θ c = c
    subst (θ , e) (v i0) = e
    subst (θ , e) (v (iS x)) = subst θ (v x)
    subst θ (lam e) = lam (subst (addvar θ) e)
    subst θ (app e e') = app (subst θ e) (subst θ e')

    subst1 : {τ τ0 : Tp} → [] ⊢ τ0 → ([] ,, τ0) ⊢ τ → [] ⊢ τ
    subst1 e0 e = subst (<> , e0) e

    -- these are not tasks (unless you really want); I didn't get to prove them; sorry!
    compose : {τ1 τ2 : Tp} {Γ : Ctx} (θ : [] ⊢c Γ) (e' : [] ⊢ τ1) (e : Γ ,, τ1 ⊢ τ2)
            → subst (θ , e') e == subst1 e' (subst (addvar θ) e)
    compose = {!!}

    ident : {Γ : Ctx} {τ : Tp} {e : Γ ⊢ τ} → e == subst (id-subst) e 
    ident = {!!}

  open RenamingAndSubstitution using (subst1 ; _⊢c_ ; subst ; ident ; compose)
  {- θ : Γ ⊢c Γ' means θ is a substitution for Γ' in terms of Γ.  It is defined as follows:

    _⊢c_ : Ctx → Ctx → Set
    Γ' ⊢c [] = Unit
    Γ' ⊢c (τ :: Γ) = (Γ' ⊢c Γ) × (Γ' ⊢ τ) 

    -- apply a substitution to a term
    subst : {Γ Γ' : Ctx}{τ : Tp} → Γ ⊢c Γ' → Γ' ⊢ τ  → Γ ⊢ τ

    -- substitution for a single variable
    subst1 : {τ τ0 : Tp} → [] ⊢ τ0 → ([] ,, τ0) ⊢ τ → [] ⊢ τ

    -- you will need these two properties:
    compose : {τ1 τ2 : Tp} {Γ : Ctx} (θ : [] ⊢c Γ) (e' : [] ⊢ τ1) (e : Γ ,, τ1 ⊢ τ2)
            → subst (θ , e') e == subst1 e' (subst (addvar θ) e)

    ident : {Γ : Ctx} {τ : Tp} {e : Γ ⊢ τ} → e == subst (id-subst) e 
  -}

  
  module OpSem where
    -- step relation
    data _↦_ : {τ : Tp} → [] ⊢ τ → [] ⊢ τ → Set where
      Step/app  :{τ1 τ2 : Tp} {e e' : [] ⊢ τ1 ⇒ τ2} {e1 : [] ⊢ τ1}
             → e ↦ e'
             → (app e e1) ↦ (app e' e1)
      Step/β : {τ1 τ2 : Tp} {e : [] ,, τ1 ⊢ τ2} {e1 : [] ⊢ τ1}
             → (app (lam e) e1) ↦ subst1 e1 e 

    -- reflexive/transitive closure
    data _↦*_ : {τ : Tp} → [] ⊢ τ → [] ⊢ τ → Set where
      Done : {τ : Tp} {e : [] ⊢ τ} → e ↦* e
      Step : {τ : Tp} {e1 e2 e3 : [] ⊢ τ} 
           → e1 ↦ e2  →  e2 ↦* e3
           → e1 ↦* e3
  open OpSem


  {- Next, you will prove "very weak normalization".  The theorem is
     that any closed term *of base type b* evaluates to the constant c.
     No claims are made about terms of function type.
  -}
  module VeryWeakNormalization where

    WN : (τ : Tp) → [] ⊢ τ → Set
    -- WN_τ(e) iff e ↦* c
    WN b e = e ↦* c
    -- WN_τ(e) iff for all e1 : τ1, if WN_τ1(e1) then WN_τ2(e e1)
    WN (τ1 ⇒ τ2) e = (e1 : [] ⊢ τ1) → WN τ1 e1 → WN τ2 (app e e1)

    -- extend WN to contexts and substitutions
    WNc : (Γ : Ctx) → [] ⊢c Γ → Set
    WNc [] θ = Unit
    WNc (τ :: Γ) (θ , e) = WNc Γ θ × WN τ e

    {- TASK 3 : show that the relation is closed under head expansion: -}
    head-expand : (τ : Tp) {e e' : [] ⊢ τ} → e ↦ e' → WN τ e' → WN τ e
    head-expand = {!!}

    {- TASK 4 : prove the fundamental theorem 

    Hint: you may find it helpful to use 
      transport : {A : Set} (B : A → Set) {a1 a2 : A} → a1 == a2 → (B a1 → B a2)
    to coerce by a propositional equality.  
    -}
    fund : {Γ : Ctx} {τ : Tp} {θ : [] ⊢c Γ} 
         → (e : Γ ⊢ τ)
         → WNc Γ θ 
         → WN τ (subst θ e)
    fund = {!!}

    {- TASK 5 : conclude weak normalization at base type -}
    corollary : (e : [] ⊢ b) → e ↦* c
    corollary = {!!}

  {- TASK 6 : change the definition of the logical relation so that you also can conclude normalization 
              at function type.
  -}
  module WeakNormalization where

    open RenamingAndSubstitution using (addvar)
    --- you will want to use
    --    addvar : {Γ Γ' : Ctx} {τ : Tp} → Γ ⊢c Γ' → (Γ ,, τ) ⊢c (Γ' ,, τ)

    -- Hint: you will need a couple of lemmas about ↦* that we didn't need above
    -- (I used three of them)

    {- TASK 6a -}
    corollary1 : (e : [] ⊢ b) → e ↦* c 
    corollary1 e = {!!}

    {- TASK 6b -}
    corollary2 : {τ1 τ2 : Tp} (e : [] ⊢ τ1 ⇒ τ2) → Σ \(e' : _) → e ↦* (lam e')
    corollary2 e = {!!}
