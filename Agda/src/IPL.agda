-- Based on the tutorial "Learn You an Agda"

module IPL where

  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  (suc n) + m = suc (n + m)

  data _even : ℕ → Set where
    ZERO : zero even
    STEP : ∀ x → x even → suc (suc x) even

  proof₁ : suc (suc (suc (suc zero))) even 
  proof₁ = STEP (suc (suc zero)) (STEP zero ZERO)

  proof₂ : ℕ → ℕ
  proof₂ ν = ν

  proof₂′ : (A : Set) → A → A
  proof₂′ _ x = x


  data _∧_ (P : Set) (Q : Set) : Set where
    ∧-intro : P → Q → (P ∧ Q)

  proof₃ : {P Q : Set} → (P ∧ Q) → P
  proof₃ (∧-intro p q) = p

  proof₄ : {P Q : Set} → (P ∧ Q) → Q
  proof₄ (∧-intro p q) = q

  _⇔_ : (P : Set) → (Q : Set) → Set
  a ⇔ b = (a → b) ∧ (b → a)
  
  ∧-comm′ : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
  ∧-comm′ (∧-intro p q) = ∧-intro q p

  ∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
  ∧-comm = ∧-intro ∧-comm′ ∧-comm′

  ∧-assoc₁ : { P Q R : Set } → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
  ∧-assoc₁ (∧-intro (∧-intro p q) r) = ∧-intro p (∧-intro q r)

  ∧-assoc₂ : { P Q R : Set } → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
  ∧-assoc₂ (∧-intro p (∧-intro q r)) = ∧-intro (∧-intro p q) r

  ∧-assoc : { P Q R : Set } → ((P ∧ Q) ∧ R) ⇔  (P ∧ (Q ∧ R))
  ∧-assoc = ∧-intro ∧-assoc₁ ∧-assoc₂

  data _∨_ (P Q : Set) : Set where
    ∨-intro₁ : P → P ∨ Q
    ∨-intro₂ : Q → P ∨ Q

  data ⊥ : Set where
