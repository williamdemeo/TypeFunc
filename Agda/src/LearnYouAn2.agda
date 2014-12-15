module LearnYouAn2 where

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

  
