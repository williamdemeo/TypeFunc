
data ℕ : Set where
zero : ℕ
suc : ℕ → ℕ


_+_ : ℕ → ℕ → ℕ
zero + zero = zero
zero + n = n
(suc n) + n′ = suc (n + n′)
