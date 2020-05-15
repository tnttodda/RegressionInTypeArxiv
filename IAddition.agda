{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (𝟚;₀;₁)
open import InfSequence
open import Prelude
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import SearchableTypes
open import NaturalsOrder

module IAddition where

-- Integer data type, with addition and conversion from 𝟛
data ℤ : 𝓤₀ ̇ where
  +_ : ℕ → ℤ
  -𝟙-_ : ℕ → ℤ

_+ℤ_ : ℤ → ℤ → ℤ
(+ x) +ℤ (+ y) = + (x +ℕ y)
(+ zero) +ℤ (-𝟙- y) = -𝟙- y
(+ succ x) +ℤ (-𝟙- zero) = + x
(+ succ x) +ℤ (-𝟙- succ y) = (+ x) +ℤ (-𝟙- y)
(-𝟙- x) +ℤ (+ zero) = -𝟙- x
(-𝟙- zero) +ℤ (+ succ y) = + y
(-𝟙- succ x) +ℤ (+ succ y) = (-𝟙- x) +ℤ (+ y)
(-𝟙- x) +ℤ (-𝟙- y) = -𝟙- succ (x +ℕ y)

𝟛→ℤ : 𝟛 → ℤ
𝟛→ℤ ₋₁ = -𝟙- 0
𝟛→ℤ ₀ = + 0
𝟛→ℤ ₁ = + 1

-- Implementation of "addition"/midpoint operator from Di Gianantonio 2006

-- Helper functions for the auxiliary operator
+'' : ℤ → 𝟛
+'' (-𝟙- succ n) = ₋₁
+'' (-𝟙- 0) = ₀
+'' (+ 0) = ₀
+'' (+ 1) = ₀
+'' (+ succ (succ n)) = ₁

+''' : ℤ → ℤ
+''' (-𝟙- succ z) = ((-𝟙- succ z) +ℤ (+ 4))
+''' (-𝟙- 0) = (-𝟙- 0)
+''' (+ 0) = (+ 0)
+''' (+ 1) = (+ 1)
+''' (+ succ (succ z)) = ((+ succ (succ z)) +ℤ (-𝟙- 3))

-- Auxiliary operator
_⊕ₐᵤₓ_ : 𝕀 → 𝕀 → ℤ → 𝕀
(a ⊕ₐᵤₓ b) i 0 = +'' ((i +ℤ i) +ℤ (𝟛→ℤ (a 0) +ℤ 𝟛→ℤ (b 0)))
(a ⊕ₐᵤₓ b) i (succ m) = (tail a ⊕ₐᵤₓ tail b) (+''' ((i +ℤ i) +ℤ (𝟛→ℤ (a 0) +ℤ 𝟛→ℤ (b 0)))) m

-- "Addition"/midpoint operator
mid _⊕_ : 𝕀 → 𝕀 → 𝕀
mid x y = (tail x ⊕ₐᵤₓ tail y) (𝟛→ℤ (head x) +ℤ 𝟛→ℤ (head y))
_⊕_ = mid

-- Continuity of the auxiliary function:
-- for all n : ℕ, α,β : 𝕀 × 𝕀 and z₁,z₂ : ℤ
-- if α,β are equal modulo ((succ n , *),(succ n , *)) and z₁,z₂ : ℤ are equal
-- then (tail (pr₁ α) ⊕ tail (pr₂ α)) z₁ and (tail (pr₁ β) ⊕ tail (pr₂ β)) z₂ are equal modulo (n , *)
aux-continuous : ∀ n → (α β : ST-Type (×* 𝕀* 𝕀*)) (z₁ z₂ : ℤ) → z₁ ≡ z₂
                                   → ST-≈ (×* 𝕀* 𝕀*) α β ((succ n , *) , (succ n , *))
                                   → ST-≈ 𝕀* ((tail (pr₁ α) ⊕ₐᵤₓ tail (pr₂ α)) z₁)
                                                     ((tail (pr₁ β) ⊕ₐᵤₓ tail (pr₂ β)) z₂) (n , *)
aux-continuous n (α₁ , α₂) (β₁ , β₂) z .z refl (α≈β₁ , α≈β₂) 0 k<n =
             ap (λ ■ → +'' ((z +ℤ z) +ℤ (𝟛→ℤ ■ +ℤ 𝟛→ℤ (α₂ 1)))) (α≈β₁ 1 k<n)
           ∙ ap (λ ■ → +'' ((z +ℤ z) +ℤ (𝟛→ℤ (β₁ 1) +ℤ 𝟛→ℤ ■))) (α≈β₂ 1 k<n)
aux-continuous (succ n) (α₁ , α₂) (β₁ , β₂) z .z refl (α≈β₁ , α≈β₂) (succ k) k<n =
     aux-continuous n (tail α₁ , tail α₂) (tail β₁ , tail β₂)
         (+''' ((z +ℤ z) +ℤ (𝟛→ℤ (α₁ 1) +ℤ 𝟛→ℤ (α₂ 1))))
         (+''' ((z +ℤ z) +ℤ (𝟛→ℤ (β₁ 1) +ℤ 𝟛→ℤ (β₂ 1))))
         (ap (λ ■ → +''' ((z +ℤ z) +ℤ (𝟛→ℤ ■ +ℤ 𝟛→ℤ (α₂ 1)))) (α≈β₁ 1 *)
         ∙ ap (λ ■ → +''' ((z +ℤ z) +ℤ (𝟛→ℤ (β₁ 1) +ℤ 𝟛→ℤ ■))) (α≈β₂ 1 *))
         ((λ j → α≈β₁ (succ j)) , (λ j → α≈β₂ (succ j)))
         k k<n 

-- Continuity of the "addition"/midpoint operator
mid-continuous : continuous² (×* 𝕀* 𝕀*) 𝕀* (uncurry mid)
mid-continuous (n , *) = m , γ where
  m : ST-Moduli (×* 𝕀* 𝕀*)
  m = (succ n , *) , (succ n , *)
  γ : uc-mod² (×* 𝕀* 𝕀*) 𝕀* (uncurry mid) (n , *) m
  γ (α₁ , β₁) (α₂ , β₂) (α≈ , β≈) =
      aux-continuous n (α₁ , β₁) (α₂ , β₂)
          (𝟛→ℤ (head α₁) +ℤ 𝟛→ℤ (head β₁))
          (𝟛→ℤ (head α₂) +ℤ 𝟛→ℤ (head β₂))
          (ap (λ ■ → 𝟛→ℤ ■ +ℤ 𝟛→ℤ (head β₁)) (α≈ 0 *)
          ∙ ap (λ ■ → 𝟛→ℤ (head α₂) +ℤ 𝟛→ℤ ■) (β≈ 0 *))
          (α≈ , β≈)

⊕-continuous : continuous² (×* 𝕀* 𝕀*) 𝕀* (uncurry _⊕_)
⊕-continuous = mid-continuous

-- Sum operator adds a finite vector of 𝕀 numbers
sum : (n : ℕ) → ST-Type (𝕍* 𝕀* n) → 𝕀
sum 0 = id
sum (succ n) (r , rs) = r ⊕ (sum n rs)

-- Continuity of the sum operator
id-continuous : (st : ST) → continuous² st st id
id-continuous st n = n , (λ _ _ → id)

sum-continuous : ∀ d → continuous² (𝕍* 𝕀* d) 𝕀* (sum d)
sum-continuous 0 = id-continuous 𝕀*
sum-continuous (succ d) (n , *) = m , γ where
  IH = sum-continuous d (succ n , *)
  m : ST-Moduli (𝕍* 𝕀* (succ d))
  m = (succ n , *) , pr₁ IH
  γ : (α β : ST-Type (𝕍* 𝕀* (succ d)))
        → ST-≈ (𝕍* 𝕀* (succ d)) α β m
        → ST-≈ 𝕀* (sum (succ d) α) (sum (succ d) β) (n , *)
  γ (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂) = pr₂ (⊕-continuous (n , *))
                                                             (α₁ , sum d α₂) (β₁ , sum d β₂)
                                                             (α≈β₁ , pr₂ IH α₂ β₂ α≈β₂)

-- Negation operator
-b : 𝟛 → 𝟛
-b ₋₁ = ₁
-b   ₀ = ₀
-b   ₁ = ₋₁

-_ : 𝕀 → 𝕀
(- x) n = -b (x n)

-- Continuity of the negation operator
neg-continuous : continuous² 𝕀* 𝕀* (-_)
neg-continuous (n , *) = (n , *) , γ where
  γ : (α β : 𝕀) → (α ≈ β) n → ((- α) ≈ (- β)) n
  γ α β α≈β k k<n = lem (α k) (β k) (α≈β k k<n) where
    lem : (b₁ b₂ : 𝟛) → b₁ ≡ b₂ → (-b b₁) ≡ (-b b₂)
    lem ₋₁ ₋₁ refl = refl
    lem   ₀   ₀ refl = refl
    lem   ₁   ₁ refl = refl

-- Minus operator
_⊖_ : 𝕀 → 𝕀 → 𝕀
x ⊖ y = x ⊕ (- y)

-- Continuity of the minus operator
⊖-continuous : continuous² (×* 𝕀* 𝕀*) 𝕀* (uncurry _⊖_)
⊖-continuous n = m , γ where
  m : ST-Moduli (×* 𝕀* 𝕀*)
  m = (pr₁ (pr₁ (⊕-continuous n))) , pr₁ (neg-continuous (pr₂ (pr₁ (⊕-continuous n))))
  γ : uc-mod² (×* 𝕀* 𝕀*) 𝕀* (uncurry _⊖_) n m
  γ (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂) =
                   pr₂ (⊕-continuous n) (α₁ , - α₂) (β₁ , - β₂) (α≈β₁ ,
                   pr₂ (neg-continuous (pr₂ (pr₁ (⊕-continuous n)))) α₂ β₂ α≈β₂)

