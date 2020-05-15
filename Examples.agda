{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (𝟚;₀;₁)
open import InfSequence
open import Prelude
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import SearchableTypes
open import NaturalsOrder
open import UIOrder
open import DecidableAndDetachable
open import TheoremsBase
open import IAddition
open import IMultiplication
open import LossTheorems
 
module Examples where

{- (1) Defining the LSE-style loss function -}

-- The map operator maps a function onto a vector of one-or-more constructions of an S-Type
map : (st₁ st₂ : ST) → (n : ℕ) → (ST-Type st₁ → ST-Type st₂) → ST-Type (𝕍* st₁ n) → ST-Type (𝕍* st₂ n)
map st₁ st₂ zero f x = f x
map st₁ st₂ (succ n) f (x , xs) = f x , map st₁ st₂ n f xs

𝟛→𝟚 : 𝟛 → 𝟚
𝟛→𝟚 ₋₁ = ⁰
𝟛→𝟚  ₀ = ⁰
𝟛→𝟚  ₁ = ¹

-- The 𝕀→𝕌 operator computes a 'normalised' representation from a code in 𝕀, returning one in 𝕌
𝕀→𝕌 : 𝕀 → 𝕌
𝕀→𝕌 r n = 𝟛→𝟚 (r n)

-- The least-squares error style loss function takes two functions f,g : 𝕀 → 𝕀 and
-- maps the function (λ x → f x ⊖ gx) ² onto a vector of one-or-more 𝕀-values.
-- The closer the outputs of each function with the same input, the smaller the loss value produced
LSE₁ : (d : ℕ) → ST-Type (𝕍* 𝕀* d) → (𝕀 → 𝕀) → (𝕀 → 𝕀) → 𝕀
LSE₁ d xs f g = sum d (map 𝕀* 𝕀* d (λ x → (f x ⊖ g x) ²) xs)

LSE : (d : ℕ) → ST-Type (𝕍* 𝕀* d) → (𝕀 → 𝕀) → (𝕀 → 𝕀) → 𝕌
LSE d xs f g = 𝕀→𝕌 (LSE₁ d xs f g)

{- (2) Showing the LSE operator satisfies the loss continuity condition  -}

-- This gives takes a vector of precision points in the exactness type of a vector of one-or-more constructions
-- of an S-Type and gives back the maximum precision point
max-mod-vec : (st : ST) (d : ℕ) → ST-Moduli (𝕍* st d) → ST-Moduli st
max-mod-vec st zero v = v
max-mod-vec st (succ d) (v , vs) = max-mod st v (max-mod-vec st d vs)

-- If two functions are equal at the maximum of a vector of two-or-more precision points, then they are
-- equal at the next point in the vector
ST-≈-max-fun : (st₁ st₂ : ST) (d : ℕ) (n : ST-Moduli (𝕍* st₂ (succ d)))
                         → (f g : Y st₁ st₂)
                         → ST-≈ᶠ st₁ st₂ f g (max-mod-vec st₂ (succ d) n)
                         → ST-≈ᶠ st₁ st₂ f g (max-mod-vec st₂ d (pr₂ n))
ST-≈-max-fun st₁ st₂ d (n , ns) f g f≈g x = pr₂ (ST-≈-max st₂ (f x) (g x) n (max-mod-vec st₂ d ns) (f≈g x))

-- This shows that for all precisions n in the exactness type of (𝕍* st d), there exists a precision m such that
-- the mapping of functions f and g that are equal with precision m onto the same vector of d+1 constructions
-- of the S-Type st results in vectors of the same size that are equivalent modulo n
map-≈ : (st : ST) (d : ℕ) (xs : ST-Type (𝕍* st d)) → Π \(n : ST-Moduli (𝕍* st d))
                 → Σ \m → (f g : Y st st) → ST-≈ᶠ st st f g m 
                 → ST-≈ (𝕍* st d) (map st st d f xs) (map st st d g xs) n
map-≈ st d xs n = max-mod-vec st d n , γ d xs n where
  γ : (d : ℕ) (xs : ST-Type (𝕍* st d)) (n : ST-Moduli (𝕍* st d))
        → (f g : Y st st) → ST-≈ᶠ st st f g (max-mod-vec st d n)
        → ST-≈ (𝕍* st d) (map st st d f xs) (map st st d g xs) n
  γ zero r n f g f≈g = f≈g r
  γ (succ d) (r , xs) (n , ns) f g f≈g = pr₁ (ST-≈-max st (f r) (g r) n (max-mod-vec st d ns) (f≈g r))
                                                       , γ d xs ns f g (ST-≈-max-fun st st d (n , ns) f g f≈g)

-- It is trivial to show that 𝕀→𝕌 is continuous
𝕀→𝕌-continuous : continuous² 𝕀* 𝕌* 𝕀→𝕌
𝕀→𝕌-continuous m = m , (λ α β α≈β n n<m → 𝟛→𝟚≡ (α n) (β n) (α≈β n n<m)) where
  𝟛→𝟚≡ : (a b : 𝟛) → a ≡ b → 𝟛→𝟚 a ≡ 𝟛→𝟚 b
  𝟛→𝟚≡ a .a refl = refl

-- All its constituent functions are continuous, so it is simple to show that LSE is continuous
LSE-continuous : (d : ℕ) (xs : ST-Type (𝕍* 𝕀* d)) → continuousᴸ 𝕀* 𝕀* (LSE d xs)
LSE-continuous d xs m = pr₂ m₅ , γ where
  m₁ = pr₁ (𝕀→𝕌-continuous m)
  m₂ = pr₁ (sum-continuous d m₁)
  m₃ = pr₁ (map-≈ 𝕀* d xs m₂)
  m₄ = pr₁ (sq-continuous m₃)
  m₅ = pr₁ (⊖-continuous m₄)
  γ : (g h : 𝕀 → 𝕀) → ST-≈ᶠ 𝕀* 𝕀* g h (pr₂ m₅) → ∀ f → ST-≈ 𝕌* (𝕀→𝕌 (LSE₁ d xs f g)) (𝕀→𝕌 (LSE₁ d xs f h)) m
  γ g h g≈h f
           = pr₂ (𝕀→𝕌-continuous m) (LSE₁ d xs f g) (LSE₁ d xs f h)
              (pr₂ (sum-continuous d m₁) (map 𝕀* 𝕀* d (λ x → (f x ⊖ g x) ²) xs)
                                                            (map 𝕀* 𝕀* d (λ x → (f x ⊖ h x) ²) xs)
               (pr₂ (map-≈ 𝕀* d xs (pr₁ (sum-continuous d m₁))) (λ x → (f x ⊖ g x) ²) (λ x → (f x ⊖ h x) ²)
               λ x → pr₂ (sq-continuous m₃) (f x ⊖ g x) (f x ⊖ h x)
                        (pr₂ (⊖-continuous m₄) (f x , g x) (f x , h x) (ST-≈-refl 𝕀* (pr₁ m₅) (f x) , g≈h x))))

{- (3) For our example, we will use a linear model with two unknown parameters -}

linear-model : (αβ : 𝕀 × 𝕀) → 𝕀 → 𝕀
linear-model (α , β) x = (α *𝕀 x) ⊕ β

linear-model-continuous : continuousᴹ (×* 𝕀* 𝕀*) 𝕀* 𝕀* linear-model
linear-model-continuous n = m , γ where
  m : ST-Moduli (×* 𝕀* 𝕀*)
  m = pr₁ (pr₁ (*𝕀-continuous (pr₁ (pr₁ (⊕-continuous n))))) , pr₂ (pr₁ (⊕-continuous n))
  γ : (α β : ST-Type (×* 𝕀* 𝕀*)) → ST-≈ (×* 𝕀* 𝕀*) α β m
        → ST-≈ᶠ (𝕍* 𝕀* 0) (𝕍* 𝕀* 0) (λ x → (pr₁ α *𝕀 x) ⊕ pr₂ α) (λ x → (pr₁ β *𝕀 x) ⊕ pr₂ β) n
  γ (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂) δ
    = pr₂ (⊕-continuous n) (α₁ *𝕀 δ , α₂) (β₁ *𝕀 δ , β₂)
              (pr₂ (*𝕀-continuous (pr₁ (pr₁ (⊕-continuous n)))) (α₁ , δ) (β₁ , δ)
              (α≈β₁ , (ST-≈-refl 𝕀* (pr₂ (pr₁ (*𝕀-continuous (pr₁ (pr₁ (mid-continuous n)))))) δ)) , α≈β₂)

{- (4) Our example interpolates an unknown oracle using constant interpolation -}

-- A vector of 'inputs' xs (of size 2+) is given for a function (𝕀* → 𝕀*). This function is interpolated to give a
-- function where on input of x, the output is a mid-point of two values in xs. x is mapped to a mid-point
-- of x₀ and x₁ if it is between these two values, relative to some precision m
constant-interpolation : (m : ℕ) (d : ℕ) (xs : ST-Type (𝕍* 𝕀* (succ d))) → Y 𝕀* 𝕀* → Y 𝕀* 𝕀*
constant-interpolation m zero (x₀ , x₁) Ω _ = mid (Ω x₀) (Ω x₁)
constant-interpolation m (succ d) (x₀ , (x₁ , xs)) Ω x = if (<ᴵ-decidable x x₁ m)
                                                                                          then mid (Ω x₀) (Ω x₁)
                                                                                          else constant-interpolation m d (x₁ , xs) Ω x

-- The loss function in offline-regression is LSE, with the input of the same mid-points as mapped to in
-- the above constant-interpolation function. Therefore, we define the following 'mid-points' function
mid-points : (d : ℕ) → ST-Type (𝕍* 𝕀* (succ d)) → ST-Type (𝕍* 𝕀* d)
mid-points zero (x₀ , x₁) = mid x₀ x₁
mid-points (succ d) (x₀ , x₁ , xs) = mid x₀ x₁ , mid-points d (x₁ , xs)

offline-regression-Ψ : (st : ST) (ε : 𝕌) (m : ℕ) (d : ℕ) (xs : ST-Type (𝕍* 𝕀* (succ d)))
                                       → (Ψ : Y 𝕀* 𝕀* → Y 𝕀* 𝕀*)
                                       → Σ (λ (reg : regressor st 𝕀* 𝕀*)
                                       → (M : ST-Type st → Y 𝕀* 𝕀*) (cᴹ : continuousᴹ st 𝕀* 𝕀* M)
                                       → (k : ST-Type st)
                                       → let Φ = LSE d (mid-points d xs) in
                                           let Ω = M k in
                                           let ΨΩ = Ψ Ω in
                                           let ω = M (reg M cᴹ ΨΩ) in
                                       (Φ ΨΩ Ω <ᵁ ε) m → (Φ ΨΩ ω <ᵁ ε) m)
offline-regression-Ψ st ε m d xs Ψ = reg , γ where
  th = imperfect-theorem-with-Φ {st} {𝕀*} {𝕀*} ε m (LSE d (mid-points d xs)) (LSE-continuous d (mid-points d xs)) 
  reg : regressor st 𝕀* 𝕀*
  reg = pr₁ th
  γ : (M : ST-Type st → Y 𝕀* 𝕀*) (cᴹ : continuousᴹ st 𝕀* 𝕀* M)
        (k : ST-Type st) →
        let Φ = LSE d (mid-points d xs) in
        (Φ (Ψ (M k)) (M k) <ᵁ ε) m → (Φ (Ψ (M k)) (M (reg M cᴹ (Ψ (M k)))) <ᵁ ε) m
  γ M cᴹ k Φ<ε = pr₂ th M cᴹ Ψ k Φ<ε

-- The following uses the imperfect-lossy-theorem to construct a regressor for offline regression as described
-- in the paper. This regressor can construct a parameter for a given continuous model that gets the loss
-- below a given epsilon, under the assumption that the loss between the true oracle and the interpolation
-- is below this epsilon. The point used for the loss function are the mid-points of the xs as defined above
offline-regression : (st : ST) (ε : 𝕌) (m : ℕ) (d : ℕ) (xs : ST-Type (𝕍* 𝕀* (succ d)))
                                 → Σ (λ (reg : regressor st 𝕀* 𝕀*)
                                 → (M : ST-Type st → Y 𝕀* 𝕀*) (cᴹ : continuousᴹ st 𝕀* 𝕀* M)
                                 → (k : ST-Type st) →
                                 let Ω = M k in
                                 let Φ = LSE d (mid-points d xs) in
                                 let Ψ = constant-interpolation m d xs in
                                 let ΨΩ = Ψ Ω in
                                 let ω = M (reg M cᴹ ΨΩ) in
                                 (Φ ΨΩ Ω <ᵁ ε) m → (Φ ΨΩ ω <ᵁ ε) m)
offline-regression st ε m d xs = offline-regression-Ψ st ε m d xs (constant-interpolation m d xs)

{- (4) Using the linear model, we can specialise the above theorem -}

offline-regression-ΨM : (st : ST) (ε : 𝕌) (m : ℕ) (d : ℕ) (xs : ST-Type (𝕍* 𝕀* (succ d)))
                                       → (M : ST-Type st → Y 𝕀* 𝕀*) (cᴹ : continuousᴹ st 𝕀* 𝕀* M) (Ψ : Y 𝕀* 𝕀* → Y 𝕀* 𝕀*)
                                       → Σ (λ (reg : regressor st 𝕀* 𝕀*)
                                       → (k : ST-Type st)
                                       → let Φ = LSE d (mid-points d xs) in
                                       (Φ (Ψ (M k)) (M k) <ᵁ ε) m → (Φ (Ψ (M k)) (M (reg M cᴹ (Ψ (M k)))) <ᵁ ε) m)
offline-regression-ΨM st ε m d xs M cᴹ Ψ = reg , γ where
  th = imperfect-theorem-with-Φ {st} {𝕀*} {𝕀*} ε m (LSE d (mid-points d xs)) (LSE-continuous d (mid-points d xs)) 
  reg : regressor st 𝕀* 𝕀*
  reg = pr₁ th
  γ : (k : ST-Type st) →
        let Φ = LSE d (mid-points d xs) in
        (Φ (Ψ (M k)) (M k) <ᵁ ε) m →
        (Φ (Ψ (M k)) (M (reg M cᴹ (Ψ (M k)))) <ᵁ ε) m
  γ k Φ<ε = pr₂ th M cᴹ Ψ k Φ<ε

linear-offline-regression : (ε : 𝕌) (m : ℕ) (d : ℕ) (xs : ST-Type (𝕍* 𝕀* (succ d)))
                                           → Σ (λ (reg : regressor (×* 𝕀* 𝕀*) 𝕀* 𝕀*)
                                           → (k : 𝕀 × 𝕀) →
                                           let M = linear-model in
                                           let Ω = M k in
                                           let Φ = LSE d (mid-points d xs) in
                                           let Ψ = constant-interpolation m d xs in
                                           let ΨΩ = Ψ Ω in
                                           let ω = M (reg linear-model linear-model-continuous ΨΩ) in
                                           (Φ ΨΩ Ω <ᵁ ε) m → (Φ ΨΩ ω <ᵁ ε) m)
linear-offline-regression ε m d xs = offline-regression-ΨM (×* 𝕀* 𝕀*) ε m d xs
                                                           linear-model linear-model-continuous (constant-interpolation m d xs)
