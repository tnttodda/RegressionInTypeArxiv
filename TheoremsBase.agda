{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (𝟚;₀;₁)
open import InfSequence
open import Prelude renaming (₀ to ⁰ ; ₁ to ¹)
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import SearchableTypes
open import NaturalsOrder
open import UIOrder
open import DecidableAndDetachable

module TheoremsBase where

-- Type constructor for oracle functions, given two dimension paramenters
Y : (st₁ st₂ : ST) → 𝓤₀ ̇
Y st₁ st₂ = ST-Type st₁ → ST-Type st₂

-- Equality of two functions on S-Types up to a point
ST-≈ᶠ : (st₁ st₂ : ST) → (f g : ST-Type st₁ → ST-Type st₂) → ST-Moduli st₂ → 𝓤₀ ̇
ST-≈ᶠ st₁ st₂ f g m = (x : ST-Type st₁) → ST-≈ st₂ (f x) (g x) m

-- These two definitions are very closely related, but used separately for clarity
ST-≈ᶠ² : (st₁ st₂ : ST) → (f g : ST-Type st₁ → ST-Type st₂)
              → (n : ST-Moduli st₁) (m : ST-Moduli st₂) → 𝓤₀ ̇
ST-≈ᶠ² st₁ st₂ f g n m = (x y : ST-Type st₁) → ST-≈ st₁ x y n → ST-≈ st₂ (f x) (g y) m

ST-≈ᶠ→ST-≈ᶠ² : (st₁ st₂ : ST) → (f g : ST-Type st₁ → ST-Type st₂)
                          (n : ST-Moduli st₁) (m : ST-Moduli st₂)
                          → uc-mod² st₁ st₂ f m n + uc-mod² st₁ st₂ g m n
                          → ST-≈ᶠ st₁ st₂ f g m → ST-≈ᶠ² st₁ st₂ f g n m
ST-≈ᶠ→ST-≈ᶠ² st₁ st₂ f g n m (inl ϕᶠ) f≈g x y x≈y = ST-≈-trans st₂ m (f x) (f y) (g y) (ϕᶠ x y x≈y) (f≈g y)
ST-≈ᶠ→ST-≈ᶠ² st₁ st₂ f g n m (inr ϕᵍ) f≈g x y x≈y = ST-≈-sym st₂ m (g y) (f x)
                                                                                   (ST-≈-trans st₂ m (g y) (g x) (f x)
                                                                                    (ϕᵍ y x (ST-≈-sym st₁ n x y x≈y))
                                                                                    (ST-≈-sym st₂ m (f x) (g x) (f≈g x)))

ST-≈ᶠ²→ST-≈ᶠ : (st₁ st₂ : ST) → (f g : ST-Type st₁ → ST-Type st₂)
                          (n : ST-Moduli st₁) (m : ST-Moduli st₂)
                          → ST-≈ᶠ² st₁ st₂ f g n m → ST-≈ᶠ st₁ st₂ f g m
ST-≈ᶠ²→ST-≈ᶠ st₁ st₂ f g n m f≈g x = f≈g x x (ST-≈-refl st₁ n x)

-- Weak continuity condition on the model function
continuousᴹ : (st st₁ st₂ : ST) (M : ST-Type st → Y st₁ st₂) → 𝓤₀ ̇
continuousᴹ st st₁ st₂ M
                     = ∀ (n : ST-Moduli st₂)
                     → Σ \(m : ST-Moduli st) → (α β : ST-Type st) → ST-≈ st α β m
                     → ST-≈ᶠ st₁ st₂ (M α) (M β) n

-- Of course, continuity implies weak continuity
strong→weak-continuity : (st st₁ st₂ : ST) (M : ST-Type st → Y st₁ st₂)
                                         → continuous² (×* st st₁) st₂ (uncurry M) → continuousᴹ st st₁ st₂ M
strong→weak-continuity st st₁ st₂ M cᴹ n
  = (pr₁ (pr₁ (cᴹ n))) , (λ α β α≈β x → pr₂ (cᴹ n) (α , x) (β , x) (α≈β , (ST-≈-refl st₁ (pr₂ (pr₁ (cᴹ n))) x)))

-- Continuity condition on the loss function
continuousᴸ : (st₁ st₂ : ST) → (Φ : Y st₁ st₂ → Y st₁ st₂ → 𝕌) → 𝓤₀ ̇
continuousᴸ st₁ st₂ Φ
                     = ∀ (n : ST-Moduli 𝕌*)
                     → Σ \(m : ST-Moduli st₂) → (g h : Y st₁ st₂) → ST-≈ᶠ st₁ st₂ g h m
                     → ∀ (f : Y st₁ st₂) → ST-≈ 𝕌* (Φ f g) (Φ f h) n

-- Type definition of a regressor for any S-Type, given the dimensions of the oracle function
regressor : (st st₁ st₂ : ST) → 𝓤₀ ̇
regressor st st₁ st₂ = (M : X → Y st₁ st₂) → continuousᴹ st st₁ st₂ M → Y st₁ st₂ → X
  where X = ST-Type st

regressor-strong : (st st₁ st₂ : ST) → 𝓤₀ ̇
regressor-strong st st₁ st₂ = (M : X → Y st₁ st₂) → continuous² (×* st st₁) st₂ (uncurry M)
                                           → (Ω : Y st₁ st₂) → continuous² st₁ st₂ Ω → X
  where X = ST-Type st
