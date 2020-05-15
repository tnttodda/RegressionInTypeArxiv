{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (𝟚;₀;₁)
open import Prelude renaming (₀ to ⁰ ; ₁ to ¹)
open import SearchableTypes
open import UIOrder
open import TheoremsBase
open import DecidableAndDetachable
open import SearchableVariants

module FunEquivTheorem where

ST-≈ᶠ-dec : (st₁ st₂ : ST) (n : ST-Moduli st₂)
                   (f g : Y st₁ st₂) (cᶠ : continuous² st₁ st₂ f) (cᵍ : continuous² st₁ st₂ g)
                  → decidable (ST-≈ᶠ st₁ st₂ f g n)
ST-≈ᶠ-dec st₁ st₂ n f g cᶠ cᵍ = Π-decidable st₁ p d c where
  p = λ x → ST-≈ st₂ (f x) (g x) n
  d = λ x → ST-≈-dec st₂ (f x) (g x) n
  c = ST-≈-f-con st₁ st₂ n f g cᶠ cᵍ

ST-≈ᶠ-con : (st st₁ st₂ : ST) (m : ST-Moduli st₂) (Ω : Y st₁ st₂) (M : ST-Type st → Y st₁ st₂)
                 → continuous² (×* st st₁) st₂ (uncurry M) → continuous st (λ x → ST-≈ᶠ st₁ st₂ Ω (M x) m)
ST-≈ᶠ-con st st₁ st₂ m Ω M cᴹ = pr₁ (pr₁ (cᴹ m))
                                                  , (λ α β α≈β → γ α β α≈β , γ β α (ST-≈-sym st (pr₁ (pr₁ (cᴹ m))) α β α≈β)) where
  γ : (α β : ST-Type st) → ST-≈ st α β (pr₁ (pr₁ (cᴹ m))) → ST-≈ᶠ st₁ st₂ Ω (M α) m → ST-≈ᶠ st₁ st₂ Ω (M β) m
  γ α β α≈β ≈ᶠ x = ST-≈-trans st₂ m (Ω x) (M α x) (M β x)
                               (≈ᶠ x) (pr₂ (cᴹ m) (α , x) (β , x) (α≈β , (ST-≈-refl st₁ (pr₂ (pr₁ (cᴹ m))) x)))

continuousᴰ : (st₁ st₂ : ST) → (Y st₁ st₂ → Y st₁ st₂) → 𝓤₀ ̇
continuousᴰ st₁ st₂ Ψ = (f : Y st₁ st₂) → (n : ST-Moduli st₂)
                                    → Σ \(m : ST-Moduli st₁) → (α β : ST-Type st₁) → ST-≈ st₁ α β m
                                    → ST-≈ st₂ (Ψ f α) (Ψ f β) n
                                    
imperfect-theorem-with-≈ : {st st₁ st₂ : ST}
                              → ∀ (m : ST-Moduli st₂)
                              → Σ \(reg : regressor-strong st st₁ st₂)
                              → (M : ST-Type st → Y st₁ st₂)
                              → (cᴹ : continuous² (×* st st₁) st₂ (uncurry M))
                              → (Ψ : Y st₁ st₂ → Y st₁ st₂)
                              → (cᴰ : continuousᴰ st₁ st₂ Ψ)
                              → (k : ST-Type st)
                              → let
                                  Ω = M k
                                  ΨΩ = Ψ Ω
                                  ω = M (reg M cᴹ ΨΩ (cᴰ (M k)))
                                  in ST-≈ᶠ st₁ st₂ Ω ΨΩ m
                                  → ST-≈ᶠ st₁ st₂ Ω ω m
imperfect-theorem-with-≈ {st} {st₁} {st₂} m = reg , γ where
  X = ST-Type st
  𝓔 = pr₁ (all-ST-searchable st)
  S = pr₂ (pr₂ (all-ST-searchable st))
  d : (Ω : Y st₁ st₂) (M : X → Y st₁ st₂) → continuous² st₁ st₂ Ω → continuous² (×* st st₁) st₂ (uncurry M)
      → detachable (λ x → ST-≈ᶠ st₁ st₂ Ω (M x) m)
  d Ω M cᴼ cᴹ³ x = ST-≈ᶠ-dec st₁ st₂ m Ω (M x) cᴼ γ₂ where
    γ₂ : (n : ST-Moduli st₂) → Σ (uc-mod² st₁ st₂ (M x) n)
    γ₂ n = (pr₂ (pr₁ (cᴹ³ n))) , λ α β α≈β → pr₂ (cᴹ³ n) (x , α) (x , β) ((ST-≈-refl st (pr₁ (pr₁ (cᴹ³ n))) x) , α≈β)
  c : (Ω : Y st₁ st₂) (M : ST-Type st → Y st₁ st₂) → continuous² (×* st st₁) st₂ (uncurry M)
     → continuous st (λ x → ST-≈ᶠ st₁ st₂ Ω (M x) m)
  c = ST-≈ᶠ-con st st₁ st₂ m 
  reg : regressor-strong st st₁ st₂
  reg M cᴹ ΨΩ cᴼ = 𝓔 (λ x → ST-≈ᶠ st₁ st₂ ΨΩ (M x) m)
                                  (d ΨΩ M cᴼ cᴹ) (ST-≈ᶠ-con st st₁ st₂ m ΨΩ M cᴹ)
  γ : (M : ST-Type st → Y st₁ st₂)
        (cᴹ : continuous² (×* st st₁) st₂ (uncurry M))
        (Ψ : Y st₁ st₂ → Y st₁ st₂) (cᴰ : continuousᴰ st₁ st₂ Ψ)
        (k : ST-Type st) →
        ST-≈ᶠ st₁ st₂ (M k) (Ψ (M k)) m →
        ST-≈ᶠ st₁ st₂ (M k) (M (reg M cᴹ (Ψ (M k)) (cᴰ (M k)))) m
  γ M cᴹ Ψ cᴰ k ≈ᶠ x = ST-≈-trans st₂ m ((M k) x) (Ψ (M k) x) (M (reg M cᴹ (Ψ (M k)) (cᴰ (M k))) x)
                               (≈ᶠ x)
                               ((S (λ y → ST-≈ᶠ st₁ st₂ (Ψ (M k)) (M y) m)
                                     (d (Ψ (M k)) M (cᴰ (M k)) cᴹ) (ST-≈ᶠ-con st st₁ st₂ m (Ψ (M k)) M cᴹ)
                                     (k , (λ x₁ → ST-≈-sym st₂ m (M k x₁) (Ψ (M k) x₁) (≈ᶠ x₁))) x))

imperfect-corollary-with-≈ : {st st₁ st₂ : ST}
                              → ∀ (m : ST-Moduli 𝕌*)
                              → (Φ : Y st₁ st₂ → Y st₁ st₂ → 𝕌)
                              → (cᴸ : continuousᴸ st₁ st₂ Φ)
                              → Σ \(reg : regressor-strong st st₁ st₂)
                              → (M : ST-Type st → Y st₁ st₂)
                              → (cᴹ : continuous² (×* st st₁) st₂ (uncurry M))
                              → (Ψ : Y st₁ st₂ → Y st₁ st₂)
                              → (cᴰ : continuousᴰ st₁ st₂ Ψ)
                              → (k : ST-Type st)
                              → let
                                  Ω = M k
                                  ΨΩ = Ψ Ω
                                  ω = M (reg M cᴹ ΨΩ (cᴰ (M k)))
                                  in ST-≈ᶠ st₁ st₂ Ω ΨΩ (pr₁ (cᴸ m))
                                  → ST-≈ 𝕌* (Φ Ω ΨΩ) (Φ Ω ω) m
imperfect-corollary-with-≈ {st} {st₁} {st₂} m Φ cᴸ = reg , γ where
  reg = pr₁ (imperfect-theorem-with-≈ (pr₁ (cᴸ m)))
  γ : (M : ST-Type st → Y st₁ st₂)
        (cᴹ : continuous² (×* st st₁) st₂ (uncurry M))
        (Ψ : Y st₁ st₂ → Y st₁ st₂) (cᴰ : continuousᴰ st₁ st₂ Ψ)
        (k : ST-Type st) →
        ST-≈ᶠ st₁ st₂ (M k) (Ψ (M k)) (pr₁ (cᴸ m)) →
        ST-≈ 𝕌* (Φ (M k) (Ψ (M k)))
        (Φ (M k) (M (reg M cᴹ (Ψ (M k)) (cᴰ (M k))))) m
  γ M cᴹ Ψ cᴰ k Ω≈ΨΩ = pr₂ (cᴸ m) ΨΩ ω step₃ Ω where
    Ω = M k
    ΨΩ = Ψ Ω
    ω = M (reg M cᴹ ΨΩ (cᴰ (M k)))
    step₁ : ST-≈ᶠ st₁ st₂ ΨΩ Ω (pr₁ (cᴸ m))
    step₁ x = ST-≈-sym st₂ (pr₁ (cᴸ m)) (Ω x) (ΨΩ x) (Ω≈ΨΩ x)
    step₂ : ST-≈ᶠ st₁ st₂ Ω ω (pr₁ (cᴸ m))
    step₂ = pr₂ (imperfect-theorem-with-≈ (pr₁ (cᴸ m))) M cᴹ Ψ cᴰ k Ω≈ΨΩ
    step₃ : ST-≈ᶠ st₁ st₂ ΨΩ ω (pr₁ (cᴸ m))
    step₃ x = ST-≈-trans st₂ (pr₁ (cᴸ m)) (ΨΩ x) (Ω x) (ω x) (step₁ x) (step₂ x)
