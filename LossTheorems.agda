{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (𝟚;₀;₁)
open import SearchableTypes
open import UIOrder
open import TheoremsBase

module LossTheorems where

imperfect-theorem-with-Φ : {st st₁ st₂ : ST}
                              → (ε : 𝕌) (m : ℕ)
                              → (Φ : Y st₁ st₂ → Y st₁ st₂ → 𝕌)
                              → (cᴸ : continuousᴸ st₁ st₂ Φ)
                              → Σ \(reg : regressor st st₁ st₂)
                              → (M : ST-Type st → Y st₁ st₂)
                              → (cᴹ : continuousᴹ st st₁ st₂ M)
                              → (Ψ : Y st₁ st₂ → Y st₁ st₂)
                              → (k : ST-Type st)
                              → let
                                  Ω = M k
                                  ΨΩ = Ψ Ω
                                  ω = M (reg M cᴹ ΨΩ)
                                  in (Φ ΨΩ Ω <ᵁ ε) m → (Φ ΨΩ ω <ᵁ ε) m
imperfect-theorem-with-Φ {st} {st₁} {st₂} ε m Φ cᴸ = reg , γ where
  X = ST-Type st
  𝓔 = pr₁ (all-ST-searchable st)
  S = pr₂ (pr₂ (all-ST-searchable st))
  d : (Ω : Y st₁ st₂) (M : X → Y st₁ st₂) (x : X) → decidable ((Φ Ω (M x) <ᵁ ε) m)
  d Ω M x = <ᵁ-decidable (Φ Ω (M x)) ε m
  c : (Ω : Y st₁ st₂) (M : X → Y st₁ st₂) → continuousᴹ st st₁ st₂ M → continuous st (λ x → (Φ Ω (M x) <ᵁ ε) m)
  c Ω M cᴹ = m' , c' where
    m' : ST-Moduli st
    m' = pr₁ (cᴹ (pr₁ (cᴸ (pr₁ (<ᵁ-continuous₁ ε m)))))
    c' : (α β : ST-Type st) → ST-≈ st α β m' → (Φ Ω (M α) <ᵁ ε) m ⇔ (Φ Ω (M β) <ᵁ ε) m
    c' α β α≈β = pr₂ (<ᵁ-continuous₁ ε m) (Φ Ω (M α)) (Φ Ω (M β))
                                (pr₂ (cᴸ (pr₁ (<ᵁ-continuous₁ ε m))) (M α) (M β)
                                     (pr₂ (cᴹ (pr₁ (cᴸ (pr₁ (<ᵁ-continuous₁ ε m))))) α β α≈β) Ω)
  reg : regressor st st₁ st₂
  reg M cᴹ ΨΩ = 𝓔 (λ x → (Φ ΨΩ (M x) <ᵁ ε) m) (d ΨΩ M) (c ΨΩ M cᴹ)
  γ : (M : ST-Type st → Y st₁ st₂) (cᴹ : continuousᴹ st st₁ st₂ M)
     → (Ψ : Y st₁ st₂ → Y st₁ st₂) (k : ST-Type st)
     → (Φ (Ψ (M k)) (M k) <ᵁ ε) m → (Φ (Ψ (M k)) (M (reg M cᴹ (Ψ (M k)))) <ᵁ ε) m
  γ M cᴹ Ψ k Ωε = S (λ x → (Φ (Ψ (M k)) (M x) <ᵁ ε) m) (d (Ψ (M k)) M) (c (Ψ (M k)) M cᴹ) (k , Ωε)


vanishing-loss : (st₁ st₂ : ST) → (Φ : Y st₁ st₂ → Y st₁ st₂ → 𝕌) → 𝓤₀ ̇
vanishing-loss st₁ st₂ Φ = ∀ (f : Y st₁ st₂) → 0₂ ∼ Φ f f

perfect-theorem : {st st₁ st₂ : ST}
                              → (ε : 𝕌) (m : ℕ)
                              → (Φ : Y st₁ st₂ → Y st₁ st₂ → 𝕌)
                              → (cᴸ : continuousᴸ st₁ st₂ Φ)
                              → Σ \(reg : regressor st st₁ st₂)
                              → vanishing-loss st₁ st₂ Φ
                              → (M : ST-Type st → Y st₁ st₂)
                              → (cᴹ : continuousᴹ st st₁ st₂ M)
                              → (k : ST-Type st)
                              → let
                                  Ω = M k
                                  ω = M (reg M cᴹ Ω)
                                  in (0₂ <ᵁ ε) m → (Φ Ω ω <ᵁ ε) m
perfect-theorem {st} {st₁} {st₂} ε m Φ cᴸ = reg , γ where
    theorem = imperfect-theorem-with-Φ {st} {st₁} {st₂} ε m Φ cᴸ
    reg : regressor st st₁ st₂
    reg = pr₁ theorem
    γ : vanishing-loss st₁ st₂ Φ
         → (M : ST-Type st → Y st₁ st₂) (cᴹ : continuousᴹ st st₁ st₂ M) (k : ST-Type st)
         → (0₂ <ᵁ ε) m → (Φ (M k) (M (reg M cᴹ (M k))) <ᵁ ε) m
    γ vᴸ M cᴹ k 0<ε = pr₂ theorem M cᴹ id k
                                 (pr₁ (pr₂ (<ᵁ-continuous₁ ε m) 0₂ (Φ (M k) (M k)) (λ n _ → vᴸ (M k) n)) 0<ε)
