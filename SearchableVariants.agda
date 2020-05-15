{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (𝟚;₀;₁)
open import SearchableTypes
open import DecidableAndDetachable

module SearchableVariants where

quantify-condition : (st : ST) → searcher st → 𝓤₁ ̇
quantify-condition st 𝓔 = (p : ST-Type st → 𝓤₀ ̇) (d : detachable p) (c : continuous st p)
                                           → (p (𝓔 p d c) → Π p)

continuously-quantifiable : (st : ST) → (𝓤₀ ⁺) ̇
continuously-quantifiable st = Σ \(𝓔 : searcher st) → quantify-condition st 𝓔

¬det : (st : ST) (p : ST-Type st → 𝓤₀ ̇) → detachable p → detachable (λ x → ¬ p x)
¬det st p d x = Cases (d x) (λ z → inr (λ x → x z)) inl

¬con : (st : ST) (p : ST-Type st → 𝓤₀ ̇) → continuous st p → continuous st (λ x → ¬ p x )
¬con st p (m , ϕ) = m , (λ α β α≈β → (λ x x₁ → x (pr₂ (ϕ α β α≈β) x₁)) , (λ x x₁ → x (pr₁ (ϕ α β α≈β) x₁)))


search-condition₂ : (st : ST) → (𝓔 : searcher st) → 𝓤₁ ̇
search-condition₂ st 𝓔 = (p : ST-Type st → 𝓤₀ ̇) → (d : detachable p) (c : continuous st p)
                                       → ¬ p (𝓔 p d c) → ¬ Σ p

s₁→s₂ : (st : ST) → (𝓔 : searcher st) → search-condition st 𝓔 → search-condition₂ st 𝓔
s₁→s₂ st 𝓔 S p d c ¬p𝓔pdc Σp = ¬p𝓔pdc (S p d c Σp)

s→q : ∀ st → (𝓔,C,S : continuously-searchable st) → continuously-quantifiable st
pr₁ (s→q st (𝓔 , _ , S)) p d c = 𝓔 (λ x → ¬ p x) (¬det st p d) (¬con st p c)
pr₂ (s→q st (𝓔 , _ , S)) p d c p𝓔 = A (S₂ (λ x → ¬ p x) (¬det st p d) (¬con st p c) (λ ¬p𝓔pdc → ¬p𝓔pdc p𝓔)) where
  A : ¬ (Σ \x → ¬ p x) → Π p
  A  ¬Σ¬p x = Cases (d x) id (λ ¬px → 𝟘-elim (¬Σ¬p (x , ¬px)))
  S₂ : search-condition₂ st 𝓔
  S₂ = s₁→s₂ st 𝓔 S

Π-decidable : (st : ST) (p : ST-Type st → 𝓤₀ ̇) → detachable p → continuous st p → decidable (Π p)
Π-decidable st p d c = Cases (d x₀)
                           (λ p𝓔 → inl (pr₂ (s→q st (𝓔 , C,S)) p d c p𝓔))
                           (λ ¬p𝓔 → inr (λ Πp → ¬p𝓔 (Πp x₀)))
 where
  𝓔 = pr₁ (all-ST-searchable st)
  C,S = pr₂ (all-ST-searchable st)
  x₀ : ST-Type st
  x₀ = 𝓔 (λ x → ¬ p x) (¬det st p d) (¬con st p c)
