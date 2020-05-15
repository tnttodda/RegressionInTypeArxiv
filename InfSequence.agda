{-# OPTIONS --without-K --exact-split --safe #-}

module InfSequence where

open import SpartanMLTT
open import NaturalsOrder
open import Prelude

-- Infinitary sequences
𝕊 : 𝓤 ̇ → 𝓤 ̇
𝕊 X = ℕ → X

-- Get the leading element of a sequence
head : {X : 𝓤 ̇} → 𝕊 X → X
head s = s 0

-- Get the trailing sequence of a sequence
tail : {X : 𝓤 ̇} → 𝕊 X → 𝕊 X
tail s n = s (succ n)

-- Compose an element and sequence to make a sequence
_::_ : {X : 𝓤 ̇} → X → 𝕊 X → 𝕊 X
(h :: t) 0 = h
(h :: t) (succ n) = t n

-- Equality up to a point for arbitrary sequences
-- If X is finite and has ST signature , _≈_ corresponds to ST-≈ for the ST type with signature (→* st)
_≈_ : {X : 𝓤 ̇} → (α β : 𝕊 X) → ℕ → 𝓤 ̇
(α ≈ β) m = (n : ℕ) → n < m → α n ≡ β n

-- This equality is reflexive, transitive and symmetric
≈-refl : {X : 𝓤 ̇} → (α : 𝕊 X) (m : ℕ) → (α ≈ α) m
≈-refl α m n n<m = refl

≈-trans : {X : 𝓤 ̇} → (α β γ : 𝕊 X) (m : ℕ) → (α ≈ β) m → (β ≈ γ) m → (α ≈ γ) m
≈-trans α β γ m α≈β β≈γ n n<m = α≈β n n<m ∙ β≈γ n n<m

≈-sym : {X : 𝓤 ̇} → (α β : 𝕊 X) (m : ℕ) → (α ≈ β) m → (β ≈ α) m
≈-sym α β m α≈β n n<m = α≈β n n<m ⁻¹

-- If two sequences are equal up to m, they are equal up to all n < m
≈-low : {X : 𝓤 ̇} → (α β : 𝕊 X) (m : ℕ) → (α ≈ β) m → (n : ℕ) → n < m → (α ≈ β) n
≈-low α β m α≈β n n<m k k<n = α≈β k (<-trans k n m k<n n<m)

-- If two sequences are equal up to succ m, they are equal up to n
≈-pred : {X : 𝓤 ̇} → (α β : 𝕊 X) (m : ℕ) → (α ≈ β) (succ m) → (α ≈ β) m
≈-pred α β m α≈β = ≈-low α β (succ m) α≈β m (<-succ m)

-- If two sequences are equal up to m, and are equal at m, they are equal up to succ m
≈-combine : {X : 𝓤 ̇} (α β : 𝕊 X) (m : ℕ) → α m ≡ β m → (α ≈ β) m → (α ≈ β) (succ m)
≈-combine α β m αm≡βm α≈β n n<m =
                                 Cases (<-split n m n<m) (α≈β n)
                                 (λ n≡m → transport (λ ■ → α ■ ≡ β ■) (n≡m ⁻¹) αm≡βm)

-- This equality is decidable at any point
≈-decidable : {X : 𝓤 ̇} → discrete X → (α β : 𝕊 X) (m : ℕ) → decidable ((α ≈ β) m)
≈-decidable D α β 0 = inl (λ _ ())
≈-decidable D α β (succ m) = Cases (≈-decidable D α β m)
                         (Cases (D (α m) (β m))
                                 (λ z₁ z₂ → inl (≈-combine α β m z₁ z₂))
                                 (λ ¬αm≡βm _ → inr (λ α≈β → ¬αm≡βm (α≈β m (<-succ m)))))
                         (λ ¬α≈β → inr (λ α≈β → ¬α≈β (≈-pred α β m α≈β)))
