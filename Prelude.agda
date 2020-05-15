{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (𝟚;₀;₁)
open import NaturalsOrder

-- Injectivity of constructors rules
inj₁ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (a b : X) → inl {𝓤} {𝓥} {X} {Y} a ≡ inl b → a ≡ b
inj₁ a .a refl = refl

inj₂ : (a b : ℕ) → succ a ≡ succ b → a ≡ b
inj₂ zero zero refl = refl
inj₂ (succ a) (succ .a) refl = refl

-- Finite types
𝔽 : ℕ → 𝓤₀ ̇
𝔽 0 = 𝟘
𝔽 1 = 𝟙
𝔽 (succ (succ n)) = 𝔽 (succ n) + 𝟙

-- Two-point and three-point types
𝟚 = 𝔽 2
𝟛 = 𝔽 3

-- Patterns for 𝟚 
pattern ⁰ = inl *
pattern ¹ = inr *

-- Patterns for 𝟛
pattern ₋₁ = inl (inl *)
pattern ₀ = inl (inr *)
pattern ₁ = inr *

-- Finite types and ℕ have decidable equality
discrete : 𝓤 ̇ → 𝓤 ̇
discrete X = (a b : X) → decidable (a ≡ b)

𝟘-discrete : discrete {𝓤} 𝟘
𝟘-discrete ()

𝟙-discrete : discrete {𝓤} 𝟙
𝟙-discrete * * = inl refl

+𝟙-preserves-discreteness : {X : 𝓤 ̇} → discrete X → discrete (_+_ {𝓤} {𝓥} X 𝟙)
+𝟙-preserves-discreteness d (inl x₁) (inl x₂) = Cases (d x₁ x₂)
                                                                            (λ x≡ → inl (ap inl x≡))
                                                                            (λ ¬x≡ → inr (λ x≡ → ¬x≡ (inj₁ x₁ x₂ x≡)))
+𝟙-preserves-discreteness d (inl x₁) (inr *) = inr (λ ())
+𝟙-preserves-discreteness d (inr *) (inl x₂) = inr (λ ())
+𝟙-preserves-discreteness d (inr *) (inr *) = inl refl

𝔽-discrete : (n : ℕ) → discrete (𝔽 n)
𝔽-discrete 0 = 𝟘-discrete
𝔽-discrete 1 = 𝟙-discrete
𝔽-discrete (succ (succ n)) = +𝟙-preserves-discreteness (𝔽-discrete (succ n))

𝟚-discrete : discrete 𝟚
𝟚-discrete = 𝔽-discrete 2

zero-or-one : (b : 𝟚) → (b ≡ ⁰) + (b ≡ ¹)
zero-or-one ⁰ = inl refl
zero-or-one ¹ = inr refl


𝟛-discrete : discrete 𝟛
𝟛-discrete = 𝔽-discrete 3

ℕ-discrete : discrete ℕ
ℕ-discrete zero zero = inl refl
ℕ-discrete zero (succ b) = inr (λ ())
ℕ-discrete (succ a) zero = inr (λ ())
ℕ-discrete (succ a) (succ b) = Cases (ℕ-discrete a b)
                                                 (λ a≡b → inl (ap succ a≡b))
                                                 λ ¬a≡b → inr (λ sa≡sb → ¬a≡b (inj₂ a b sa≡sb))



-- Vectors (note the numbers are mis-aligned to make proofs simpler)
Vec : (X : 𝓤 ̇) → ℕ → 𝓤 ̇
Vec X 0 = X
Vec X (succ n) = X × Vec X n

-- Constant version of +-elimination (called 'Cases')
if_then_else_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → X + Y → A → A → A
if inl _ then f else g = f
if inr _ then f else g = g

-- Shorthand for saying a predicate holds for all numbers below a given number
<ₙ : (ℕ → 𝓤 ̇) → ℕ → 𝓤 ̇
<ₙ P n = ∀ k → k < n → P k

-- Equivalence Relation

record EquivRel {X : 𝓤 ̇} (_≈_ : X → X → 𝓤 ̇) : 𝓤 ̇ where
  field
    ref : ∀ a → a ≈ a
    sym : ∀ a b → a ≈ b → b ≈ a
    tra : ∀ a b c → a ≈ b → b ≈ c → a ≈ c

≡-is-equivrel : {X : 𝓤 ̇} → EquivRel {𝓤} {X} _≡_
EquivRel.ref ≡-is-equivrel a = refl
EquivRel.sym ≡-is-equivrel a b = _⁻¹
EquivRel.tra ≡-is-equivrel a b c = _∙_

×-preserves-equivrel : {X : 𝓤 ̇} {Y : 𝓥 ̇} {_≈₁_ : X → X → 𝓤 ̇}{_≈₂_ : Y → Y → 𝓥 ̇}
                                    → EquivRel _≈₁_ → EquivRel _≈₂_
                                    → EquivRel (λ (a b : X × Y) → (pr₁ a ≈₁ pr₁ b) × (pr₂ a ≈₂ pr₂ b))
EquivRel.ref (×-preserves-equivrel R₁ R₂) (a₁ , a₂)
 = EquivRel.ref R₁ a₁ , EquivRel.ref R₂ a₂ 
EquivRel.sym (×-preserves-equivrel R₁ R₂) (a₁ , a₂) (b₁ , b₂) (a≈b₁ , a≈b₂)
 = EquivRel.sym R₁ a₁ b₁ a≈b₁ , EquivRel.sym R₂ a₂ b₂ a≈b₂
EquivRel.tra (×-preserves-equivrel R₁ R₂) (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) (a≈b₁ , a≈b₂) (b≈c₁ , b≈c₂)
 = EquivRel.tra R₁ a₁ b₁ c₁ a≈b₁ b≈c₁ , EquivRel.tra R₂ a₂ b₂ c₂ a≈b₂ b≈c₂

<ₙ-preserves-equivrel : {X : 𝓤 ̇} {_≈_ : X → X → 𝓤 ̇} → EquivRel _≈_
                                   → (n : ℕ) → EquivRel (λ (α β : ℕ → X) → <ₙ (λ k → α k ≈ β k) n)
EquivRel.ref (<ₙ-preserves-equivrel R n) α k _
 = EquivRel.ref R (α k)
EquivRel.sym (<ₙ-preserves-equivrel R n) α β α≈β k k<n
 = EquivRel.sym R (α k) (β k) (α≈β k k<n)
EquivRel.tra (<ₙ-preserves-equivrel R n) α β δ α≈β β≈δ k k<n
 = EquivRel.tra R (α k) (β k) (δ k) (α≈β k k<n) (β≈δ k k<n)

-- Max function for natural numbers

maxℕ : ℕ → ℕ → ℕ
maxℕ 0 0 = 0
maxℕ 0 (succ b) = succ b
maxℕ (succ a) 0 = succ a
maxℕ (succ a) (succ b) = succ (maxℕ a b)

max-sym : (a b : ℕ) → maxℕ a b ≡ maxℕ b a
max-sym zero zero = refl
max-sym zero (succ b) = refl
max-sym (succ a) zero = refl
max-sym (succ a) (succ b) = ap succ (max-sym a b)

<-max' : (k a b : ℕ) → k < a → k < maxℕ a b
<-max' zero (succ a) zero k<a = *
<-max' zero (succ a) (succ b) k<a = *
<-max' (succ k) (succ a) zero k<a = k<a
<-max' (succ k) (succ a) (succ b) k<a = <-max' k a b k<a

<-max : (k a b : ℕ) → k < a + k < b → k < maxℕ a b
<-max k a b (inl k<a) = <-max' k a b k<a
<-max k a b (inr k<b) = transport (k <_) (max-sym b a) (<-max' k b a k<b)

≤-max' : (a b x y : ℕ) → a ≤ b → x ≤ y → maxℕ a x ≤ maxℕ b y
≤-max' zero zero zero y a≤b x≤y = *
≤-max' zero zero (succ x) (succ y) a≤b x≤y = x≤y
≤-max' zero (succ b) zero y a≤b x≤y = *
≤-max' zero (succ b) (succ zero) (succ y) a≤b x≤y = *
≤-max' zero (succ b) (succ (succ x)) (succ y) a≤b x≤y = ≤-max' zero b (succ x) y * x≤y
≤-max' (succ a) (succ b) zero zero a≤b x≤y = a≤b
≤-max' (succ zero) (succ b) zero (succ y) a≤b x≤y = *
≤-max' (succ (succ a)) (succ b) zero (succ y) a≤b x≤y = ≤-max' (succ a) b zero y a≤b *
≤-max' (succ a) (succ b) (succ x) (succ y) a≤b x≤y = ≤-max' a b x y a≤b x≤y

≤-max : (m a b : ℕ) → a ≤ b → maxℕ m a ≤ maxℕ m b
≤-max m a b a≤b = ≤-max' m m a b (≤-refl m) a≤b

<≤-trans : (a b c : ℕ) → a < b → b ≤ c → a < c
<≤-trans zero (succ b) (succ c) a<b b≤c = *
<≤-trans (succ a) (succ b) (succ c) a<b b≤c = <≤-trans a b c a<b b≤c
