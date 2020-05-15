{-# OPTIONS --without-K --exact-split --safe #-}

open import Prelude
open import SpartanMLTT hiding (𝟚;₀;₁)
open import InfSequence 
open import SearchableTypes
open import DecidableAndDetachable
open import NaturalsOrder

module UIOrder where

{- (1) Defining the partial orders <ᵁ, <ᴵ and total order ≤ᵁ -}

<'ₛ : {X : 𝓤 ̇} → (<ₓ : X → X → 𝓤 ̇) → 𝕊 X → 𝕊 X → ℕ → 𝓤 ̇
<'ₛ _<ₓ_ α β m = (α ≈ β) m × (α m <ₓ β m)

<ₛ : {X : 𝓤 ̇} → (<ₓ : X → X → 𝓤 ̇) → 𝕊 X → 𝕊 X → ℕ → 𝓤 ̇
<ₛ <ₓ α β m = Σ \k → k < m × <'ₛ <ₓ α β k

_<₂_ : 𝟚 → 𝟚 → 𝓤₀ ̇
a <₂ b = (a ≡ ⁰) × (b ≡ ¹)

_<₃_ : 𝟛 → 𝟛 → 𝓤₀ ̇
a <₃ b = ((a ≡ ₀) × (b ≡ ₁)) + ((a ≡ ₋₁) × ((b ≡ ₀) + (b ≡ ₁)))

_<ᵁ_ : 𝕌 → 𝕌 → ℕ → 𝓤₀ ̇
_<ᵁ_ =  <ₛ _<₂_

_<ᴵ_ : 𝕀 → 𝕀 → ℕ → 𝓤₀ ̇
_<ᴵ_ = <ₛ _<₃_ -- Note that this order is problematic, due to elements of [-1,1] having multiple encodings in 𝕀

≤ₛ : {X : 𝓤 ̇} → (<ₓ : X → X → 𝓤 ̇) → 𝕊 X → 𝕊 X → ℕ → 𝓤 ̇
≤ₛ _<ₓ_ α β m = <ₛ _<ₓ_ α β m + (α ≈ β) m

_≤ᵁ_ : 𝕌 → 𝕌 → ℕ → 𝓤₀ ̇
_≤ᵁ_ =  ≤ₛ _<₂_

{- (2) Showing these orders are decidable -}

<'ₛ-decidable : {X : 𝓤 ̇} → discrete X → (<ₓ : X → X → 𝓤 ̇) → ((a b : X) → decidable (<ₓ a b))
                      → (α ε : 𝕊 X) (m : ℕ) → decidable (<'ₛ <ₓ α ε m)
<'ₛ-decidable d <ₓ dec α ε m = ×-preserves-decidability (≈-decidable d α ε m) (dec (α m) (ε m))

<ₙ-preserves-decidability : {A : ℕ → 𝓤 ̇} → detachable A → ∀ m → decidable (Σ \k → k < m × A k)
<ₙ-preserves-decidability {𝓤} {A} d 0 = inr (λ <₀ → pr₁ (pr₂ <₀))
<ₙ-preserves-decidability {𝓤} {A} d (succ m) = Cases (d m)
                                                                (λ Am → inl (m , <-succ m , Am))
                                                                (Cases (<ₙ-preserves-decidability d m) γ₁ λ x₁ x₂ → inr (γ₂ x₁ x₂)) where
  γ₁ : Σ (λ k → (k < m) × A k) → ¬ A m → Σ (λ v → (v < succ m) × A v) + ¬ Σ (λ k → (k < succ m) × A k)
  γ₁ (k , k<m , Ak) _ = inl (k , <-trans k m (succ m) k<m (<-succ m) , Ak)
  γ₂ : ¬ Σ (λ k → (k < m) × A k) → ¬ A m → ¬ Σ (λ k → (k < succ m) × A k)
  γ₂ ¬Σk ¬Am (k , k<m , Ak) = ¬Σk (k , γ₂< k m k<m (λ k≡m → ¬Am (transport A k≡m Ak)) , Ak) where
    γ₂< : (k m : ℕ) → k < succ m → k ≢ m → k < m
    γ₂< zero zero k<sm k≢m = 𝟘-elim (k≢m refl)
    γ₂< zero (succ m) k<sm k≢m = *
    γ₂< (succ k) (succ m) k<sm k≢m = γ₂< k m k<sm (λ k≡m → k≢m (ap succ k≡m))

<ₛ-decidable : {X : 𝓤 ̇} → discrete X → (<ₓ : X → X → 𝓤 ̇) → ((a b : X) → decidable (<ₓ a b))
                      → (α ε : 𝕊 X) (m : ℕ) → decidable (<ₛ <ₓ α ε m)
<ₛ-decidable d <ₓ dec α ε m = <ₙ-preserves-decidability (<'ₛ-decidable d <ₓ dec α ε) m
 
<₂-antireflexive : (a : 𝟚) → ¬ (a <₂ a)
<₂-antireflexive ⁰ ()
<₂-antireflexive ¹ ()

<₂-antisymmetric : (a b : 𝟚) → (a <₂ b) → ¬ (b <₂ a)
<₂-antisymmetric ⁰ ¹ _ ()

<₂-decidable : (a b : 𝟚) → decidable (a <₂ b)
<₂-decidable ⁰ ⁰ = inr (<₂-antireflexive ⁰)
<₂-decidable ⁰ ¹ = inl (refl , refl)
<₂-decidable ¹ ⁰ = inr (<₂-antisymmetric ⁰ ¹ (refl , refl))
<₂-decidable ¹ ¹ = inr (<₂-antireflexive ¹)

<ᵁ-decidable : (α ε : 𝕌) (m : ℕ) → decidable ((α <ᵁ ε) m)
<ᵁ-decidable = <ₛ-decidable 𝟚-discrete _<₂_ <₂-decidable

<₃-antireflexive : (a : 𝟛) → ¬ (a <₃ a)
<₃-antireflexive ₋₁ (inr (_ , inl ()))
<₃-antireflexive ₁ (inr ())

<₃-antisymmetric : (a b : 𝟛) → (a <₃ b) → ¬ (b <₃ a)
<₃-antisymmetric ₋₁ ₋₁ x = 𝟘-elim (<₃-antireflexive ₋₁ x)
<₃-antisymmetric   ₀   ₀ x = 𝟘-elim (<₃-antireflexive ₀ x)
<₃-antisymmetric   ₁   ₁ x = 𝟘-elim (<₃-antireflexive ₁ x)
<₃-antisymmetric ₋₁ ₀ _ (inr ())
<₃-antisymmetric ₋₁ ₁ _ (inr ())
<₃-antisymmetric ₀ ₁ _ (inr ())
<₃-antisymmetric ₀ ₋₁ (inl ())
<₃-antisymmetric   ₁ ₋₁ (inl ())
<₃-antisymmetric   ₁   ₀ (inl ())

<₃-decidable : (a b : 𝟛) → decidable (a <₃ b)
<₃-decidable ₋₁ ₋₁ = inr (<₃-antireflexive ₋₁)
<₃-decidable ₀ ₀ = inr (<₃-antireflexive ₀)
<₃-decidable ₁ ₁ = inr (<₃-antireflexive ₁)
<₃-decidable ₀ ₋₁ = inr (<₃-antisymmetric ₋₁ ₀ (inr (refl , inl refl)))
<₃-decidable ₁ ₋₁ = inr (<₃-antisymmetric ₋₁ ₁ (inr (refl , inr refl)))
<₃-decidable ₁ ₀ = inr (<₃-antisymmetric ₀ ₁ (inl (refl , refl)))
<₃-decidable ₋₁ ₀ = inl (inr (refl , inl refl))
<₃-decidable ₋₁ ₁ = inl (inr (refl , inr refl))
<₃-decidable ₀ ₁ = inl (inl (refl , refl))

<ᴵ-decidable : (α ε : 𝕀) (m : ℕ) → decidable ((α <ᴵ ε) m)
<ᴵ-decidable = <ₛ-decidable 𝟛-discrete _<₃_ <₃-decidable

≤ₛ-decidable : {X : 𝓤 ̇} → discrete X → (<ₓ : X → X → 𝓤 ̇) → ((a b : X) → decidable (<ₓ a b))
                                                              → (α ε : 𝕊 X) (m : ℕ) → decidable (≤ₛ <ₓ α ε m)
≤ₛ-decidable d <ₓ dec α ε m = +-preserves-decidability (<ₛ-decidable d <ₓ dec α ε m) (≈-decidable d α ε m)

≤ᵁ-decidable : (α ε : 𝕌) (m : ℕ) → decidable ((α ≤ᵁ ε) m)
≤ᵁ-decidable = ≤ₛ-decidable 𝟚-discrete _<₂_ <₂-decidable

{- (2) Showing the <ᵁ order is continuous -}

<ᵁ-continuous₁ : (ε : 𝕌) (n : ℕ) → continuous 𝕌* (λ α → (α <ᵁ ε) n)
<ᵁ-continuous₁ ε n = (n , *) , λ α β α≈β → γ α β α≈β , γ β α (≈-sym α β n α≈β) where
  γ : (α β : 𝕌) → (α ≈ β) n → (α <ᵁ ε) n → (β <ᵁ ε) n
  γ α β α≈β (k , k<n , α≈ε , α<ε)
                                         = k , k<n
                                          , ≈-trans β α ε k (≈-sym α β k (≈-low α β n α≈β k k<n)) α≈ε
                                          , transport (_<₂ ε k) (α≈β k k<n) α<ε

<ᵁ-continuous₂ : (α : 𝕌) (n : ℕ) → continuous 𝕌* (λ ε → (α <ᵁ ε) n)
<ᵁ-continuous₂ α n = (n , *) , λ ε δ ε≈δ → γ ε δ ε≈δ , γ δ ε (≈-sym ε δ n ε≈δ) where
  γ : (ε δ : 𝕌) → (ε ≈ δ) n → (α <ᵁ ε) n → (α <ᵁ δ) n
  γ ε δ ε≈δ (k , k<n , α≈ε , α<ε)
                                         = k , k<n
                                         , ≈-trans α ε δ k α≈ε (≈-low ε δ n ε≈δ k k<n)
                                         , transport (α k <₂_) (ε≈δ k k<n) α<ε

<ᵁ-transport₁ : (α β ε : 𝕌) (m : ℕ) → (α ≈ β) (pr₁ (pr₁ (<ᵁ-continuous₁ ε m)))
                         → (α <ᵁ ε) m → (β <ᵁ ε) m
<ᵁ-transport₁ α β ε m α≈β = pr₁ (pr₂ (<ᵁ-continuous₁ ε m) α β α≈β)

<ᵁ-transport₂ : (α ε δ : 𝕌) (m : ℕ) → (ε ≈ δ) (pr₁ (pr₁ (<ᵁ-continuous₂ α m)))
                         → (α <ᵁ ε) m → (α <ᵁ δ) m
<ᵁ-transport₂ α ε δ m ε≈δ = pr₁ (pr₂ (<ᵁ-continuous₂ α m) ε δ ε≈δ)

{- (3) Proving that <ᵁ gives a family of strict partial orders -}

record StrictPartialOrder {X : 𝓤 ̇} (_<_ : X → X → 𝓤 ̇) : 𝓤 ⁺ ̇ where
  field
    irref : ∀ a → ¬ (a < a)
    trans : ∀ a b c → a < b → b < c → a < c

ℕ-split : (n m : ℕ) → (n ≡ m) + ((n < m) + (m < n))
ℕ-split zero zero = inl refl
ℕ-split zero (succ m) = inr (inl *)
ℕ-split (succ n) zero = inr (inr *)
ℕ-split (succ n) (succ m)
  = Cases (ℕ-split n m)
      (λ x → inl (ap succ x))
      (λ y → Cases y (λ y₁ → inr (inl y₁)) (λ y₂ → inr (inr y₂)))

<₂-fact : (a b : 𝟚) → a <₂ b → a ≢ b
<₂-fact ⁰ ¹ a<b = λ ()

<₂-PartialOrder : StrictPartialOrder _<₂_
StrictPartialOrder.irref <₂-PartialOrder ⁰ ()
StrictPartialOrder.irref <₂-PartialOrder ¹ ()
StrictPartialOrder.trans <₂-PartialOrder ¹ ¹ ¹ () ()

<₂-trans = StrictPartialOrder.trans <₂-PartialOrder

<ᵁ-PartialOrder : (m : ℕ) → StrictPartialOrder (λ α β → (α <ᵁ β) m)
StrictPartialOrder.irref (<ᵁ-PartialOrder m) α (k , k<m , _ , α<α) = <₂-fact (α k) (α k) α<α refl
StrictPartialOrder.trans (<ᵁ-PartialOrder m) α β δ (k , k<m , α≈β , α<β) (j , j<m , β≈δ , β<δ)
 = Cases (ℕ-split j k)
          (λ j≡k → k , k<m , ≈-trans α β δ k α≈β (transport (β ≈ δ) j≡k β≈δ)
                                       , <₂-trans (α k) (β k) (δ k) α<β (transport (λ ■ → β ■ <₂ δ ■) j≡k β<δ))
     (λ y → Cases y
          (λ j<k → j , j<m , ≈-trans α β δ j (λ n n<j → α≈β n (<-trans n j k n<j j<k)) β≈δ
                                     , transport (_<₂ δ j) (α≈β j j<k ⁻¹) β<δ)
          λ k<j → k , k<m , ≈-trans α β δ k α≈β (λ n n<k → β≈δ n (<-trans n k j n<k k<j))
                                     , transport (α k <₂_) (β≈δ k k<j) α<β)

{- (4) Proving that ≤ᵁ gives a family of total orders -}

record TotalOrder {X : 𝓤 ̇} (_≤_ : X → X → 𝓤 ̇) : 𝓤 ⁺ ̇ where
  field
    _≊_ : X → X → 𝓤 ̇
    ≊-EquivRel : EquivRel _≊_
    antisym : ∀ a b → a ≤ b → b ≤ a → a ≊ b
    trans : ∀ a b c → a ≤ b → b ≤ c → a ≤ c
    connex : ∀ a b → a ≤ b + b ≤ a
  ref : ∀ a → a ≤ a
  ref a = Cases (connex a a) id id

≤ᵁ-trichotomous₁ : (α β : 𝕌) (m : ℕ) → (¬ (α <ᵁ β) m × ¬ (β <ᵁ α) m) → (α ≈ β) m
≤ᵁ-trichotomous₁ α β zero (¬α<β , ¬β<α) _ ()
≤ᵁ-trichotomous₁ α β (succ m) (¬α<β , ¬β<α) k k<sm
  = Cases (ℕ-discrete k m)
      (λ k≡m → transport (λ ■ → α ■ ≡ β ■) (k≡m ⁻¹)
                       (<₂-trichotomous≡ (α m) (β m)
                          (≤ᵁ-fact α β m ¬α<β
                              (≤ᵁ-trichotomous₁ α β m ((≤ᵁ-not-lower α β m ¬α<β) , (≤ᵁ-not-lower β α m ¬β<α))))
                          (≤ᵁ-fact β α m ¬β<α
                              (≤ᵁ-trichotomous₁ β α m ((≤ᵁ-not-lower β α m ¬β<α) , (≤ᵁ-not-lower α β m ¬α<β))))))
      (λ k≢m → ≤ᵁ-trichotomous₁ α β m ((≤ᵁ-not-lower α β m ¬α<β) , (≤ᵁ-not-lower β α m ¬β<α))
                       k (≤-low k m k<sm k≢m))
  where
    ≤ᵁ-not-lower : (α β : 𝕌) (m : ℕ) → ¬ (α <ᵁ β) (succ m) → ¬ (α <ᵁ β) m
    ≤ᵁ-not-lower α β m ¬α<β (k , k<m , α<β) = ¬α<β (k , <-trans k m (succ m) k<m (<-succ m) , α<β)
    ≤ᵁ-fact : (α β : 𝕌) (m : ℕ) → ¬ (α <ᵁ β) (succ m) → (α ≈ β) m → ¬ (α m <₂ β m)
    ≤ᵁ-fact α β m ¬α<β α≈βm αm<βm = ¬α<β (m , <-succ m , α≈βm , αm<βm)
    <₂-trichotomous≡ : (a b : 𝟚) → ¬ (a <₂ b) → ¬ (b <₂ a) → a ≡ b
    <₂-trichotomous≡ ⁰ ⁰ ¬a<b ¬b<a = refl
    <₂-trichotomous≡ ¹ ¹ ¬a<b ¬b<a = refl
    <₂-trichotomous≡ ⁰ ¹ ¬a<b ¬b<a = 𝟘-elim (¬a<b (refl , refl))
    <₂-trichotomous≡ ¹ ⁰ ¬a<b ¬b<a = 𝟘-elim (¬b<a (refl , refl))
    ≤-low : (k m : ℕ) → k ≤ m → k ≢ m → k < m
    ≤-low zero zero k≤m k≢m = k≢m refl
    ≤-low zero (succ m) k≤m k≢m = *
    ≤-low (succ k) (succ m) k≤m k≢m = ≤-low k m k≤m (λ k≡m → k≢m (ap succ k≡m))
    
deMorg+ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → ¬ (¬ X × ¬ Y) → decidable X → decidable Y → X + Y
deMorg+ _ (inl X) _ = inl X
deMorg+ _ (inr _) (inl Y) = inr Y
deMorg+ ¬¬X¬Y (inr ¬X) (inr ¬Y) = 𝟘-elim (¬¬X¬Y (¬X , ¬Y))

≤ᵁ-trichotomous₂ : (α β : 𝕌) (m : ℕ) → ¬ (α ≈ β) m → (α <ᵁ β) m + (β <ᵁ α) m
≤ᵁ-trichotomous₂ α β m ¬α≈β = deMorg+ (contrapositive (≤ᵁ-trichotomous₁ α β m) ¬α≈β)
                                                    (<ᵁ-decidable α β m) (<ᵁ-decidable β α m)

≤ᵁ-TotalOrder : (m : ℕ) → TotalOrder (λ α β → (α ≤ᵁ β) m)
TotalOrder._≊_ (≤ᵁ-TotalOrder m) α β = (α ≈ β) m
TotalOrder.≊-EquivRel (≤ᵁ-TotalOrder m) = ST-≈-EquivRel 𝕌* (m , *)
TotalOrder.antisym (≤ᵁ-TotalOrder m) α β (inl (k , k<m , α≈β , α<β)) (inl (j , j<m , β≈α , β<α))
  = Cases (ℕ-split k j)
      (λ k≡j → 𝟘-elim (<₂-antisymmetric (α k) (β k) α<β (transport (λ ■ → β ■ <₂ α ■) (k≡j ⁻¹) β<α)))
      (λ y → Cases y
      (λ k<j → 𝟘-elim (<₂-fact (α k) (β k) α<β (≈-sym β α j β≈α k k<j)))
      (λ j<k → 𝟘-elim (<₂-fact (β j) (α j) β<α (≈-sym α β k α≈β j j<k))))
TotalOrder.antisym (≤ᵁ-TotalOrder m) α β (inl _) (inr β≈α) = ≈-sym β α m β≈α
TotalOrder.antisym (≤ᵁ-TotalOrder m) α β (inr α≈β) _ = α≈β
TotalOrder.trans (≤ᵁ-TotalOrder m) α β δ (inl α<β) (inl β<δ)
  = inl (StrictPartialOrder.trans (<ᵁ-PartialOrder m) α β δ α<β β<δ)
TotalOrder.trans (≤ᵁ-TotalOrder m) α β δ (inl α<β) (inr β≈δ)
  = inl (<ᵁ-transport₂ α β δ m β≈δ α<β)
TotalOrder.trans (≤ᵁ-TotalOrder m) α β δ (inr α≈β) (inl β<δ)
  = inl (<ᵁ-transport₁ β α δ m (≈-sym α β m α≈β) β<δ)
TotalOrder.trans (≤ᵁ-TotalOrder m) α β δ (inr α≈δ) (inr β≈δ)
  = inr (≈-trans α β δ m α≈δ β≈δ)
TotalOrder.connex (≤ᵁ-TotalOrder m) α β = Cases (≈-decidable 𝟚-discrete α β m)
                                                                                 (λ α≈β → inl (inr α≈β))
                                                                            (λ ¬α≈β → Cases (≤ᵁ-trichotomous₂ α β m ¬α≈β)
                                                                                 (λ α<β → inl (inl α<β)) (λ β<α → inr (inl β<α)))

≤ᵁ-refl = λ m → TotalOrder.ref (≤ᵁ-TotalOrder m)
≤ᵁ-con = λ m → TotalOrder.connex (≤ᵁ-TotalOrder m)
≤ᵁ-trans = λ m → TotalOrder.trans (≤ᵁ-TotalOrder m)

≤ᵁ-least-element : (m : ℕ) → Σ \x₀ → ∀ x → (x₀ ≤ᵁ x) m
≤ᵁ-least-element m = 0₂ , λ x → Cases (≤ᵁ-con m 0₂ x) id (γ x) where
  γ : ∀ x → (x ≤ᵁ 0₂) m → (0₂ ≤ᵁ x) m
  γ x (inr x≈0₂) = inr (≈-sym x 0₂ m x≈0₂)

