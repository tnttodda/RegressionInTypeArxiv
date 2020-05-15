{-# OPTIONS --without-K --exact-split --safe #-}

module SearchableTypes where

open import Prelude
open import SpartanMLTT hiding (𝟚;₀;₁)
open import NaturalsOrder
open import InfSequence
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import UF-Equiv
open import DecidableAndDetachable

{- (1) S-Types and the equivalence relation on S-Types -}

-- The signatures for S-Types
data ST : 𝓤₀ ̇ where
  𝔽* : (n : ℕ) → n ≢ 0 → ST
  ×* : ST → ST → ST
  →* : ST → ST

-- S-Type signature for vectors
𝕍* : (st : ST) (n : ℕ) → ST
𝕍* st 0 = st
𝕍* st (succ n) = ×* st (𝕍* st n)

-- Gives the S-Type from its signature
ST-Type : ST → 𝓤₀ ̇
ST-Type (𝔽* n _) = 𝔽 n
ST-Type (×* st₁ st₂) = ST-Type st₁ × ST-Type st₂
ST-Type (→* st) = 𝕊 (ST-Type st)

-- Gives the exactness type for an S-type from its signature
ST-Moduli : ST → 𝓤₀ ̇
ST-Moduli (𝔽* _ _) = 𝟙
ST-Moduli (×* st₁ st₂) = ST-Moduli st₁ × ST-Moduli st₂
ST-Moduli (→* st) = ℕ × ST-Moduli st

-- Definition of equality with precision m
ST-≈ : (st : ST) (a b : ST-Type st) (m : ST-Moduli st) → 𝓤₀ ̇
ST-≈ (𝔽* _ _) a b _ = a ≡ b
ST-≈ (×* st₁ st₂) (a₁ , a₂) (b₁ , b₂) (m₁ , m₂) = ST-≈ st₁ a₁ b₁ m₁ × ST-≈ st₂ a₂ b₂ m₂
ST-≈ (→* st) a b (n , m) = <ₙ (λ k → ST-≈ st (a k) (b k) m) n

-- Given a precision m and for any S-Type, equality precision m is an equivalence relation
ST-≈-EquivRel : (st : ST) (m : ST-Moduli st) → EquivRel (λ α β → ST-≈ st α β m)
ST-≈-EquivRel (𝔽* _ _) * = ≡-is-equivrel
ST-≈-EquivRel (×* st₁ st₂) (m₁ , m₂)= ×-preserves-equivrel (ST-≈-EquivRel st₁ m₁) (ST-≈-EquivRel st₂ m₂)
ST-≈-EquivRel (→* st) (n , m) = <ₙ-preserves-equivrel (ST-≈-EquivRel st m) n

-- These are for easy access to the reflexivity, symmetricity and transitivity properties of ST-≈ 
ST-≈-refl : (st : ST) (m : ST-Moduli st) → ∀ α → ST-≈ st α α m
ST-≈-refl st m = EquivRel.ref (ST-≈-EquivRel st m)

ST-≈-sym : (st : ST) (m : ST-Moduli st) → ∀ α β → ST-≈ st α β m → ST-≈ st β α m
ST-≈-sym st m = EquivRel.sym (ST-≈-EquivRel st m)

ST-≈-trans : (st : ST) (m : ST-Moduli st) → ∀ α β δ → ST-≈ st α β m → ST-≈ st β δ m → ST-≈ st α δ m
ST-≈-trans st m = EquivRel.tra (ST-≈-EquivRel st m)



{- (2) Continuity on S-Types, the motivation behind using S-Types -}

-- Continuity on predicates of S-Types
uc-mod : (st : ST) (p : ST-Type st → 𝓤₀ ̇) (m : ST-Moduli st) → 𝓤₀ ̇
uc-mod st p m = (α β : ST-Type st) → ST-≈ st α β m → p α ⇔ p β

continuous : (st : ST) (p : ST-Type st → 𝓤₀ ̇) → 𝓤₀ ̇
continuous st p = Σ (uc-mod st p)

-- Continuity on functions of S-Types
uc-mod² : (st₁ st₂ : ST) (f : ST-Type st₁ → ST-Type st₂) (n : ST-Moduli st₂) (m : ST-Moduli st₁) → 𝓤₀ ̇
uc-mod² st₁ st₂ f n m = (α β : ST-Type st₁) → ST-≈ st₁ α β m → ST-≈ st₂ (f α) (f β) n

continuous² : (st₁ st₂ : ST) (f : ST-Type st₁ → ST-Type st₂) → 𝓤₀ ̇
continuous² st₁ st₂ f = Π \n → Σ (uc-mod² st₁ st₂ f n)

-- All predicates with finite domain are trivially continuous
all-𝔽-preds-continuous : (n : ℕ) (z : n ≢ 0) → (p : ST-Type (𝔽* n z) → 𝓤₀ ̇) → continuous (𝔽* n z) p
all-𝔽-preds-continuous n z p = * , γ where
  γ : (α β : ST-Type (𝔽* n z)) → ST-≈ (𝔽* n z) α β * → p α ⇔ p β
  γ α .α refl = id , id

-- All functions with finite domain are trivially continuous
all-𝔽-funs-continuous : (n : ℕ) (z : n ≢ 0) (st : ST) → (f : ST-Type (𝔽* n z) → ST-Type st)
                                     → continuous² (𝔽* n z) st f
all-𝔽-funs-continuous n z st f m = * , γ where
  γ : (α β : ST-Type (𝔽* n z)) → ST-≈ (𝔽* n z) α β * → ST-≈ st (f α) (f β) m
  γ α .α refl = ST-≈-refl st m (f α) 

-- Composition preserves continuity
∘-continuous : (st₁ st₂ st₃ : ST)
                       → ∀ f g → continuous² st₁ st₂ f → continuous² st₂ st₃ g
                       → continuous² st₁ st₃ (g ∘ f)
∘-continuous st₁ st₂ st₃ f g c₁ c₂ n
 = pr₁ (c₁ (pr₁ (c₂ n))) , λ α β α≈β → pr₂ (c₂ n) (f α) (f β) (pr₂ (c₁ (pr₁ (c₂ n))) α β α≈β)

-- Definition for when two predicates on S-Types are 'equal' up to a given point
ST-≈ₚ : (st : ST) (p₁ p₂ : ST-Type st → 𝓤₀ ̇) → 𝓤₀ ̇
ST-≈ₚ st p₁ p₂ = Σ \m → (α β : ST-Type st) → ST-≈ st α β m → p₁ α ⇔ p₂ β 

{- (3) Continuous Searchability, inspired by Escardó's Searchable Types -}

-- Definition of Continuous Searchability for S-Types
searcher : (st : ST) → 𝓤₁ ̇
searcher st = (p : ST-Type st → 𝓤₀ ̇) → detachable p → continuous st p → ST-Type st

continuous-searcher : (st : ST) (𝓔 : searcher st) → 𝓤₁ ̇
continuous-searcher st 𝓔 = (p₁ p₂ : ST-Type st → 𝓤₀ ̇) (d₁ : detachable p₁) (d₂ : detachable p₂)
                                         → (ms : ST-Moduli st) (ϕ₁ : uc-mod st p₁ ms) (ϕ₂ : uc-mod st p₂ ms)
                                         → (cₚ : ST-≈ₚ st p₁ p₂) → ST-≈ st (𝓔 p₁ d₁ (ms , ϕ₁)) (𝓔 p₂ d₂ (ms , ϕ₂)) (pr₁ cₚ)

search-condition : (st : ST) (𝓔 : searcher st) → 𝓤₁ ̇
search-condition st 𝓔 = (p : ST-Type st → 𝓤₀ ̇) (d : detachable p) (c : continuous st p) → Σ p → p (𝓔 p d c)

continuously-searchable : (st : ST) → 𝓤₁ ̇
continuously-searchable st = Σ \(𝓔 : searcher st) → continuous-searcher st 𝓔 × search-condition st 𝓔

-- Finite Types are Continuously Searchable
finite-ST-searchable : (n : ℕ) → continuously-searchable (𝔽* (succ n) (λ ()))
finite-ST-searchable 0 = 𝓔 , C , S where
  𝓔 : searcher (𝔽* 1 (λ ()))
  𝓔 p d _ = *
  C : continuous-searcher (𝔽* 1 (λ ())) 𝓔
  C p₁ p₂ d₁ d₂ _ _ _ _ = refl
  S : search-condition (𝔽* 1 (λ ())) 𝓔
  S p d _ (* , p*) = p*
finite-ST-searchable (succ n) = 𝓔 , C , S where
  𝓔x = pr₁ (finite-ST-searchable n)
  Cx = pr₁ (pr₂ (finite-ST-searchable n))
  Sx = pr₂ (pr₂ (finite-ST-searchable n))
  S1 = pr₂ (pr₂ (finite-ST-searchable 0))
  x₀ : (p : 𝔽 (succ n) + 𝟙 → 𝓤₀ ̇) → detachable p → ST-Type (𝔽* (succ n) λ ())
  x₀ p d = 𝓔x (λ x → p (inl x)) (λ x → d (inl x)) (all-𝔽-preds-continuous (succ n) (λ ()) λ x → p (inl x))
  𝓔 : searcher (𝔽* (succ (succ n)) λ ())
  𝓔 p d _ = if (d (inl (x₀ p d))) then (inl (x₀ p d)) else (inr *)
  C : continuous-searcher (𝔽* (succ (succ n)) λ ()) 𝓔
  C p₁ p₂ d₁ d₂ _ _ _ (* , ϕₚ) = C' (d₁ (inl (x₀ p₁ d₁))) (d₂ (inl (x₀ p₂ d₂))) where
    x₀≡ : x₀ p₁ d₁ ≡ x₀ p₂ d₂
    x₀≡ = Cx _ _ _ _ _ _ (pr₂ (all-𝔽-preds-continuous (succ n) (λ ()) λ x → p₂ (inl x))) (* , λ α β α≈β → ϕₚ _ _ (ap inl α≈β))
    C' : (d*₁ : decidable (p₁ (inl (x₀ p₁ d₁)))) (d*₂ : decidable (p₂ (inl (x₀ p₂ d₂))))
                → (if d*₁ then (inl (x₀ p₁ d₁)) else (inr *)) ≡ (if d*₂ then (inl (x₀ p₂ d₂)) else (inr *))
    C' (inl p₁x) (inl p₂x) = ap inl x₀≡
    C' (inr p₁*) (inr p₂*) = refl
    C' (inl p₁x) (inr p₂*) = 𝟘-elim (p₂* (pr₁ (ϕₚ _ _ (ap inl x₀≡)) p₁x))
    C' (inr p₁*) (inl p₂x) = 𝟘-elim (p₁* (pr₂ (ϕₚ _ _ (ap inl x₀≡)) p₂x))
  S : search-condition (𝔽* (succ (succ n)) λ ()) 𝓔
  S p d _ = S' (d (inl (x₀ p d))) where
    S' : (d* : decidable (p (inl (x₀ p d)))) → Σ p → p (if d* then (inl (x₀ p d)) else (inr *))
    S' (inl px₀) (inl x* , px*) = px₀
    S' (inl px₀) (inr y* , py*) = px₀
    S' (inr ¬px₀) (inl x* , px*) = 𝟘-elim (¬px₀ (Sx (λ x → p (inl x)) (λ x → d (inl x))
                                               (all-𝔽-preds-continuous (succ n) (λ ()) (λ x → p (inl x))) (x* , px*)))
    S' (inr ¬px₀) (inr y* , py*) = S1 (λ y → p (inr y)) (λ y → d (inr y))
                                               (all-𝔽-preds-continuous 1 (λ ()) (λ z → p (inr z))) (y* , py*)

-- Binary Products of Continuously Searchable S-Types are Continuously Searchable
product-ST-searchable : (st₁ st₂ : ST) → continuously-searchable st₁ → continuously-searchable st₂
                                     → continuously-searchable (×* st₁ st₂)
product-ST-searchable st₁ st₂ (𝓔x , Cx , Sx) (𝓔y , Cy , Sy) = 𝓔 , C , S where
  X = ST-Type st₁
  Y = ST-Type st₂
  y₀* : (p : X × Y → 𝓤₀ ̇) → detachable p → continuous (×* st₁ st₂) p → X → Y
  y₀* p d ((m₁ , m₂) , ϕ) x = 𝓔y (λ y → p (x , y)) (λ y → d (x , y))
                                               (m₂ , (λ α β α≈β → ϕ (x , α) (x , β) ((ST-≈-refl st₁ m₁ x) , α≈β)))
  x₀* : (p : X × Y → 𝓤₀ ̇) → detachable p → continuous (×* st₁ st₂) p → X
  x₀* p d ((m₁ , m₂) , ϕ) = 𝓔x (λ x → p (x , y₀ x)) (λ x → d (x , y₀ x))
                                            (m₁ , (λ α₁ β₁ α≈β₁ → ϕ _ _ (α≈β₁ ,
                                             Cy _ _ _ _ _ _ _ (m₂ , (λ α₂ β₂ α≈β₂ → ϕ (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂)))))) where
      y₀ = y₀* p d ((m₁ , m₂) , ϕ)
  𝓔 : (p : X × Y → 𝓤₀ ̇) → detachable p → continuous (×* st₁ st₂) p → X × Y
  𝓔 p d ((m₁ , m₂) , ϕ) = x₀ , x→y₀ x₀ where
      x₀ = x₀* p d ((m₁ , m₂) , ϕ)
      x→y₀ = y₀* p d ((m₁ , m₂) , ϕ)
  C : continuous-searcher (×* st₁ st₂) 𝓔
  C p₁ p₂ d₁ d₂ ms ϕ₁ ϕ₂ ((m₁ , m₂) , ϕₚ) =
                               (Cx _ _ _ _ _ _ _ (m₁ , λ α₁ β₁ α≈β₁ → ϕₚ (α₁ , x→y₁ α₁) (β₁ , x→y₂ β₁) (α≈β₁ ,
                               (Cy _ _ _ _ _ _ _ (m₂ , λ α₂ β₂ α≈β₂ → ϕₚ (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂))))))
                              , (Cy _ _ _ _ _ _ _ (m₂ , λ α₂ β₂ α≈β₂ → ϕₚ (x₁ , α₂) (x₂ , β₂)
                               ((Cx _ _ _ _ _ _ _ (m₁ , λ α₁ β₁ α≈β₁ → ϕₚ (α₁ , x→y₁ α₁) (β₁ , (x→y₂ β₁)) (α≈β₁ ,
                               (Cy _ _ _ _ _ _ _ (m₂ , (λ α₂ β₂ α≈β₂ → ϕₚ (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂)))))) , α≈β₂)))) where
      x₁ = x₀* p₁ d₁ (ms , ϕ₁)
      x→y₁ = y₀* p₁ d₁ (ms , ϕ₁)
      x₂ = x₀* p₂ d₂ (ms , ϕ₂)
      x→y₂ = y₀* p₂ d₂ (ms , ϕ₂)
  S : (p : X × Y → 𝓤₀ ̇) (d : detachable p) (c : continuous (×* st₁ st₂) p) → Σ p → p (𝓔 p d c)
  S p d ((m₁ , m₂) , ϕ) ((x* , y*) , px*y*) = px₀y₀ where
      x₀ = x₀* p d ((m₁ , m₂) , ϕ)
      x→y₀ = y₀* p d ((m₁ , m₂) , ϕ)
      px₀y₀ : p (x₀ , x→y₀ x₀)
      px₀y₀ = Sx (λ x → p (x , x→y₀ x)) (λ x → d (x , x→y₀ x))
                        (m₁ , λ α₁ β₁ α≈β₁ → ϕ (α₁ , x→y₀ α₁) (β₁ , x→y₀ β₁) (α≈β₁ ,
                        Cy _ _ _ _ _ _ _ (m₂ , (λ α₂ β₂ α≈β₂ → ϕ (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂)))))
                  (x* , (Sy (λ y → p (x* , y)) (λ y → d (x* , y))
                                (m₂ , (λ α β α≈β → ϕ (x* , α) (x* , β) (ST-≈-refl st₁ m₁ x* , α≈β)))
                  (y* , px*y*)))

seq-build-eta : (st : ST) (a b : ST-Type st) (α β : 𝕊 (ST-Type st)) → (m : ℕ) (ms : ST-Moduli st)
          → ST-≈ st a b ms → ST-≈ (→* st) α β (m , ms)
          → ST-≈ (→* st) (a :: α) (b :: β) (succ m , ms)
seq-build-eta st a b α β m ms a≈b α≈β zero n<m = a≈b
seq-build-eta st a b α β m ms a≈b α≈β (succ n) n<m = α≈β n n<m

head-tail-refl : (st : ST) → (s : ST-Type (→* st)) → ∀ m → ST-≈ (→* st) s (head s :: tail s) m
head-tail-refl st s (n , m) 0 k<n = ST-≈-refl st m (s 0)
head-tail-refl st s (n , m) (succ k) k<n = ST-≈-refl st m (s (succ k))

tail-decrease-mod : (st : ST) (p : 𝕊 (ST-Type st) → 𝓤₀ ̇) (d : detachable p)
                                → (m : ℕ) (ms : ST-Moduli st)
                                → uc-mod (→* st) p (succ m , ms)
                                → (f : 𝕊 (ST-Type st) → ST-Type st)
                                → uc-mod² (→* st) st f ms (m , ms)
                                → uc-mod (→* st) (λ s → p (f s :: s)) (m , ms)
tail-decrease-mod st p d m ms ϕ f f≈ α β α≈β
  = ϕ (f α :: α) (f β :: β) (seq-build-eta st (f α) (f β) α β m ms (f≈ α β α≈β) α≈β)

-- Sequences of a Continuously Searchable S-Type are Continuously Searchable
tychonoff : (st : ST) → continuously-searchable st → continuously-searchable (→* st)
tychonoff st (𝓔x , Cx , Sx)
  = (λ p d c → 𝓔 p d (pr₁ (pr₁ c)) (pr₂ (pr₁ c)) (pr₂ c))
    , (λ p₁ p₂ d₁ d₂ ms ϕ₁ ϕ₂ cₚ → C p₁ p₂ d₁ d₂ (pr₁ ms) (pr₂ ms) ϕ₁ ϕ₂ (pr₁ (pr₁ cₚ)) (pr₂ (pr₁ cₚ)) (pr₂ cₚ))
    , (λ p d c → S p d (pr₁ (pr₁ c)) (pr₂ (pr₁ c)) (pr₂ c)) where
    
  X = ST-Type st
  𝓔 : (p : 𝕊 X → 𝓤₀ ̇) → detachable p → (m : ℕ) (ms : ST-Moduli st) → uc-mod (→* st) p (m , ms) → 𝕊 X
  C : (p₁ p₂ : 𝕊 X → 𝓤₀ ̇) (d₁ : detachable p₁) (d₂ : detachable p₂)
        → (m : ℕ) (ms : ST-Moduli st)
        → (ϕ₁ : uc-mod (→* st) p₁ (m , ms)) (ϕ₂ : uc-mod (→* st) p₂ (m , ms))
        → (mₚ : ℕ) (msₚ : ST-Moduli st) (ϕₚ : (α β : 𝕊 X) → ST-≈ (→* st) α β (mₚ , msₚ) → p₁ α ⇔ p₂ β)
        → ST-≈ (→* st) (𝓔 p₁ d₁ m ms ϕ₁) (𝓔 p₂ d₂ m ms ϕ₂) (mₚ , msₚ)
  S : (p : 𝕊 X → 𝓤₀ ̇) (d : detachable p) (m : ℕ) (ms : ST-Moduli st) (ϕ : uc-mod (→* st) p (m , ms))
        → Σ p → p (𝓔 p d m ms ϕ)

  α-build* : (p : 𝕊 X → 𝓤₀ ̇) → detachable p → (m : ℕ) (ms : ST-Moduli st) → uc-mod (→* st) p (succ m , ms)
                  → 𝕊 X → X
  α-build* p d m ms ϕ s = 𝓔x (λ x → p (x :: s)) (λ x → d (x :: s))
                                               (ms , λ a b a≈b → ϕ _ _ (seq-build-eta _ _ _ _ _ _ _ a≈b (ST-≈-refl (→* st) (m , ms) s)))
  tail-decrease-mod' : (p : 𝕊 X → 𝓤₀ ̇) (d : detachable p) (m : ℕ) (ms : ST-Moduli st)
                                   → (ϕ : uc-mod (→* st) p (succ m , ms))
                                   → uc-mod (→* st) (λ s → p (α-build* p d m ms ϕ s :: s)) (m , ms)
  tail-decrease-mod' p d m ms ϕ
    = tail-decrease-mod st p d m ms ϕ (α-build* p d m ms ϕ)
        (λ α β α≈β → Cx _ _ _ _ _ _ _ (ms ,
        (λ α₁ β₁ α≈β₁ → ϕ (α₁ :: α) (β₁ :: β) (seq-build-eta st α₁ β₁ α β m ms α≈β₁ α≈β))))
        
  αₜ* : (p : 𝕊 X → 𝓤₀ ̇) → detachable p → (m : ℕ) (ms : ST-Moduli st) → uc-mod (→* st) p (succ m , ms)
           → 𝕊 X
  αₜ* p d m ms ϕ = 𝓔 (λ s → p (α-build s :: s)) (λ s → d (α-build s :: s)) m ms
                                 (tail-decrease-mod' p d m ms ϕ) where
    α-build = α-build* p d m ms ϕ
  𝓔 p d zero ms ϕ = λ _ → 𝓔x (λ _ → 𝟙) (λ _ → inl *) (ms , λ _ _ _ → id , id)
  𝓔 p d (succ m) ms ϕ = α-build* p d m ms ϕ αₜ :: αₜ* p d m ms ϕ where
    α-build : 𝕊 X → X
    α-build = α-build* p d m ms ϕ
    αₜ : 𝕊 X
    αₜ = αₜ* p d  m ms ϕ

  Cᵢₕ : (p₁ p₂ : 𝕊 X → 𝓤₀ ̇) (d₁ : detachable p₁) (d₂ : detachable p₂)
        → (m : ℕ) (ms : ST-Moduli st)
        → (ϕ₁ : uc-mod (→* st) p₁ (succ m , ms)) (ϕ₂ : uc-mod (→* st) p₂ (succ m , ms))
        → (mₚ : ℕ) (msₚ : ST-Moduli st) (ϕₚ : (α β : 𝕊 X) → ST-≈ (→* st) α β (succ mₚ , msₚ) → p₁ α ⇔ p₂ β)
        → ST-≈ (→* st) (𝓔 (λ s → p₁ (α-build* p₁ d₁ m ms ϕ₁ s :: s))
                                     (λ s → d₁ (α-build* p₁ d₁ m ms ϕ₁ s :: s)) m ms (tail-decrease-mod' p₁ d₁ m ms ϕ₁))
                                 (𝓔 (λ s → p₂ (α-build* p₂ d₂ m ms ϕ₂ s :: s))
                                     (λ s → d₂ (α-build* p₂ d₂ m ms ϕ₂ s :: s)) m ms (tail-decrease-mod' p₂ d₂ m ms ϕ₂)) (mₚ , msₚ)
  Cᵢₕ p₁ p₂ d₁ d₂ m ms ϕ₁ ϕ₂ mₚ msₚ ϕₚ =
      C (λ s → p₁ (α-build₁ s :: s)) (λ s → p₂ (α-build₂ s :: s))
         (λ s → d₁ (α-build₁ s :: s)) (λ s → d₂ (α-build₂ s :: s))
         m ms (tail-decrease-mod' p₁ d₁ m ms ϕ₁) (tail-decrease-mod' p₂ d₂ m ms ϕ₂) mₚ msₚ
         (λ α β α≈β → ϕₚ (α-build₁ α :: α) (α-build₂ β :: β) (seq-build-eta st (α-build₁ α) (α-build₂ β) α β mₚ msₚ
             (Cx _ _ _ _ _ _ _ (msₚ ,
             (λ α₁ β₁ α≈β₁ → ϕₚ (α₁ :: α) (β₁ :: β) (seq-build-eta st α₁ β₁ α β mₚ msₚ α≈β₁ α≈β)))) α≈β)) where
    α-build₁ = α-build* p₁ d₁ m ms ϕ₁
    α-build₂ = α-build* p₂ d₂ m ms ϕ₂
    
  C p₁ p₂ d₁ d₂ zero ms ϕ₁ ϕ₂ mₚ msₚ ϕₚ n n<m =
                  Cx _ _ _ _ _ _ _ (msₚ , (λ _ _ _ → id , id))
  C p₁ p₂ d₁ d₂ (succ m) ms ϕ₁ ϕ₂ (succ mₚ) msₚ ϕₚ zero n<m =
                  Cx _ _ _ _ _ _ _ (msₚ , (λ α β α≈β → ϕₚ _ _ (seq-build-eta _ _ _ _ _ _ _ α≈β
                  (Cᵢₕ p₁ p₂ d₁ d₂ m ms ϕ₁ ϕ₂ mₚ msₚ ϕₚ)))) where
    α-build₁ = α-build* p₁ d₁ m ms ϕ₁
    α-build₂ = α-build* p₂ d₂ m ms ϕ₂
  C p₁ p₂ d₁ d₂ (succ m) ms ϕ₁ ϕ₂ (succ mₚ) msₚ ϕₚ (succ n) n<m = Cᵢₕ p₁ p₂ d₁ d₂ m ms ϕ₁ ϕ₂ mₚ msₚ ϕₚ n n<m where
    α-build₁ = α-build* p₁ d₁ m ms ϕ₁
    α-build₂ = α-build* p₂ d₂ m ms ϕ₂
    
  S p d zero ms ϕ (s , ps) = pr₁ (ϕ s (𝓔 p d 0 ms ϕ) (λ n ())) ps
  S p d (succ m) ms ϕ (s₀ , ps₀) = S (λ s → p (α-build s :: s)) (λ s → d (α-build s :: s))
                                              m ms (tail-decrease-mod' p d m ms ϕ)
                                              (tail s₀ , Sx (λ x → p (x :: tail s₀)) (λ x → d (x :: tail s₀))
                                                    (ms , λ a b a≈b →
                                                    ϕ (a :: tail s₀) (b :: tail s₀) (seq-build-eta st a b (tail s₀) (tail s₀) m ms a≈b
                                                    (ST-≈-refl (→* st) (m , ms) (tail s₀))))
                                              (head s₀ , pr₁ (ϕ s₀ (head s₀ :: tail s₀) (head-tail-refl st s₀ (succ m , ms))) ps₀)) where
    α-build = α-build* p d m ms ϕ
    αₜ = αₜ* p d m ms ϕ

-- All S-Types are Continuously Searchable
all-ST-searchable : (st : ST) → continuously-searchable st
all-ST-searchable (𝔽* 0 z) = 𝟘-elim (z refl)
all-ST-searchable (𝔽* (succ n) z) = finite-ST-searchable n
all-ST-searchable (×* st₁ st₂) = product-ST-searchable st₁ st₂ (all-ST-searchable st₁) (all-ST-searchable st₂)
all-ST-searchable (→* st) = tychonoff st (all-ST-searchable st)

{- (4) Order of the exactness types -}

-- The constructions of each exactness type are ordered according to the following order:
ST-Moduli-≤ : (st : ST) → (a b : ST-Moduli st) → 𝓤₀ ̇
ST-Moduli-≤ (𝔽* _ _) * * = 𝟙
ST-Moduli-≤ (×* st₁ st₂) (a₁ , a₂) (b₁ , b₂) = ST-Moduli-≤ st₁ a₁ b₁ × ST-Moduli-≤ st₂ a₂ b₂
ST-Moduli-≤ (→* st) (aₙ , aₘₛ) (bₙ , bₘₛ) = (aₙ ≤ bₙ) × ST-Moduli-≤ st aₘₛ bₘₛ

-- Thus, there is a 'minimum' for each exactness type
least-mod : (st : ST) → ST-Moduli st
least-mod (𝔽* _ _) = *
least-mod (×* st₁ st₂) = least-mod st₁ , least-mod st₂
least-mod (→* st) = 0 , least-mod st

-- This gives the maximum of two constructions of an exactness type
max-mod : (st : ST) → (a b : ST-Moduli st) → ST-Moduli st
max-mod (𝔽* _ _) * * = *
max-mod (×* st₁ st₂) (a₁ , a₂) (b₁ , b₂) = max-mod st₁ a₁ b₁ , max-mod st₂ a₂ b₂
max-mod (→* st) (aₙ , aₘ) (bₙ , bₘ) = maxℕ aₙ bₙ , max-mod st aₘ bₘ

≤-max-mod : (st : ST) → ∀ a b x y → ST-Moduli-≤ st a b → ST-Moduli-≤ st x y
                 → ST-Moduli-≤ st (max-mod st a x) (max-mod st b y)
≤-max-mod (𝔽* _ _) * * * * * * = *
≤-max-mod (×* st₁ st₂) (a₁ , a₂) (b₁ , b₂) (x₁ , x₂) (y₁ , y₂) (a<b₁ , a<b₂) (x<y₁ , x<y₂)
              = ≤-max-mod st₁ a₁ b₁ x₁ y₁ a<b₁ x<y₁ , ≤-max-mod st₂ a₂ b₂ x₂ y₂ a<b₂ x<y₂
≤-max-mod (→* st) (a₁ , a₂) (b₁ , b₂) (x₁ , x₂) (y₁ , y₂) (a<b₁ , a<b₂) (x<y₁ , x<y₂)
             = ≤-max' a₁ b₁ x₁ y₁ a<b₁ x<y₁ , ≤-max-mod st a₂ b₂ x₂ y₂ a<b₂ x<y₂

-- If a and b are equal with precision (max-mod st m₁ m₂), then they are also equal with precision m₁ or m₂
ST-≈-max : (st : ST) (a b : ST-Type st) (m₁ m₂ : ST-Moduli st)
                   → ST-≈ st a b (max-mod st m₁ m₂) → ST-≈ st a b m₁ × ST-≈ st a b m₂
ST-≈-max (𝔽* _ _) _ _ _ _ a≈b = a≈b , a≈b
ST-≈-max (×* st₁ st₂) (a₁ , a₂) (b₁ , b₂) (m₁ , m₂) (l₁ , l₂) (a≈b₁ , a≈b₂)
  = (pr₁ IH₁ , pr₁ IH₂) , (pr₂ IH₁ , pr₂ IH₂) where
         IH₁ = ST-≈-max st₁ a₁ b₁ m₁ l₁ a≈b₁
         IH₂ = ST-≈-max st₂ a₂ b₂ m₂ l₂ a≈b₂
ST-≈-max (→* st) a b (mₙ , mₘ) (lₙ , lₘ) a≈b
  = (λ n n<mₙ → pr₁ (ST-≈-max st (a n) (b n) mₘ lₘ (a≈b n (<-max n mₙ lₙ (inl n<mₙ)))))
    , (λ n n<lₙ → pr₂ (ST-≈-max st (a n) (b n) mₘ lₘ (a≈b n (<-max n mₙ lₙ (inr n<lₙ)))))

-- Given two constructs of an S-Type and a precision, it is decidable whether they are equal with this precision
ST-≈-dec : (st : ST) (a b : ST-Type st) (m : ST-Moduli st) → decidable (ST-≈ st a b m)
ST-≈-dec (𝔽* n _) a b * = 𝔽-discrete n a b
ST-≈-dec (×* st₁ st₂) (a₁ , a₂) (b₁ , b₂) (m₁ , m₂)
  = ×-preserves-decidability (ST-≈-dec st₁ a₁ b₁ m₁) (ST-≈-dec st₂ a₂ b₂ m₂)
ST-≈-dec (→* st) a b (n , m) = γ a b n m where
  γ : (a b : ST-Type (→* st)) (n : ℕ) (m : ST-Moduli st) → decidable (ST-≈ (→* st) a b (n , m))
  γ a b zero m = inl (λ _ ())
  γ a b (succ n) m = Cases (γ a b n m)
                                 (λ γn → Cases (ST-≈-dec st (a n) (b n) m)
                                                         (λ γsn → inl (prove γn γsn))
                                                         (λ ¬γsn → inr (λ Pk → ¬γsn (Pk n (<-succ n)))))
                                 (λ ¬γn → inr (λ Pn → ¬γn (λ k k<n → Pn k (<-trans k n (succ n) k<n (<-succ n))))) where
      prove : ((k : ℕ) → k < n → ST-≈ st (a k) (b k) m) → ST-≈ st (a n) (b n) m
                → (k : ℕ) → k < succ n → ST-≈ st (a k) (b k) m
      prove Pk Pn k k<n
        = Cases (<-split k n k<n) (Pk k) (λ k≡n → transport (λ - → ST-≈ st (a -) (b -) m) (k≡n ⁻¹) Pn)

-- Given continuous functions f and g, the predicate of whether
-- (f x) and (g x) are equivalent with some preicision is continuous
ST-≈-f-con : (st₁ st₂ : ST) (n : ST-Moduli st₂)
                   (f g : ST-Type st₁ → ST-Type st₂) (cᶠ : continuous² st₁ st₂ f) (cᵍ : continuous² st₁ st₂ g)
                  → continuous st₁ (λ x → ST-≈ st₂ (f x) (g x) n)
ST-≈-f-con st₁ st₂ n f g cᶠ cᵍ = m , λ α β α≈β → γ α β α≈β , γ β α (ST-≈-sym st₁ m α β α≈β) where
    m : ST-Moduli st₁
    m = max-mod st₁ (pr₁ (cᶠ n)) (pr₁ (cᵍ n))
    γ : (α β : ST-Type st₁) → ST-≈ st₁ α β m → ST-≈ st₂ (f α) (g α) n → ST-≈ st₂ (f β) (g β) n
    γ α β α≈β fα≈gα = ST-≈-trans st₂ n (f β) (f α) (g β) (pr₂ (cᶠ n) β α α≈βᶠ)
                                    (ST-≈-trans st₂ n (f α) (g α) (g β) fα≈gα (pr₂ (cᵍ n) α β α≈βᵍ)) where
      α≈βᶠ : ST-≈ st₁ β α (pr₁ (cᶠ n))
      α≈βᶠ = pr₁ (ST-≈-max st₁ β α (pr₁ (cᶠ n)) (pr₁ (cᵍ n)) (ST-≈-sym st₁ m α β α≈β))
      α≈βᵍ : ST-≈ st₁ α β (pr₁ (cᵍ n))
      α≈βᵍ = pr₂ (ST-≈-max st₁ α β (pr₁ (cᶠ n)) (pr₁ (cᵍ n)) α≈β)

{- (5) Finally, the S-Types 𝕌 and 𝕀, which respectively realise the intervals [0,1] and [-1,1] -}

𝕌* = →* (𝔽* 2 λ ())
𝕌 = ST-Type 𝕌*
𝕀* = →* (𝔽* 3 λ ())
𝕀 = ST-Type 𝕀*

0₂ : 𝕌
0₂ _ = ⁰

0₃ : 𝕀
0₃ _ = ₀
