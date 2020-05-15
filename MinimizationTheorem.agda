{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (𝟚;₀;₁)
open import Prelude
open import SearchableTypes
open import UIOrder
open import TheoremsBase
open import DecidableAndDetachable
open import SearchableVariants
open import InfSequence
open import NaturalsOrder

module MinimizationTheorem where

head-tail-f-refl : (st₁ st₂ : ST) → (f : ST-Type (→* st₁) → ST-Type st₂)
                       → (m : ST-Moduli st₂) (n : ST-Moduli (→* st₁)) → uc-mod² (→* st₁) st₂ f m n
                       → (s : ST-Type (→* st₁)) → ST-≈ (st₂) (f s) (f (head s :: tail s)) m
head-tail-f-refl st₁ st₂ f m n ϕ s = ϕ s (head s :: tail s) (head-tail-refl st₁ s n)

tail-decrease-mod² : (st₁ st₂ : ST) (f : 𝕊 (ST-Type st₁) → ST-Type st₂)
                                → (m : ℕ) (ms : ST-Moduli st₁) (n : ST-Moduli st₂)
                                → uc-mod² (→* st₁) st₂ f n (succ m , ms)
                                → (g : 𝕊 (ST-Type st₁) → ST-Type st₁)
                                → uc-mod² (→* st₁) st₁ g ms (m , ms)
                                → uc-mod² (→* st₁) st₂ (λ s → f (g s :: s)) n (m , ms)
tail-decrease-mod² st₁ st₂ f m ms n ϕᶠ g ϕᵍ α β α≈β
  = ϕᶠ (g α :: α) (g β :: β) (seq-build-eta st₁ (g α) (g β) α β m ms (ϕᵍ α β α≈β) α≈β)

minimizer : ST → 𝓤₀ ̇
minimizer st = (f : ST-Type st → 𝕌) (m : ℕ)
                          (n : ST-Moduli st) → uc-mod² st 𝕌* f (m , *) n
                          → Σ \x₀ → (∀ x → (f x₀ ≤ᵁ f x) m)

continuous-minimizer : ∀ st → minimizer st → 𝓤₀ ̇
continuous-minimizer st min = (f g : ST-Type st → 𝕌)
                                                     (m : ℕ) (n : ST-Moduli st)
                                                     (ϕᶠ : uc-mod² st 𝕌* f (m , *) n) (ϕᵍ : uc-mod² st 𝕌* g (m , *) n)
                                                     (f≈g : ST-≈ᶠ² st 𝕌* f g n (m , *))
                                                     → ST-≈ st (pr₁ (min f m n ϕᶠ)) (pr₁ (min g m n ϕᵍ)) n

finite-min : (n : ℕ) → Σ (continuous-minimizer (𝔽* (succ n) (λ ())))
finite-min 0 = 𝓜 , C where
  𝓜 : minimizer (𝔽* 1 λ ())
  𝓜 f m _ _ = * , γ where
    γ : ∀ x → (f * ≤ᵁ f x) m
    γ * = ≤ᵁ-refl m (f *)
  C : continuous-minimizer (𝔽* 1 λ ()) 𝓜
  C _ _ _ _ _ _ _ = refl
finite-min (succ n) = 𝓜 , C where
  f-cont : (f : 𝔽 (succ n) + 𝟙 → 𝕌) → ∀ m → uc-mod² (𝔽* (succ n) (λ ())) 𝕌* (λ x → f (inl x)) (m , *) *
  f-cont f m = (pr₂ (all-𝔽-funs-continuous (succ n) (λ ()) 𝕌* (λ x → f (inl x)) (m , *)))
  ihₓ→ : ∀ f m → Σ (λ x₀ → ∀ x → (f (inl x₀) ≤ᵁ f (inl x)) m)
  ihₓ→ f m = pr₁ (finite-min n) (λ x → f (inl x)) m * (f-cont f m)
  xᵢₕ→ : ∀ f m → 𝔽 (succ n)
  xᵢₕ→ f m = pr₁ (ihₓ→ f m)
  γᵢₕ→ : ∀ f m → ∀ x → (f (inl (pr₁ (ihₓ→ f m))) ≤ᵁ f (inl x)) m
  γᵢₕ→ f m = pr₂ (ihₓ→ f m)
  d*→ : (f : 𝔽 (succ n) + 𝟙 → 𝕌) → ∀ m → decidable ((f (inl (xᵢₕ→ f m)) ≤ᵁ f (inr *)) m)
  d*→ f m = ≤ᵁ-decidable (f (inl (xᵢₕ→ f m))) (f (inr *)) m
  x₀γ : (f : 𝔽 (succ n) + 𝟙 → 𝕌) → ∀ m → decidable ((f (inl (xᵢₕ→ f m)) ≤ᵁ f (inr *)) m) 
         → Σ (λ x₀ → ∀ x → (f x₀ ≤ᵁ f x) m)
  x₀γ f m (inl fx≤f*) = inl (xᵢₕ→ f m) , γ where
    γ : ∀ x → (f (inl (xᵢₕ→ f m)) ≤ᵁ f x) m
    γ (inl x) = γᵢₕ→ f m x
    γ (inr *) = fx≤f*
  x₀γ f m (inr ¬fx≤f*) = inr * , γ where
    γ : ∀ x → (f (inr *) ≤ᵁ f x) m
    γ (inl x) = ≤ᵁ-trans m (f (inr *)) (f (inl (xᵢₕ→ f m))) (f (inl x)) γ' ((γᵢₕ→ f m) x) where
      γ' : (f (inr *) ≤ᵁ f (inl (xᵢₕ→ f m))) m
      γ' = Cases (≤ᵁ-con m (f (inl (xᵢₕ→ f m))) (f (inr *))) (λ fx≤f* → 𝟘-elim (¬fx≤f* fx≤f*)) id
    γ (inr *) = inr λ _ _ → refl
  𝓜 : minimizer (𝔽* (succ (succ n)) λ ())
  𝓜 f m * ϕ = x₀γ f m (d*→ f m)
  C : continuous-minimizer (𝔽* (succ (succ n)) λ ()) 𝓜
  C f g m * ϕᶠ ϕᵍ f≈g = δ (d*→ f m) (d*→ g m) where
    δᵢₕ = pr₂ (finite-min n) (λ x → f (inl x)) (λ x → g (inl x)) m * (f-cont f m) (f-cont g m)
                   (λ x y x≡y → f≈g (inl x) (inl y) (ap inl x≡y))
    δ : (d₁ : decidable (((λ z → f (inl (xᵢₕ→ f m)) z) ≤ᵁ (λ z → f ₁ z)) m))
       → (d₂ : decidable (((λ z → g (inl (xᵢₕ→ g m)) z) ≤ᵁ (λ z → g ₁ z)) m))
       → pr₁ (x₀γ f m d₁) ≡ pr₁ (x₀γ g m d₂)
    δ (inl fx≤f*) (inl gx≤g*) = ap inl δᵢₕ
    δ (inl fx≤f*) (inr ¬gx≤g*) = 𝟘-elim (¬gx≤g* (≤ᵁ-trans m (g (inl (xᵢₕ→ g m))) (f (inl (xᵢₕ→ f m))) (g (inr *))
                                                   (inr (λ n n<m → f≈g (inl (xᵢₕ→ f m)) (inl (xᵢₕ→ g m)) (ap inl δᵢₕ) n n<m ⁻¹))
                                                   (≤ᵁ-trans m (f (inl (xᵢₕ→ f m))) (f (inr *)) (g (inr *)) fx≤f*
                                                   (inr (f≈g (inr *) (inr *) refl)))))
    δ (inr ¬fx≤f*) (inl gx≤g*) = 𝟘-elim (¬fx≤f* (≤ᵁ-trans m (f (inl (xᵢₕ→ f m))) (g (inl (xᵢₕ→ g m))) (f (inr *))
                                                   (inr (f≈g (inl (xᵢₕ→ f m)) (inl (xᵢₕ→ g m)) (ap inl δᵢₕ)))
                                                   (≤ᵁ-trans m (g (inl (xᵢₕ→ g m))) (g (inr *)) (f (inr *)) gx≤g*
                                                   (inr (λ n n<m → f≈g (inr *) (inr *) refl n n<m ⁻¹)))))
    δ (inr ¬fx≤f*) (inr ¬gx≤g*) = refl

product-min : (st₁ st₂ : ST) → Σ (continuous-minimizer st₁) → Σ (continuous-minimizer st₂)
                    → Σ (continuous-minimizer (×* st₁ st₂))
product-min st₁ st₂ IHˣ IHʸ = 𝓜 , C where
  ihˣ→ : ∀ f y m → (n : ST-Moduli (×* st₁ st₂)) → uc-mod² (×* st₁ st₂) 𝕌* f (m , *) n
           → Σ (λ x₀ → ∀ x → (f (x₀ , y) ≤ᵁ f (x , y)) m)
  ihˣ→ f y m (n₁ , n₂) ϕ = pr₁ IHˣ (λ x → f (x , y)) m n₁ (λ α β α≈β → ϕ (α , y) (β , y) (α≈β , ST-≈-refl st₂ n₂ y))
  x₀→ : ∀ f y m → (n : ST-Moduli (×* st₁ st₂)) → uc-mod² (×* st₁ st₂) 𝕌* f (m , *) n
           → ST-Type st₁
  x₀→ f y m n ϕ = pr₁ (ihˣ→ f y m n ϕ)
  δˣ→  : ∀ f m → (n : ST-Moduli (×* st₁ st₂)) → (ϕ : uc-mod² (×* st₁ st₂) 𝕌* f (m , *) n)
           → (α β : ST-Type st₂) → ST-≈ st₂ α β (pr₂ n)
           → ST-≈ st₁ (x₀→ f α m n ϕ) (x₀→ f β m n ϕ) (pr₁ n)
  δˣ→ f m (n₁ , n₂) ϕ α β α≈β = pr₂ IHˣ (λ x → f (x , α)) (λ x → f (x , β)) m n₁
                                                 (λ α₁ β₁ α≈β₁ → ϕ (α₁ , α) (β₁ , α) (α≈β₁ , ST-≈-refl st₂ n₂ α))
                                                 (λ α₁ β₁ α≈β₁ → ϕ (α₁ , β) (β₁ , β) (α≈β₁ , ST-≈-refl st₂ n₂ β))
                                                 (λ x y x≈y → ϕ (x , α) (y , β) (x≈y , α≈β))
  ihʸ→ : ∀ f m → (n : ST-Moduli (×* st₁ st₂)) → (ϕ : uc-mod² (×* st₁ st₂) 𝕌* f (m , *) n)
           → Σ (λ y₀ → ∀ y → (f (x₀→ f y₀ m (pr₁ n , pr₂ n) ϕ , y₀) ≤ᵁ f (x₀→ f y m (pr₁ n , pr₂ n) ϕ , y)) m)
  ihʸ→ f m (n₁ , n₂) ϕ = pr₁ IHʸ (λ y → f (x₀→ f y m (n₁ , n₂) ϕ , y)) m n₂
                                      (λ α β α≈β → ϕ (x₀→ f α m (n₁ , n₂) ϕ , α) (x₀→ f β m (n₁ , n₂) ϕ , β)
                                      ((δˣ→ f m (n₁ , n₂) ϕ α β α≈β) , α≈β))
  y₀→ : ∀ f m → (n : ST-Moduli (×* st₁ st₂)) → (ϕ : uc-mod² (×* st₁ st₂) 𝕌* f (m , *) n)
           → ST-Type st₂
  y₀→ f m n ϕ = pr₁ (ihʸ→ f m n ϕ)
  𝓜 : minimizer (×* st₁ st₂)
  𝓜 f m n ϕ = (x₀ y₀ , y₀) , γ where
    y₀ = y₀→ f m n ϕ
    x₀ = λ y → x₀→ f y m n ϕ
    γˣ : ∀ y x → (f (x₀ y , y) ≤ᵁ f (x , y)) m
    γˣ = λ y → pr₂ (ihˣ→ f y m n ϕ)
    γʸ : ∀ y → (f (x₀ y₀ , y₀) ≤ᵁ f (x₀ y , y)) m
    γʸ = pr₂ (ihʸ→ f m n ϕ)
    γ : ∀ xy → (f (x₀ y₀ , y₀) ≤ᵁ f xy) m
    γ (x , y) = ≤ᵁ-trans m (f (x₀ y₀ , y₀)) (f (x₀ y , y)) (f (x , y)) (γʸ y) (γˣ y x)
  C : continuous-minimizer (×* st₁ st₂) 𝓜
  C f g m (n₁ , n₂) ϕᶠ ϕᵍ f≈g = δˣ , δʸ where
    f-x₀ = λ y → x₀→ f y m (n₁ , n₂) ϕᶠ
    g-x₀ = λ y → x₀→ g y m (n₁ , n₂) ϕᵍ
    f-y₀ = y₀→ f m (n₁ , n₂) ϕᶠ
    g-y₀ = y₀→ g m (n₁ , n₂) ϕᵍ
    δʸ : ST-≈ st₂ f-y₀ g-y₀ n₂
    δʸ = pr₂ IHʸ (λ y → f (f-x₀ y , y)) (λ y → g (g-x₀ y , y)) m n₂
            (λ α β α≈β → ϕᶠ (x₀→ f α m (n₁ , n₂) ϕᶠ , α) (x₀→ f β m (n₁ , n₂) ϕᶠ , β) (δˣ→ f m (n₁ , n₂) ϕᶠ α β α≈β , α≈β))
            (λ α β α≈β → ϕᵍ (x₀→ g α m (n₁ , n₂) ϕᵍ , α) (x₀→ g β m (n₁ , n₂) ϕᵍ , β) (δˣ→ g m (n₁ , n₂) ϕᵍ α β α≈β , α≈β))
            (λ α β α≈β → f≈g (f-x₀ α , α) (g-x₀ β , β)
                                  (pr₂ IHˣ (λ x → f (x , α)) (λ x → g (x , β)) m n₁
                                  (λ α₁ β₁ α≈β₁ → ϕᶠ (α₁ , α) (β₁ , α) (α≈β₁ , ST-≈-refl st₂ n₂ α))
                                  (λ α₁ β₁ α≈β₁ → ϕᵍ (α₁ , β) (β₁ , β) (α≈β₁ , ST-≈-refl st₂ n₂ β))
                                  (λ α₁ β₁ α≈β₁ → f≈g (α₁ , α) (β₁ , β) (α≈β₁ , α≈β)) , α≈β))
    δˣ : ST-≈ st₁ (f-x₀ f-y₀) (g-x₀ g-y₀) n₁
    δˣ = pr₂ IHˣ (λ x → f (x , f-y₀)) (λ x → g (x , g-y₀)) m n₁
            (λ α β α≈β → ϕᶠ (α , f-y₀) (β , f-y₀) (α≈β , ST-≈-refl st₂ n₂ f-y₀))
            (λ α β α≈β → ϕᵍ (α , g-y₀) (β , g-y₀) (α≈β , ST-≈-refl st₂ n₂ g-y₀))
            (λ x y x≈y → f≈g (x , f-y₀) (y , g-y₀) (x≈y , δʸ))

sequence-min : ∀ st → Σ (continuous-minimizer st)
                           → Σ \(min : (f : ST-Type (→* st) → 𝕌) (m : ℕ)
                                          → (n : ℕ) (ns : ST-Moduli st)
                                          → uc-mod² (→* st) 𝕌* f (m , *) (n , ns)
                                          → Σ \xs₀ → ∀ xs → (f xs₀ ≤ᵁ f xs) m)
                           → (f g : ST-Type (→* st) → 𝕌) (m : ℕ)
                                           (n : ℕ) (ns : ST-Moduli st)
                                           (ϕᶠ : uc-mod² (→* st) 𝕌* f (m , *) (n , ns))
                                           (ϕᵍ : uc-mod² (→* st) 𝕌* g (m , *) (n , ns))
                                           (f≈g : ST-≈ᶠ² (→* st) 𝕌* f g (n , ns) (m , *))
                                          → ST-≈ (→* st) (pr₁ (min f m n ns ϕᶠ)) (pr₁ (min g m n ns ϕᵍ)) (n , ns)
sequence-min st IHˣ = 𝓜 , C where
  𝓜 : (f : ST-Type (→* st) → 𝕌) (m n : ℕ) (ns : ST-Moduli st)
         → uc-mod² (→* st) 𝕌* f (m , *) (n , ns)
         → Σ (λ xs₀ → (xs : ℕ → ST-Type st) → (f xs₀ ≤ᵁ f xs) m)
         
  ihˣ→ : ∀ f s m → (n : ℕ) (ns : ST-Moduli st) → uc-mod² (→* st) 𝕌* f (m , *) (succ n , ns)
         → Σ (λ x₀ → ∀ x → (f (x₀ :: s) ≤ᵁ f (x :: s)) m)
  ihˣ→ f s m n ns ϕ = pr₁ IHˣ (λ z z₁ → f (z :: s) z₁) m ns
                                 (λ α β α≈β → ϕ (α :: s) (β :: s) (seq-build-eta st α β s s n ns α≈β (ST-≈-refl (→* st) (n , ns) s)))
  x₀→ : ∀ f s m → (n : ℕ) (ns : ST-Moduli st) → uc-mod² (→* st) 𝕌* f (m , *) (succ n , ns)
         → ST-Type st
  x₀→ f s m n ns ϕ = pr₁ (ihˣ→ f s m n ns ϕ)
  ihˢ→ : ∀ f m → (n : ℕ) (ns : ST-Moduli st) → (ϕ : uc-mod² (→* st) 𝕌* f (m , *) (succ n , ns))
         → Σ (λ s₀ → ∀ s → (f (x₀→ f s₀ m n ns ϕ :: s₀) ≤ᵁ f (x₀→ f s m n ns ϕ :: s)) m)
  ihˢ→ f m n ns ϕ = 𝓜 (λ s → f (x₀→ f s m n ns ϕ :: s)) m n ns (tail-decrease-mod² st 𝕌* f n ns (m , *) ϕ
                                     (λ s → x₀→ f s m n ns ϕ)
                                     (λ α β α≈β → pr₂ IHˣ (λ x → f (x :: α)) (λ x → f (x :: β)) m ns
                                        (λ α₁ β₁ α≈β₁ → ϕ (α₁ :: α) (β₁ :: α)
                                        (seq-build-eta st α₁ β₁ α α n ns α≈β₁ (ST-≈-refl (→* st) (n , ns) α)))
                                        (λ α₁ β₁ α≈β₁ → ϕ (α₁ :: β) (β₁ :: β)
                                        (seq-build-eta st α₁ β₁ β β n ns α≈β₁ (ST-≈-refl (→* st) (n , ns) β)))
                                        (λ α₁ β₁ α≈β₁ → ϕ (α₁ :: α) (β₁ :: β) (seq-build-eta st α₁ β₁ α β n ns α≈β₁ α≈β))))
  s₀→ : ∀ f m → (n : ℕ) (ns : ST-Moduli st) → (ϕ : uc-mod² (→* st) 𝕌* f (m , *) (succ n , ns))
         → 𝕊 (ST-Type st)
  s₀→ f m n ns ϕ = pr₁ (ihˢ→ f m n ns ϕ)
  𝓜 f m zero ns ϕ = xs₀ , γ where
    xs₀ : ℕ → ST-Type st
    xs₀ = λ _ → pr₁ (pr₁ IHˣ (λ x → f (λ _ → x)) m ns (λ α β _ → ϕ (λ _ → α) (λ _ → β) (λ _ ())))
    γ : ∀ xs → (f xs₀ ≤ᵁ f xs) m
    γ xs = inr (ϕ xs₀ xs (λ _ ()))
  𝓜 f m (succ n) ns ϕ = x₀ s₀ :: s₀ , γ where
    x₀ = λ s → x₀→ f s m n ns ϕ
    s₀ = s₀→ f m n ns ϕ
    γˣ = λ s → pr₂ (ihˣ→ f s m n ns ϕ)
    γʸ = pr₂ (ihˢ→ f m n ns ϕ)
    γ : ∀ xs → (f (x₀ s₀ :: s₀) ≤ᵁ f xs) m
    γ xs = ≤ᵁ-trans m (f (x₀ s₀ :: s₀)) (f (x₀ (tail xs) :: tail xs)) (f xs) (γʸ (tail xs))
              (≤ᵁ-trans m (f (x₀ (tail xs) :: tail xs)) (f (head xs :: tail xs)) (f xs) (γˣ (tail xs) (head xs))
              (inr (ST-≈-sym 𝕌* (m , *) (f xs) (f (head xs :: tail xs))
                 (head-tail-f-refl st 𝕌* f (m , *) (succ n , ns) ϕ xs))))
  C : (f g : ST-Type (→* st) → 𝕌) (m n : ℕ) (ns : ST-Moduli st)
        (ϕᶠ : uc-mod² (→* st) 𝕌* f (m , *) (n , ns))
        (ϕᵍ : uc-mod² (→* st) 𝕌* g (m , *) (n , ns)) →
        ST-≈ᶠ² (→* st) 𝕌* f g (n , ns) (m , *) →
        ST-≈ (→* st) (pr₁ (𝓜 f m n ns ϕᶠ)) (pr₁ (𝓜 g m n ns ϕᵍ)) (n , ns)
  C f g m 0 ns ϕᶠ ϕᵍ f≈g = λ _ ()
  C f g m (succ n) ns ϕᶠ ϕᵍ f≈g = seq-build-eta st (f-x₀ f-s₀) (g-x₀ g-s₀) f-s₀ g-s₀ n ns δˣ δˢ where
    f-x₀ = λ y → x₀→ f y m n ns ϕᶠ
    g-x₀ = λ y → x₀→ g y m n ns ϕᵍ
    f-s₀ = s₀→ f m n ns ϕᶠ
    g-s₀ = s₀→ g m n ns ϕᵍ
    δˢ : ST-≈ (→* st) f-s₀ g-s₀ (n , ns) -- clean up this one
    δˢ = C (λ s → f (f-x₀ s :: s)) (λ s → g (g-x₀ s :: s)) m n ns _ _
            (λ α β α≈β → f≈g (f-x₀ α :: α) (g-x₀ β :: β) (seq-build-eta st (f-x₀ α) (g-x₀ β) α β n ns
                                  (pr₂ IHˣ (λ z → f (z :: α)) (λ z → g (z :: β)) m ns
                                  (λ α₁ β₁ α≈β₁
                                  → ϕᶠ (α₁ :: α) (β₁ :: α) (seq-build-eta st α₁ β₁ α α n ns α≈β₁ (ST-≈-refl (→* st) (n , ns) α))) 
                                  (λ α₁ β₁ α≈β₁
                                  → ϕᵍ (α₁ :: β) (β₁ :: β) (seq-build-eta st α₁ β₁ β β n ns α≈β₁ (ST-≈-refl (→* st) (n , ns) β)))
                                  λ α₁ β₁ α≈β₁ → f≈g (α₁ :: α) (β₁ :: β) (seq-build-eta st α₁ β₁ α β n ns α≈β₁ α≈β)) α≈β))
    δˣ : ST-≈ st (f-x₀ f-s₀) (g-x₀ g-s₀) ns
    δˣ = pr₂ IHˣ (λ x → f (x :: f-s₀)) (λ x → g (x :: g-s₀)) m ns
               (λ α β α≈β → ϕᶠ (α :: f-s₀) (β :: f-s₀) (seq-build-eta st α β f-s₀ f-s₀ n ns α≈β (ST-≈-refl (→* st) (n , ns) f-s₀)))
               (λ α β α≈β → ϕᵍ (α :: g-s₀) (β :: g-s₀) (seq-build-eta st α β g-s₀ g-s₀ n ns α≈β (ST-≈-refl (→* st) (n , ns) g-s₀)))
               (λ α β α≈β → f≈g (α :: f-s₀) (β :: g-s₀) (seq-build-eta st α β f-s₀ g-s₀ n ns α≈β δˢ))

minimization-general : ∀ st → Σ (continuous-minimizer st)
minimization-general (𝔽* zero z) = 𝟘-elim (z refl)
minimization-general (𝔽* (succ n) _) = finite-min n
minimization-general (×* st₁ st₂) = product-min st₁ st₂ (minimization-general st₁) (minimization-general st₂)
minimization-general (→* st)
  = (λ f m n ϕ → pr₁ (sequence-min st (minimization-general st)) f m (pr₁ n) (pr₂ n) ϕ)
   , λ f g m n ϕᶠ ϕᵍ f≈g → pr₂ (sequence-min st (minimization-general st)) f g m (pr₁ n) (pr₂ n) ϕᶠ ϕᵍ f≈g

argmin : (st : ST) (f : ST-Type st → 𝕌) (m : ℕ)
               (n : ST-Moduli st) → uc-mod² st 𝕌* f (m , *) n
               → Σ \x₀ → (∀ x → (f x₀ ≤ᵁ f x) m)
argmin st = pr₁ (minimization-general st)

minimization-theorem : (st st₁ st₂ : ST) (m : ℕ) (M : ST-Type st → Y st₁ st₂) (Ω : Y st₁ st₂)
                                       → (Φ : Y st₁ st₂ → Y st₁ st₂ → 𝕌)
                                       → continuousᴹ st st₁ st₂ M → continuousᴸ st₁ st₂ Φ
                                       → Σ \k₀ → (∀ k → (Φ Ω (M k₀) ≤ᵁ Φ Ω (M k)) m)
minimization-theorem st st₁ st₂ m M Ω Φ cᴹ cᴸ = argmin st (λ x → Φ Ω (M x)) m n γ where
  n : ST-Moduli st
  n = pr₁ (cᴹ (pr₁ (cᴸ (m , *))))
  γ : (α β : ST-Type st) →  ST-≈ st α β n → ST-≈ 𝕌* (Φ Ω (M α)) (Φ Ω (M β)) (m , *)
  γ α β α≈β = pr₂ (cᴸ (m , *)) (M α) (M β) (pr₂ (cᴹ (pr₁ (cᴸ (m , *)))) α β α≈β) Ω
