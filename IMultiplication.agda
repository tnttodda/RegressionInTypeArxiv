{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (𝟚;₀;₁)
open import InfSequence
open import Prelude
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import SearchableTypes
open import NaturalsOrder
open import UIOrder
open import IAddition

module IMultiplication where

-- This file defines the multiplication operator on the 𝕀 representation, and provides a continuity proof

{- (1) Multiplication and auxiliary operators -}

-- The operators are all defined equivalent to those found in
-- https://www.cs.bham.ac.uk/~mhe/papers/fun2011.lhs (Escardo11)

-- First, we define the "digitMul" operator, which takes a construction of 𝟛 and appropriately multiplies a construction of 𝕀 by -1, 0 or 1

compl₃ : 𝟛 → 𝟛
compl₃ ₋₁ = ₁
compl₃  ₀ = ₀
compl₃  ₁ = ₋₁

compl' : 𝕀 → 𝕀
compl' x n = compl₃ (x n)

digitMul : 𝟛 → 𝕀 → 𝕀
digitMul ₋₁ x = compl' x
digitMul  ₀ x = 0₃
digitMul  ₁ x = x

-- Then, we define the p, p', p'' and q operators (named identically to those found in Escardo11)

_*𝟛_ : 𝟛 → 𝟛 → 𝟛
₋₁ *𝟛 ₋₁ = ₁
₋₁ *𝟛 ₀ = ₀
₋₁ *𝟛 ₁ = ₋₁
₀ *𝟛 ₋₁ = ₀
₀ *𝟛 ₀ = ₀
₀ *𝟛 ₁ = ₀
₁ *𝟛 ₋₁ = ₋₁
₁ *𝟛 ₀ = ₀
₁ *𝟛 ₁ = ₁

p p' p'' : 𝕀 × 𝕀 → 𝕀
p (a , b) = mid (p' (a , b)) (p'' (a , b))
p' (a , b) 0 = (a 0 *𝟛 b 1)
p' (a , b) (succ n) = mid (digitMul (b 1) x) (digitMul (a 1) y) n where
  x = tail (tail a)
  y = tail (tail b) 
p'' (a , b) = mid (digitMul (b 0) x) (digitMul (a 0) y) where
  x = tail (tail a)
  y = tail (tail b) 

-- The 'q' operator is defined slightly differently (it has an additional parameter in ℕ that will be managed
-- in the multiplication function) to account for the Agda termination checker

q : ℕ → 𝕀 × 𝕀 → 𝕀
q k (a , b) 0 = (a 0 *𝟛 b 0)
q k (a , b) 1 = (a 1 *𝟛 b 0)
q k (a , b) 2 = (a 1 *𝟛 b 1)
q 0 (a , b) (succ (succ (succ n))) = ₀
q (succ k) (a , b) (succ (succ (succ n))) = mid (p (x , y)) (q k (x , y)) n where
  x = tail (tail a)
  y = tail (tail b)

-- Note here the use of 'n' in the q operator
_*𝕀_ : 𝕀 → 𝕀 → 𝕀
(a *𝕀 b) n = mid (p (a , b)) (q n (a , b)) n

-- The square function is defined as one would expect
_² : 𝕀 → 𝕀
x ² = x *𝕀 x

{- (2) Proving the above operators are continuous -}

-- Proving tail and (tail ∘ tail) is continuous is essential but trivial
tl-continuous : continuous² 𝕀* 𝕀* tail
tl-continuous (n , *) = (succ n , *) , (λ α β α≈β k k<n → α≈β (succ k) k<n)

tltl-continuous : continuous² 𝕀* 𝕀* (tail ∘ tail)
tltl-continuous = ∘-continuous 𝕀* 𝕀* 𝕀* tail tail tl-continuous tl-continuous

tltl-continuous' : ∀ n → uc-mod² 𝕀* 𝕀* (tail ∘ tail) n (succ (succ (pr₁ n)) , *)
tltl-continuous' (n , *) = pr₂ (tltl-continuous (n , *))

-- digitMul is clearly continuous, as it is continuous no matter what (b : 𝟛) is input

const-continuous : (st₁ st₂ : ST) (x : ST-Type st₂) → continuous² st₁ st₂ (λ _ → x)
const-continuous st₁ st₂ x n = least-mod st₁ , (λ _ _ _ → ST-≈-refl st₂ n x)

compl₃≡ : (a b : 𝟛) → a ≡ b → compl₃ a ≡ compl₃ b
compl₃≡ ₋₁ ₋₁ refl = refl
compl₃≡   ₀   ₀ refl = refl
compl₃≡   ₁   ₁ refl = refl

compl-continuous : continuous² 𝕀* 𝕀* compl'
compl-continuous n = n , (λ α β α≈β n n<m → compl₃≡ (α n) (β n) (α≈β n n<m))

digitMul-continuous : (b : 𝟛) → continuous² 𝕀* 𝕀* (digitMul b)
digitMul-continuous ₋₁ = compl-continuous
digitMul-continuous   ₀ = const-continuous 𝕀* 𝕀* (λ _ → ₀)
digitMul-continuous   ₁ = id-continuous 𝕀*

-- We require the following corollaries of digitMul being continuous further down
digitMul-continuous-weak : (b₁ b₂ : 𝟛) → b₁ ≡ b₂ → (n : ST-Moduli 𝕀*) → (α β : 𝕀)
                                          → ST-≈ 𝕀* α β n → ST-≈ 𝕀* (digitMul b₁ α) (digitMul b₂ β) n
digitMul-continuous-weak ₋₁ ₋₁ refl n = pr₂ (digitMul-continuous ₋₁ n)
digitMul-continuous-weak   ₀   ₀ refl n α β _ = pr₂ (digitMul-continuous ₀ n) α β (λ _ ())
digitMul-continuous-weak   ₁   ₁ refl n = pr₂ (digitMul-continuous ₁ n)

digitMul-continuous₁ : (a : ST-Type 𝕀* → ST-Type 𝕀*) → continuous² 𝕀* 𝕀* a 
                                      → ∀ k → continuous² (×* 𝕀* 𝕀*) 𝕀* (λ αβ → digitMul (pr₁ αβ k) (a (pr₂ αβ)))
digitMul-continuous₁ a a≈ k n = ((succ k , *) , pr₁ (a≈ n))
                                                , λ α β α≈β →
                                                digitMul-continuous-weak (pr₁ α k) (pr₁ β k)
                                                (pr₁ α≈β k (<-succ k)) n (a (pr₂ α)) (a (pr₂ β)) (pr₂ (a≈ n) (pr₂ α) (pr₂ β) (pr₂ α≈β))

digitMul-continuous₂ : (a : ST-Type 𝕀* → ST-Type 𝕀*) → continuous² 𝕀* 𝕀* a 
                                      → ∀ k → continuous² (×* 𝕀* 𝕀*) 𝕀* (λ αβ → digitMul (pr₂ αβ k) (a (pr₁ αβ)))
digitMul-continuous₂ a a≈ k n = ((pr₁ (a≈ n)) , (succ k , *))
                                                , (λ α β α≈β →
                                                digitMul-continuous-weak (pr₂ α k) (pr₂ β k)
                                                (pr₂ α≈β k (<-succ k)) n (a (pr₁ α)) (a (pr₁ β)) (pr₂ (a≈ n) (pr₁ α) (pr₁ β) (pr₁ α≈β)))

-- This general statement is used throughout the following proofs
-- It says that given a continuous binary function f, and two continuous functions g and h,
-- the function (λ x → f (g x , h x)) is also continuous
binary-continuous : (st₁ st₂ st₃ : ST) (f : ST-Type (×* st₂ st₂) → ST-Type st₃) → continuous² (×* st₂ st₂) st₃ f
                              → (g h : ST-Type st₁ → ST-Type st₂)
                              → continuous² st₁ st₂ g → continuous² st₁ st₂ h
                              → continuous² st₁ st₃ (λ αβ → f (g αβ , h αβ))
binary-continuous st₁ st₂ st₃ f f≈ g h g≈ h≈ n = m , γ where
  m₁ = pr₁ (pr₁ (f≈ n))
  m₂ = pr₂ (pr₁ (f≈ n))
  m = max-mod st₁ (pr₁ (g≈ m₁)) (pr₁ (h≈ m₂))
  γ : (α β : ST-Type st₁) → ST-≈ st₁ α β m → ST-≈ st₃ (f (g α , h α)) (f (g β , h β)) n
  γ α β α≈β = pr₂ (f≈ n) (g α , h α) (g β , h β) ((pr₂ (g≈ m₁) α β (pr₁ max≈)) , (pr₂ (h≈ m₂) α β (pr₂ max≈))) where
    max≈ = ST-≈-max st₁ α β (pr₁ (g≈ m₁)) (pr₁ (h≈ m₂)) α≈β

-- This general statement is used in the rest of the proofs, where the binary function is the 'mid' operator
-- mid was proven to be continuous in the file IAddition.agda
binary-continuous𝕀 = binary-continuous (×* 𝕀* 𝕀*) 𝕀* 𝕀*

-- This is just a simple corollary of the general statement and the continuity of digitMul and (tail ∘ tail)
p''-continuous : continuous² (×* 𝕀* 𝕀*) 𝕀* p''
p''-continuous = binary-continuous𝕀 (uncurry mid) mid-continuous
                            (λ αβ → digitMul (pr₂ αβ 0) (tail (tail (pr₁ αβ))))
                            (λ αβ → digitMul (pr₁ αβ 0) (tail (tail (pr₂ αβ))))
                            (digitMul-continuous₂ (λ ■ → tail (tail ■)) tltl-continuous 0)
                            (digitMul-continuous₁ (λ ■ → tail (tail ■)) tltl-continuous 0)

-- When computing the head of the output, the function has a trivial modulus of continuity
-- When computing other values of the output, the continuity is proved again by using the general statement
p'-continuous : continuous² (×* 𝕀* 𝕀*) 𝕀* p' 
p'-continuous n = m n , γ n where
  p'-continuous-n-above-0 : continuous² (×* 𝕀* 𝕀*) 𝕀*
                                              (λ αβ → uncurry mid (digitMul (pr₂ αβ 1) (tail (tail (pr₁ αβ)))
                                                                             , digitMul (pr₁ αβ 1) (tail (tail (pr₂ αβ)))))
  p'-continuous-n-above-0 = binary-continuous𝕀 (uncurry mid) mid-continuous
                                              (λ αβ → digitMul (pr₂ αβ 1) (tail (tail (pr₁ αβ))))
                                              (λ αβ → digitMul (pr₁ αβ 1) (tail (tail (pr₂ αβ))))
                                              (digitMul-continuous₂ (λ ■ → tail (tail ■)) tltl-continuous 1)
                                              (digitMul-continuous₁ (λ ■ → tail (tail ■)) tltl-continuous 1)
  m : ST-Moduli 𝕀* → ST-Moduli (×* 𝕀* 𝕀*)
  m (0 , *) = least-mod (×* 𝕀* 𝕀*)
  m (succ n , *) = (pr₁ (p'-continuous-n-above-0 (n , *)))
  γ : (n : ST-Moduli 𝕀*) (α β : ST-Type (×* 𝕀* 𝕀*)) → ST-≈ (×* 𝕀* 𝕀*) α β (m n) → ST-≈ 𝕀* (p' α) (p' β) n
  γ (succ n , *) (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂) zero k<n = ap (_*𝟛 α₂ 1) (α≈β₁ 0 *) ∙ ap (β₁ 0 *𝟛_) (α≈β₂ 1 *)
  γ (succ n , *) α β α≈β (succ k) k<n = pr₂ (p'-continuous-n-above-0 (n , *)) α β α≈β k k<n

-- This is a simple corollary of the general statement and the continuity of the p' and p'' operators
p-continuous : continuous² (×* 𝕀* 𝕀*) 𝕀* p
p-continuous = binary-continuous𝕀 (uncurry mid) mid-continuous p' p'' p'-continuous p''-continuous

{- Proving q is continuous is more complex:
 * The proof is by induction on n (the digit position to be computed) and k
    (which is 0 if no more lookahead is required to compute the current digit
 * When computing digits of the output in positions greater than 2, this is a corollary of the general statement,
    the continuity of the p operator and the inductive hypothesis
 * When computing digits 0, 1 and 2, the continuity is trivial as at these points the output requires 
    0 or 1 digits of lookahead
 * The function "qm" is used to computer the modulus of continuity for a given n and k
-}

q-continuous : ∀ k → continuous² (×* 𝕀* 𝕀*) 𝕀* (q k)

q-continuous-n-above-2 : ∀ k → continuous² (×* 𝕀* 𝕀*) 𝕀* (λ αβ → uncurry mid (p αβ , q k αβ))
q-continuous-n-above-2 k = binary-continuous𝕀 (uncurry mid) mid-continuous p (q k) p-continuous (q-continuous k)

qm : ℕ → ℕ → ST-Moduli (×* 𝕀* 𝕀*)
qm n 0 = (0 , *) , (0 , *)
qm 0 (succ k) = (0 , *) , (0 , *)
qm 1 (succ k) = (0 , *) , (0 , *)
qm 2 (succ k) = (0 , *) , (0 , *)
qm (succ (succ (succ n))) (succ k) = pr₁ (q-continuous-n-above-2 k (n , *))

qm₁ qm₂ : ℕ → ℕ → ℕ
qm₁ n k = pr₁ (pr₁ (qm n k))
qm₂ n k = pr₁ (pr₂ (qm n k))

q-continuous k (n , *) = m n k , γ n k where
  m : ℕ → ℕ → ST-Moduli (×* 𝕀* 𝕀*)
  m n k = (succ (succ (qm₁ n k)) , *) , (succ (succ (qm₂ n k)) , *)
  γ : (n : ℕ) → ∀ k → uc-mod² (×* 𝕀* 𝕀*) 𝕀* (q k) (n , *) (m n k)
  γ n k (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂) 0 j<k =
                    ap (_*𝟛 α₂ 0) (α≈β₁ 0 *)
                 ∙ ap (β₁ 0 *𝟛_) (α≈β₂ 0 *)
  γ n k (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂) 1 j<k =
                    ap (_*𝟛 α₂ 0) (α≈β₁ 1 *)
                 ∙ ap (β₁ 1 *𝟛_) (α≈β₂ 0 *)
  γ n k (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂) 2 j<k =
                    ap (_*𝟛 α₂ 1) (α≈β₁ 1 *)
                 ∙ ap (β₁ 1 *𝟛_) (α≈β₂ 1 *)
  γ n zero α β α≈β (succ (succ (succ j))) j<k = refl
  γ (succ (succ (succ (succ n)))) (succ k) (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂) (succ (succ (succ j))) j<k =
                 pr₂ (q-continuous-n-above-2 k (succ n , *))
                 (tail (tail α₁) , tail (tail α₂)) (tail (tail β₁) , tail (tail β₂))
                 ((tltl-continuous' (pr₁ (qm (succ (succ (succ (succ n)))) (succ k))) α₁ β₁ α≈β₁) ,
                   tltl-continuous' (pr₂ (qm (succ (succ (succ (succ n)))) (succ k))) α₂ β₂ α≈β₂)
                 j j<k

-- Moving towards proving *𝕀 is continuous, we prove that the moduli of continuity for q is monotonic
-- This means that for decreasing values of k, the moduli of continuity does not decrease
qm₁-monotonic : (n k₁ k₂ : ℕ) → k₁ < k₂ → qm₁ n k₁ ≤ qm₁ n k₂ -- (pr₁ (pr₁ (IH n k₁))) ≤ (pr₁ (pr₁ (IH n k₂)))
qm₁-monotonic n 0 (succ k₂) x = *
qm₁-monotonic zero (succ k₁) (succ k₂) x = *
qm₁-monotonic (succ zero) (succ k₁) (succ k₂) x = *
qm₁-monotonic (succ (succ zero)) (succ k₁) (succ k₂) x = *
qm₁-monotonic (succ (succ (succ n))) (succ k₁) (succ k₂) x
  = ≤-max (succ (succ (maxℕ n (succ n)))) (qm₁ (succ n) k₁) (qm₁ (succ n) k₂) (qm₁-monotonic (succ n) k₁ k₂ x)
  
qm₂-monotonic : (n k₁ k₂ : ℕ) → k₁ < k₂ → qm₂ n k₁ ≤ qm₂ n k₂
qm₂-monotonic n zero (succ k₂) x = *
qm₂-monotonic zero (succ k₁) (succ k₂) x = *
qm₂-monotonic (succ zero) (succ k₁) (succ k₂) x = *
qm₂-monotonic (succ (succ zero)) (succ k₁) (succ k₂) x = *
qm₂-monotonic (succ (succ (succ n))) (succ k₁) (succ k₂) x 
  = ≤-max (succ (succ (maxℕ n (succ n)))) (qm₂ (succ n) k₁) (qm₂ (succ n) k₂) (qm₂-monotonic (succ n) k₁ k₂ x)

{- The modulus of continuity is proved in the expected way, using the general statement and the continuity of p and q
 However, proving this modulus of continuity is satisfactory requires the lemma that q's MoC is monotonic
 This is because when computing the MoC, we do not have access to k
 Therefore we use the maximum MoC, and because k < n,
 and q's MoC is computed montonically, the computed MoC is satisfactory -}
*𝕀-continuous : continuous² (×* 𝕀* 𝕀*) 𝕀* (uncurry _*𝕀_)
*𝕀-continuous n = m (pr₁ n) (pr₁ n) , γ (pr₁ n) where
  m : ℕ → ℕ → ST-Moduli (×* 𝕀* 𝕀*)
  m n k = pr₁ (binary-continuous𝕀 (uncurry mid) mid-continuous p (q k) p-continuous (q-continuous k) (n , *))
  q-monotonic : (n k₁ k₂ : ℕ) → k₁ < k₂ → ST-Moduli-≤ (×* 𝕀* 𝕀*) (m n k₁) (m n k₂)
  q-monotonic n k₁ k₂ x = ((qm₁-monotonic (succ (succ (succ n))) (succ k₁) (succ k₂) x) , *)
                                      , ((qm₂-monotonic (succ (succ (succ n))) (succ k₁) (succ k₂) x) , *)
  q-monotonic→ : (n k₁ k₂ : ℕ) → k₁ < k₂
                         → (α β : ST-Type (×* 𝕀* 𝕀*)) → ST-≈ (×* 𝕀* 𝕀*) α β (m n k₂) → ST-≈ (×* 𝕀* 𝕀*) α β (m n k₁)
  q-monotonic→ n k₁ k₂ k<k (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂)
    = (λ j j<m₁ → α≈β₁ j (<≤-trans j (pr₁ (pr₁ (m n k₁))) (pr₁ (pr₁ (m n k₂))) j<m₁ (pr₁ (pr₁ (q-monotonic n k₁ k₂ k<k)))))
      , λ j j<m₂ → α≈β₂ j (<≤-trans j (pr₁ (pr₂ (m n k₁))) (pr₁ (pr₂ (m n k₂))) j<m₂  (pr₁ (pr₂ (q-monotonic n k₁ k₂ k<k))))
  γ : (n : ℕ) → (α β : ST-Type (×* 𝕀* 𝕀*)) → ST-≈ (×* 𝕀* 𝕀*) α β (m n n) → ST-≈ 𝕀* (uncurry _*𝕀_ α) (uncurry _*𝕀_ β) (n , *)
  γ n α β α≈β k k<n =  pr₂ (binary-continuous𝕀 (uncurry mid) mid-continuous p (q k)
                                       p-continuous (q-continuous k) (n , *)) α β (q-monotonic→ n k n k<n α β α≈β) k k<n

-- This is a simple corollary from the above
sq-continuous : continuous² 𝕀* 𝕀* (_²)
sq-continuous n = m , (λ α β α≈β → pr₂ *𝕀c (α , α) (β , β) (pr₁ (γ α β α≈β) , pr₂ (γ α β α≈β))) where
  *𝕀c = *𝕀-continuous n
  m = max-mod 𝕀* (pr₁ (pr₁ *𝕀c)) (pr₂ (pr₁ *𝕀c))
  γ : (α β : 𝕀) → ST-≈ 𝕀* α β m → Σ (λ x → ST-≈ 𝕀* α β (pr₂ (pr₁ *𝕀c)))
  γ α β α≈β = ST-≈-max 𝕀* α β (pr₁ (pr₁ *𝕀c)) (pr₂ (pr₁ *𝕀c)) α≈β
