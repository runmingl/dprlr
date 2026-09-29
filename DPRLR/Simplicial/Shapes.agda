module DPRLR.Simplicial.Shapes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Equiv.Fiberwise using (fibers-total)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit.Base
open import Cubical.HITs.Pushout.Base

open import DPRLR.Simplicial.Interval
open import DPRLR.Simplicial.Hom

top₂ : 𝟚 → 𝟚 × 𝟚
top₂ i = i , 𝟏

Δ² : Type₀
Δ² = Pushout top₂ (λ _ → tt)

Λ² : Type₀
Λ² = Pushout {A = Unit} {B = 𝟚} {C = 𝟚} (λ _ → 𝟏) (λ _ → 𝟎)

ι-horn : Λ² → Δ²
ι-horn (inl i) = inl (i , 𝟎)
ι-horn (inr i) = inl (𝟏 , i)
ι-horn (push tt i) = inl (𝟏 , 𝟎)

private
  variable
    ℓ : Level
    A : Type ℓ

--                  z
--                  ↑
--                  | g
--                  |
--       x────f────→y
HornData : Type ℓ → Type ℓ
HornData A = Σ ((𝟚 → A) × A) (λ (f , z) → f 𝟏 ≤ z)

--       Extension of (f, g) to Δ²:
--
--                    z
--                  ↗ ↑ ↖
--                /   |   \
--      h = q 𝟎 /  q i|     \ q 𝟏 = g
--            /       |       \
--           x───────f i───────y
--                   f →
--
--       h : x ≤ z      q : (i : 𝟚) → f i ≤ z
HornExtension : HornData A → Type _
HornExtension ((f , z) , g) = fiber (λ (q : (i : 𝟚) → f i ≤ z) → q 𝟏) g

Δ²-elim : Iso (Δ² → A)
  (Σ ((𝟚 → A) × A) (λ (f , z) → (i : 𝟚) → f i ≤ z))
Iso.fun Δ²-elim t =
  ((λ i → t (inl (i , 𝟎))) , t (inr tt))
  , λ i → (λ j → t (inl (i , j))) , refl , cong t (push i)
Iso.inv Δ²-elim ((f , z) , q) (inl (i , j)) = hom-path (q i) j
Iso.inv Δ²-elim ((f , z) , q) (inr tt) = z
Iso.inv Δ²-elim ((f , z) , q) (push i k) = right-endpoint (q i) k
Iso.rightInv Δ²-elim ((f , z) , q) k =
  ((λ i → left-endpoint (q i) k) , z)
  , λ i → hom-path (q i)
    , (λ j → left-endpoint (q i) (k ∧ j))
    , right-endpoint (q i)
Iso.leftInv Δ²-elim t k (inl (i , j)) = t (inl (i , j))
Iso.leftInv Δ²-elim t k (inr tt) = t (inr tt)
Iso.leftInv Δ²-elim t k (push i j) = t (push i j)

Λ²-elim : Iso (Λ² → A)
  (Σ[ f ∈ (𝟚 → A) ] Σ[ g ∈ (𝟚 → A) ] (f 𝟏 ≡ g 𝟎))
Iso.fun Λ²-elim k = (k ∘ inl) , (k ∘ inr) , cong k (push tt)
Iso.inv Λ²-elim (f , g , p) (inl i) = f i
Iso.inv Λ²-elim (f , g , p) (inr i) = g i
Iso.inv Λ²-elim (f , g , p) (push tt j) = p j
Iso.rightInv Λ²-elim _ = refl
Iso.leftInv Λ²-elim k i (inl j) = k (inl j)
Iso.leftInv Λ²-elim k i (inr j) = k (inr j)
Iso.leftInv Λ²-elim k i (push tt j) = k (push tt j)

horn-data≃ : (Λ² → A) ≃ HornData A
horn-data≃ = compEquiv (isoToEquiv Λ²-elim) (isoToEquiv (iso
  (λ { (f , g , p) → (f , g 𝟏) , g , sym p , refl })
  (λ { ((f , z) , g) → f , hom-path g , sym (left-endpoint g) })
  (λ { ((f , z) , g) i →
    (f , right-endpoint g i)
    , hom-path g , left-endpoint g , (λ j → right-endpoint g (i ∧ j)) })
  (λ _ → refl)))

--                k
--       Λ²────────────→A
--        |             ↗
-- ι-horn |           / t
--        ↓         /
--        Δ²───────┘       t ∘ ι-horn ≡ k
horn-extension≃ : (k : Λ² → A)
  → fiber (_∘ ι-horn) k ≃ HornExtension (horn-data≃ .fst k)
horn-extension≃ {A = A} k = compEquiv
  (Σ-cong-equiv (isoToEquiv Δ²-elim) (λ t →
    compEquiv (congEquiv horn-data≃)
      (compPathlEquiv (sym (funExt⁻ restriction-square t)))))
  (isoToEquiv (fibers-total
    (λ (f , z) → (i : 𝟚) → f i ≤ z)
    (λ (f , z) → f 𝟏 ≤ z)
    (λ _ q → q 𝟏)))
  where
  restriction-square :
    (λ (t : Δ² → A) → horn-data≃ .fst (t ∘ ι-horn))
    ≡ (λ t → Iso.fun Δ²-elim t .fst , Iso.fun Δ²-elim t .snd 𝟏)
  restriction-square k t =
    ((λ i → t (inl (i , 𝟎))) , t (push 𝟏 k))
    , (λ j → t (inl (𝟏 , j))) , refl , (λ j → t (push 𝟏 (k ∧ j)))
