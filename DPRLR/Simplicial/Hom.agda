module DPRLR.Simplicial.Hom where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Interval

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

infix 4 _≤_ _⊢_≤[_]_

Hom : (A : Type ℓ) → A → A → Type ℓ
Hom A x y =
  Σ (𝟚 → A)
    (λ p → (p 𝟎 ≡ x) × (p 𝟏 ≡ y))

_≤_ : {A : Type ℓ} → A → A → Type ℓ
_≤_ {A = A} = Hom A

hom-path : {x y : A} → Hom A x y → 𝟚 → A
hom-path h = h .fst

left-endpoint : {x y : A} → (h : Hom A x y) → hom-path h 𝟎 ≡ x
left-endpoint h = h .snd .fst

right-endpoint : {x y : A} → (h : Hom A x y) → hom-path h 𝟏 ≡ y
right-endpoint h = h .snd .snd

hom-refl : (x : A) → Hom A x x
hom-refl x = (λ _ → x) , refl , refl

path→hom : {x y : A} → x ≡ y → x ≤ y
path→hom {x = x} p = subst (λ y → x ≤ y) p (hom-refl x)

hom-map : (f : A → B) → {x y : A} → Hom A x y → Hom B (f x) (f y)
hom-map f h =
  (λ i → f (hom-path h i))
  , cong f (left-endpoint h)
  , cong f (right-endpoint h)

HomP :
  {A : Type ℓ} (P : A → Type ℓ') {x y : A}
  → Hom A x y
  → P x
  → P y
  → Type ℓ'
HomP P h u v =
  Σ ((i : 𝟚) → P (hom-path h i))
    (λ q →
      (PathP (λ i → P (left-endpoint h i)) (q 𝟎) u)
      ×
      (PathP (λ i → P (right-endpoint h i)) (q 𝟏) v))

_⊢_≤[_]_ :
  {A : Type ℓ} (P : A → Type ℓ') {x y : A}
  → P x → x ≤ y → P y → Type ℓ'
P ⊢ u ≤[ h ] v = HomP P h u v

isThin : Type ℓ → Type ℓ
isThin A = (x y : A) → isProp (x ≤ y)
