module DPRLR.Simplicial.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool.Base renaming (Bool to Bool₂)
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom

private
  variable
    ℓ : Level
    A : Type ℓ

idtoarr :
  {x y : A}
  → x ≡ y
  → x ≤ y
idtoarr =
  path→hom

idtoarr-refl :
  {x : A}
  → idtoarr (refl {x = x}) ≡ hom-refl x
idtoarr-refl {x = x} =
  substRefl {B = λ y → x ≤ y} (hom-refl x)

isDiscrete : Type ℓ → Type ℓ
isDiscrete A =
  (x y : A) → isEquiv (idtoarr {A = A} {x = x} {y = y})

arr→path :
  {A : Type ℓ}
  → isDiscrete A
  → {x y : A}
  → x ≤ y
  → x ≡ y
arr→path d {x = x} {y = y} =
  invIsEq (d x y)

idtoarr-arr→path :
  {A : Type ℓ}
  → (d : isDiscrete A)
  → {x y : A}
  → (f : x ≤ y)
  → idtoarr (arr→path d f) ≡ f
idtoarr-arr→path d {x = x} {y = y} =
  secIsEq (d x y)

path-to-isContr :
  {A : Type ℓ}
  → (a : A)
  → isContr (Σ A (λ x → x ≡ a))
path-to-isContr a =
  isOfHLevelRespectEquiv 0
    (Σ-cong-equiv-snd (λ _ → isoToEquiv (iso sym sym (λ _ → refl) (λ _ → refl))))
    (isContrSingl a)

hom-to-isContr :
  {A : Type ℓ}
  → isDiscrete A
  → (a : A)
  → isContr (Σ A (λ x → x ≤ a))
hom-to-isContr d a =
  isOfHLevelRespectEquiv 0
    (Σ-cong-equiv-snd (λ x → idtoarr , d x a))
    (path-to-isContr a)

postulate
  Bool₂-isDiscrete : isDiscrete Bool₂
