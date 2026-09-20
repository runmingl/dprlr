module DPRLR.Simplicial.Discrete where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Cubical.Foundations.Path using (symIso)
open import Cubical.Data.Bool.Base renaming (Bool to Bool₂)
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom

private
  variable
    ℓ : Level
    A : Type ℓ

isDiscrete : Type ℓ → Type ℓ
isDiscrete A =
  (x y : A) → isEquiv (path→hom {A = A} {x = x} {y = y})

hom→path :
  {A : Type ℓ}
  → isDiscrete A
  → {x y : A}
  → x ≤ y
  → x ≡ y
hom→path d {x = x} {y = y} =
  invIsEq (d x y)

path→hom-hom→path :
  {A : Type ℓ}
  → (d : isDiscrete A)
  → {x y : A}
  → (f : x ≤ y)
  → path→hom (hom→path d f) ≡ f
path→hom-hom→path d {x = x} {y = y} =
  secIsEq (d x y)

hom-to-isContr :
  {A : Type ℓ}
  → isDiscrete A
  → (a : A)
  → isContr (Σ A (λ x → x ≤ a))
hom-to-isContr d a =
  isOfHLevelRespectEquiv 0
    (Σ-cong-equiv-snd λ x →
        a ≡ x
      ≃⟨ isoToEquiv symIso ⟩
        x ≡ a
      ≃⟨ path→hom , d x a ⟩
        x ≤ a
      ■)
    (isContrSingl a)

postulate
  Bool₂-isDiscrete : isDiscrete Bool₂
