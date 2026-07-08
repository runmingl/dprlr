module DPRLR.Simplicial.Representable where

open import Cubical.Foundations.Prelude

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Segal
open import DPRLR.Simplicial.Contravariant

representable-isContravariant :
  {ℓ : Level} {A : Type ℓ}
  → isSegal A
  → (a : A)
  → isContravariant (λ x → x ≤ a)
representable-isContravariant S a .contrav-lift f v =
  S f v
