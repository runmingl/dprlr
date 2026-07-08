module DPRLR.Simplicial.Segal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom

private
  variable
    ℓ : Level

Composite :
  {A : Type ℓ} {x y z : A}
  → x ≤ y
  → y ≤ z
  → Type ℓ
Composite {z = z} f g =
  Σ (_ ≤ z) (λ h → (λ w → w ≤ z) ⊢ h ≤[ f ] g)

isSegal : Type ℓ → Type ℓ
isSegal A =
  {x y z : A}
  → (f : x ≤ y)
  → (g : y ≤ z)
  → isContr (Composite f g)

segal-contractible-composites :
  {A : Type ℓ}
  → isSegal A
  → {x y z : A}
  → (f : x ≤ y)
  → (g : y ≤ z)
  → isContr (Composite f g)
segal-contractible-composites S f g =
  S f g

contractible-composites→isSegal :
  {A : Type ℓ}
  → ({x y z : A}
     → (f : x ≤ y)
     → (g : y ≤ z)
     → isContr (Composite f g))
  → isSegal A
contractible-composites→isSegal S =
  S

segal-composite :
  {A : Type ℓ}
  → isSegal A
  → {x y z : A}
  → (f : x ≤ y)
  → (g : y ≤ z)
  → Composite f g
segal-composite S f g =
  segal-contractible-composites S f g .fst

segal-compose :
  {A : Type ℓ}
  → isSegal A
  → {x y z : A}
  → x ≤ y
  → y ≤ z
  → x ≤ z
segal-compose S f g =
  segal-composite S f g .fst

segal-compose-witness :
  {A : Type ℓ}
  → (S : isSegal A)
  → {x y z : A}
  → (f : x ≤ y)
  → (g : y ≤ z)
  → (λ w → w ≤ z) ⊢ segal-compose S f g ≤[ f ] g
segal-compose-witness S f g =
  segal-composite S f g .snd
