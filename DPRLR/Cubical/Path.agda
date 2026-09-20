module DPRLR.Cubical.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (ΣPathP ; PathPΣ)

ΣPathP-subst : {ℓ ℓ' : Level} {X : Type ℓ} (P : X → Type ℓ')
  {x y : X} (p : x ≡ y) (u : P x)
  → (x , u) ≡ (y , subst P p u)
ΣPathP-subst P p u = ΣPathP (p , subst-filler P p u)

ΣPath→PathP : {ℓ ℓ' : Level} {X : Type ℓ} {P : X → Type ℓ'}
  → isSet X → {x y : X} {u : P x} {v : P y}
  → (p : x ≡ y) → (x , u) ≡ (y , v)
  → PathP (λ i → P (p i)) u v
ΣPath→PathP {P = P} setX p e =
  subst (λ q → PathP (λ i → P (q i)) _ _)
    (setX _ _ (cong fst e) p) (PathPΣ e .snd)
