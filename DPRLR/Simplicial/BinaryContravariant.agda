module DPRLR.Simplicial.BinaryContravariant where

open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Contravariant

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    B : Type ℓ'

SlicesContravariant :
  {A : Type ℓ} {B : Type ℓ'}
  → (A × B → Type ℓ'')
  → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
SlicesContravariant {A = A} {B = B} R =
  ((a : A) → isContravariant (λ b → R (a , b)))
  ×
  ((b : B) → isContravariant (λ a → R (a , b)))

binary-contravariance :
  {R : A × B → Type ℓ''}
  → isContravariant R
  → SlicesContravariant R
binary-contravariance c =
  (λ a → contravariant-reindex (λ b → a , b) c)
  ,
  (λ b → contravariant-reindex (λ a → a , b) c)
