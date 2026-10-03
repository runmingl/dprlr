module DPRLR.Simplicial.Shapes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit.Base
open import Cubical.HITs.Pushout.Base

open import DPRLR.Simplicial.Interval

Λ² : Type₀
Λ² = Pushout {A = Unit} {B = 𝟚} {C = 𝟚} (λ _ → 𝟏) (λ _ → 𝟎)

Δ² : Type₀
Δ² = Σ[ i ∈ 𝟚 ] Σ[ j ∈ 𝟚 ] (j ≤₂ i)

Δ²-ext : {s t : Δ²} → s .fst ≡ t .fst → s .snd .fst ≡ t .snd .fst → s ≡ t
Δ²-ext p q = ΣPathP (p , ΣPathP (q , isProp→PathP (λ i → ≤₂-isProp _ _) _ _))

bottom₂ right₂ diagonal₂ : 𝟚 → Δ²
bottom₂ i = i , 𝟎 , ≤₂-bottom i
right₂ j = 𝟏 , j , ≤₂-top j
diagonal₂ i = i , i , ≤₂-refl i

ι-horn : Λ² → Δ²
ι-horn (inl i) = bottom₂ i
ι-horn (inr j) = right₂ j
ι-horn (push tt k) = Δ²-ext {s = bottom₂ 𝟏} {t = right₂ 𝟎} refl refl k

private
  variable
    ℓ : Level
    A : Type ℓ

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
