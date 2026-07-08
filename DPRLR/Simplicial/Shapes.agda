module DPRLR.Simplicial.Shapes where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit.Base
open import Cubical.HITs.Pushout.Base

open import DPRLR.Simplicial.Interval

top₂ : 𝟚 → 𝟚 × 𝟚
top₂ i = i , 𝟏

Δ² : Type₀
Δ² = Pushout top₂ (λ _ → tt)

Λ²₁ : Type₀
Λ²₁ = Pushout {A = Unit} {B = 𝟚} {C = 𝟚} (λ _ → 𝟏) (λ _ → 𝟎)

spine₂ : Λ²₁ → Δ²
spine₂ (inl i) = inl (i , 𝟎)
spine₂ (inr i) = inl (𝟏 , i)
spine₂ (push tt i) = inl (𝟏 , 𝟎)
