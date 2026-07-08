module DPRLR.Simplicial.Interval where

open import Cubical.Foundations.Prelude

infix 4 _≤₂_

postulate
  𝟚 : Type₀
  𝟎 : 𝟚
  𝟏 : 𝟚

  _≤₂_ : 𝟚 → 𝟚 → Type₀
  ≤₂-refl : (i : 𝟚) → i ≤₂ i
  ≤₂-bottom : (i : 𝟚) → 𝟎 ≤₂ i
  ≤₂-top : (i : 𝟚) → i ≤₂ 𝟏
  ≤₂-isProp : (i j : 𝟚) → isProp (i ≤₂ j)
