module DPRLR.Simplicial.Interval where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isProp× ; isPropΠ3)
open import Cubical.Data.Sigma using (_×_ ; Σ≡Prop)
open import Cubical.Functions.Logic

infix 4 _≤₂_
infixr 7 _∧₂_
infixr 6 _∨₂_

postulate
  𝟚 : Type₀
  𝟚-isSet : isSet 𝟚

  _≤₂_ : 𝟚 → 𝟚 → Type₀
  ≤₂-isProp : (i j : 𝟚) → isProp (i ≤₂ j)
  ≤₂-refl : (i : 𝟚) → i ≤₂ i
  ≤₂-trans : {i j k : 𝟚} → i ≤₂ j → j ≤₂ k → i ≤₂ k
  ≤₂-antisym : {i j : 𝟚} → i ≤₂ j → j ≤₂ i → i ≡ j
  ≤₂-total : (i j : 𝟚) → (i ≤₂ j) ⊔′ (j ≤₂ i)

  𝟎 𝟏 : 𝟚
  ≤₂-bottom : (i : 𝟚) → 𝟎 ≤₂ i
  ≤₂-top : (i : 𝟚) → i ≤₂ 𝟏

private
  Meet : 𝟚 → 𝟚 → Type₀
  Meet i j = Σ[ m ∈ 𝟚 ] ((m ≤₂ i) × (m ≤₂ j)
    × ((k : 𝟚) → k ≤₂ i → k ≤₂ j → k ≤₂ m))

  isPropMeet : (i j : 𝟚) → isProp (Meet i j)
  isPropMeet i j (m , ml , mr , mg) (n , nl , nr , ng) =
    Σ≡Prop (λ _ → isProp× (≤₂-isProp _ _)
      (isProp× (≤₂-isProp _ _) (isPropΠ3 λ _ _ _ → ≤₂-isProp _ _)))
      (≤₂-antisym (ng m ml mr) (mg n nl nr))

  meet : (i j : 𝟚) → Meet i j
  meet i j =
    ⊔-elim (_ , ≤₂-isProp i j) (_ , ≤₂-isProp j i) (λ _ → _ , isPropMeet i j)
      (λ p → i , ≤₂-refl i , p , (λ k ki kj → ki))
      (λ p → j , p , ≤₂-refl j , (λ k ki kj → kj))
      (≤₂-total i j)

  Join : 𝟚 → 𝟚 → Type₀
  Join i j = Σ[ m ∈ 𝟚 ] ((i ≤₂ m) × (j ≤₂ m)
    × ((k : 𝟚) → i ≤₂ k → j ≤₂ k → m ≤₂ k))

  isPropJoin : (i j : 𝟚) → isProp (Join i j)
  isPropJoin i j (m , ml , mr , mlst) (n , nl , nr , nlst) =
    Σ≡Prop (λ _ → isProp× (≤₂-isProp _ _)
      (isProp× (≤₂-isProp _ _) (isPropΠ3 λ _ _ _ → ≤₂-isProp _ _)))
      (≤₂-antisym (mlst n nl nr) (nlst m ml mr))

  join : (i j : 𝟚) → Join i j
  join i j =
    ⊔-elim (_ , ≤₂-isProp i j) (_ , ≤₂-isProp j i) (λ _ → _ , isPropJoin i j)
      (λ p → j , p , ≤₂-refl j , (λ k ik jk → jk))
      (λ p → i , ≤₂-refl i , p , (λ k ik jk → ik))
      (≤₂-total i j)

_∧₂_ : 𝟚 → 𝟚 → 𝟚
i ∧₂ j = meet i j .fst

∧₂-left : (i j : 𝟚) → (i ∧₂ j) ≤₂ i
∧₂-left i j = meet i j .snd .fst

∧₂-right : (i j : 𝟚) → (i ∧₂ j) ≤₂ j
∧₂-right i j = meet i j .snd .snd .fst

∧₂-greatest : {i j k : 𝟚} → k ≤₂ i → k ≤₂ j → k ≤₂ (i ∧₂ j)
∧₂-greatest {i} {j} {k} = meet i j .snd .snd .snd k

_∨₂_ : 𝟚 → 𝟚 → 𝟚
i ∨₂ j = join i j .fst

∨₂-left : (i j : 𝟚) → i ≤₂ (i ∨₂ j)
∨₂-left i j = join i j .snd .fst

∨₂-right : (i j : 𝟚) → j ≤₂ (i ∨₂ j)
∨₂-right i j = join i j .snd .snd .fst

∨₂-least : {i j k : 𝟚} → i ≤₂ k → j ≤₂ k → (i ∨₂ j) ≤₂ k
∨₂-least {i} {j} {k} = join i j .snd .snd .snd k

∧₂-mono : {i i' j j' : 𝟚} → i ≤₂ i' → j ≤₂ j' → (i ∧₂ j) ≤₂ (i' ∧₂ j')
∧₂-mono {i} {j = j} p q =
  ∧₂-greatest (≤₂-trans (∧₂-left i j) p) (≤₂-trans (∧₂-right i j) q)

∧₂-zero : (i : 𝟚) → (i ∧₂ 𝟎) ≡ 𝟎
∧₂-zero i = ≤₂-antisym (∧₂-right i 𝟎) (≤₂-bottom _)

∧₂-one : (i : 𝟚) → (i ∧₂ 𝟏) ≡ i
∧₂-one i = ≤₂-antisym (∧₂-left i 𝟏) (∧₂-greatest (≤₂-refl i) (≤₂-top i))

∨₂-mono : {i i' j j' : 𝟚} → i ≤₂ i' → j ≤₂ j' → (i ∨₂ j) ≤₂ (i' ∨₂ j')
∨₂-mono {i' = i'} {j' = j'} p q =
  ∨₂-least (≤₂-trans p (∨₂-left i' j')) (≤₂-trans q (∨₂-right i' j'))

∨₂-zero : (i : 𝟚) → (i ∨₂ 𝟎) ≡ i
∨₂-zero i = ≤₂-antisym (∨₂-least (≤₂-refl i) (≤₂-bottom i)) (∨₂-left i 𝟎)

∨₂-one : (i : 𝟚) → (i ∨₂ 𝟏) ≡ 𝟏
∨₂-one i = ≤₂-antisym (≤₂-top _) (∨₂-right i 𝟏)

∧₂-of-≤ : {i j : 𝟚} → i ≤₂ j → (i ∧₂ j) ≡ i
∧₂-of-≤ {i} {j} p = ≤₂-antisym (∧₂-left i j) (∧₂-greatest (≤₂-refl i) p)

∧₂-of-≥ : {i j : 𝟚} → j ≤₂ i → (i ∧₂ j) ≡ j
∧₂-of-≥ {i} {j} p = ≤₂-antisym (∧₂-right i j) (∧₂-greatest p (≤₂-refl j))

∨₂-of-≤ : {i j : 𝟚} → i ≤₂ j → (i ∨₂ j) ≡ j
∨₂-of-≤ {i} {j} p = ≤₂-antisym (∨₂-least p (≤₂-refl j)) (∨₂-right i j)

∨₂-of-≥ : {i j : 𝟚} → j ≤₂ i → (i ∨₂ j) ≡ i
∨₂-of-≥ {i} {j} p = ≤₂-antisym (∨₂-least (≤₂-refl i) p) (∨₂-left i j)

∨₂-zero-left : (i : 𝟚) → (𝟎 ∨₂ i) ≡ i
∨₂-zero-left i = ∨₂-of-≤ (≤₂-bottom i)
