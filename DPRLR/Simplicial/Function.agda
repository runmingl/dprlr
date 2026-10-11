module DPRLR.Simplicial.Function where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import DPRLR.Simplicial.Hom

private
  variable
    ℓ ℓA ℓB ℓX ℓP : Level
    A : Type ℓA
    B : A → Type ℓB
    X : Type ℓX

hom-funExt⁻ :
  {f g : (x : A) → B x}
  → f ≤ g
  → (x : A) → f x ≤ g x
hom-funExt⁻ h x = hom-map (λ f → f x) h

hom-funExt :
  {f g : (x : A) → B x}
  → ((x : A) → f x ≤ g x)
  → f ≤ g
hom-funExt h =
  (λ i x → hom-path (h x) i)
  , funExt (λ x → left-endpoint (h x))
  , funExt (λ x → right-endpoint (h x))

hom-funExt⁻-Iso :
  {f g : (x : A) → B x}
  → Iso (f ≤ g) ((x : A) → f x ≤ g x)
Iso.fun hom-funExt⁻-Iso =
  hom-funExt⁻
Iso.inv hom-funExt⁻-Iso =
  hom-funExt
Iso.rightInv hom-funExt⁻-Iso _ =
  refl
Iso.leftInv hom-funExt⁻-Iso _ =
  refl

hom-funExt⁻≃ :
  {f g : (x : A) → B x}
  → (f ≤ g) ≃ ((x : A) → f x ≤ g x)
hom-funExt⁻≃ =
  isoToEquiv hom-funExt⁻-Iso

HomPΠ-funExt⁻ :
  {P : A → X → Type ℓP}
  {x y : A}
  {h : x ≤ y}
  {u : (i : X) → P x i}
  {v : (i : X) → P y i}
  → (λ a → (i : X) → P a i) ⊢ u ≤[ h ] v
  → (i : X) → (λ a → P a i) ⊢ u i ≤[ h ] v i
HomPΠ-funExt⁻ q i =
  (λ j → q .fst j i)
  , (λ j → q .snd .fst j i)
  , (λ j → q .snd .snd j i)

HomPΠ :
  {P : A → X → Type ℓP}
  {x y : A}
  {h : x ≤ y}
  {u : (i : X) → P x i}
  {v : (i : X) → P y i}
  → ((i : X) → (λ a → P a i) ⊢ u i ≤[ h ] v i)
  → (λ a → (i : X) → P a i) ⊢ u ≤[ h ] v
HomPΠ q =
  (λ j i → q i .fst j)
  , (λ j i → q i .snd .fst j)
  , (λ j i → q i .snd .snd j)
