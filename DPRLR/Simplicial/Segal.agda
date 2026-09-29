module DPRLR.Simplicial.Segal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
  using (isPropΣ ; isPropΠ ; isPropΠ2 ; isPropImplicitΠ3)
open import Cubical.Foundations.Function using (_∘_)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Interval
open import DPRLR.Simplicial.Shapes
  using (Λ² ; Δ² ; ι-horn ; HornData ; HornExtension ; horn-data≃ ; horn-extension≃)

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

Composite-isProp :
  {A : Type ℓ}
  → ((x y : A) → isProp (x ≤ y))
  → {x y z : A}
  → (f : x ≤ y)
  → (g : y ≤ z)
  → isProp (Composite f g)
Composite-isProp homProp {z = z} f g =
  isPropΣ
    (homProp _ z)
    (λ h → HomP-isProp λ w → homProp w z)

isSegal : Type ℓ → Type ℓ
isSegal A =
  {x y z : A}
  → (f : x ≤ y)
  → (g : y ≤ z)
  → isContr (Composite f g)

segal-composite :
  {A : Type ℓ}
  → isSegal A
  → {x y z : A}
  → (f : x ≤ y)
  → (g : y ≤ z)
  → Composite f g
segal-composite S f g =
  S f g .fst

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

-- RS17, Theorem 5.5.
isSegal≃isEquiv-spine :
  {A : Type ℓ}
  → isSegal A ≃ isEquiv (λ (triangle : Δ² → A) → triangle ∘ ι-horn)
isSegal≃isEquiv-spine {A = A} =
    isSegal A
  ≃⟨ segal≃unique-composites ⟩
    ((k : HornData A) → isContr (Composites k))
  ≃⟨ invEquiv (equivΠ horn-data≃ (λ k → cong≃ isContr (extension≃composite k))) ⟩
    ((k : Λ² → A) → isContr (fiber (_∘ ι-horn) k))
  ≃⟨ invEquiv (isEquiv≃isEquiv' (_∘ ι-horn)) ⟩
    isEquiv (λ (triangle : Δ² → A) → triangle ∘ ι-horn)
  ■
  where
  Composites : HornData A → Type _
  Composites ((f , z) , g) = Composite (f , refl , refl) g

  extension-composite-Iso : (k : HornData A) → Iso (HornExtension k) (Composites k)
  Iso.fun (extension-composite-Iso k) (q , right) = q 𝟎 , q , refl , right
  Iso.inv (extension-composite-Iso k) (h , q , left , right) = q , right
  Iso.rightInv (extension-composite-Iso k) (h , q , left , right) i =
    left i , q , (λ j → left (i ∧ j)) , right
  Iso.leftInv (extension-composite-Iso k) _ = refl

  extension≃composite : (k : Λ² → A)
    → fiber (_∘ ι-horn) k ≃ Composites (horn-data≃ .fst k)
  extension≃composite k = compEquiv (horn-extension≃ k)
    (isoToEquiv (extension-composite-Iso (horn-data≃ .fst k)))

  segal≃unique-composites : isSegal A ≃ ((k : HornData A) → isContr (Composites k))
  segal≃unique-composites = propBiimpl→Equiv
    (isPropImplicitΠ3 λ x y z → isPropΠ2 λ f g → isPropIsContr)
    (isPropΠ λ k → isPropIsContr)
    (λ S ((f , z) , g) → S (f , refl , refl) g)
    normalize-endpoints
    where
    normalize-endpoints : ((k : HornData A) → isContr (Composites k)) → isSegal A
    normalize-endpoints normalized {z = z} (f , left , right) =
      transport
        (λ i → (g : right i ≤ z) →
          isContr (Composite (f , (λ j → left (i ∧ j)) , (λ j → right (i ∧ j))) g))
        (λ g → normalized ((f , z) , g))
