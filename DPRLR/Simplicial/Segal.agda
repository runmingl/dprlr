module DPRLR.Simplicial.Segal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.Fiberwise using (fiberEquiv ; totalEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
  using (isPropΣ ; isPropΠ ; isPropΠ2 ; isPropImplicitΠ3 ; isOfHLevelRespectEquiv)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit.Base using (tt)
open import Cubical.HITs.Pushout.Base using (inl ; inr ; push)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Interval
open import DPRLR.Simplicial.Shapes using (Λ²₁ ; Δ² ; spine₂)

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

-- RS17 Theorem 5.5
isSegal≃isEquiv-spine :
  {A : Type ℓ}
  → isSegal A ≃ isEquiv (λ (triangle : Δ² → A) → triangle ∘ spine₂)
isSegal≃isEquiv-spine {A = A} =
    isSegal A
  ≃⟨ segal≃contractible-fibers ⟩
    ((b : BoundaryData) (g : RightEdge b) → isContr (fiber (evaluate b) g))
  ≃⟨ equivΠCod (λ b → invEquiv (isEquiv≃isEquiv' (evaluate b))) ⟩
    ((b : BoundaryData) → isEquiv (evaluate b))
  ≃⟨ fiberwise≃total ⟩
    isEquiv restrict-columns
  ≃⟨ restriction≃ ⟩
    isEquiv (λ (triangle : Δ² → A) → triangle ∘ spine₂)
  ■
  where
  BoundaryData : Type _
  BoundaryData = (𝟚 → A) × A

  Columns : BoundaryData → Type _
  Columns (p , z) = (i : 𝟚) → p i ≤ z

  RightEdge : BoundaryData → Type _
  RightEdge (p , z) = p 𝟏 ≤ z

  evaluate : (b : BoundaryData) → Columns b → RightEdge b
  evaluate b q = q 𝟏

  restrict-columns : Σ BoundaryData Columns → Σ BoundaryData RightEdge
  restrict-columns (b , q) = b , evaluate b q

  triangle-Iso : Iso (Δ² → A) (Σ BoundaryData Columns)
  Iso.fun triangle-Iso t =
    ((λ i → t (inl (i , 𝟎))) , t (inr tt))
    , λ i → (λ j → t (inl (i , j))) , refl , cong t (push i)
  Iso.inv triangle-Iso ((p , z) , q) (inl (i , j)) = hom-path (q i) j
  Iso.inv triangle-Iso ((p , z) , q) (inr tt) = z
  Iso.inv triangle-Iso ((p , z) , q) (push i k) = right-endpoint (q i) k
  Iso.rightInv triangle-Iso ((p , z) , q) k =
    ((λ i → left-endpoint (q i) k) , z)
    , λ i → hom-path (q i)
      , (λ j → left-endpoint (q i) (k ∧ j))
      , right-endpoint (q i)
  Iso.leftInv triangle-Iso t k (inl (i , j)) = t (inl (i , j))
  Iso.leftInv triangle-Iso t k (inr tt) = t (inr tt)
  Iso.leftInv triangle-Iso t k (push i j) = t (push i j)

  spine-Iso : Iso (Λ²₁ → A) (Σ BoundaryData RightEdge)
  Iso.fun spine-Iso s =
    ((λ i → s (inl i)) , s (inr 𝟏))
    , (λ i → s (inr i)) , sym (cong s (push tt)) , refl
  Iso.inv spine-Iso ((p , z) , g) (inl i) = p i
  Iso.inv spine-Iso ((p , z) , g) (inr i) = hom-path g i
  Iso.inv spine-Iso ((p , z) , g) (push tt k) = left-endpoint g (~ k)
  Iso.rightInv spine-Iso ((p , z) , g) k =
    (p , right-endpoint g k)
    , hom-path g , left-endpoint g , (λ j → right-endpoint g (k ∧ j))
  Iso.leftInv spine-Iso s k (inl i) = s (inl i)
  Iso.leftInv spine-Iso s k (inr i) = s (inr i)
  Iso.leftInv spine-Iso s k (push tt j) = s (push tt j)

  restriction-square :
    (λ t → Iso.fun spine-Iso (t ∘ spine₂))
    ≡ (λ t → restrict-columns (Iso.fun triangle-Iso t))
  restriction-square k t =
    ((λ i → t (inl (i , 𝟎))) , t (push 𝟏 k))
    , (λ j → t (inl (𝟏 , j))) , refl , (λ j → t (push 𝟏 (k ∧ j)))

  composite-Iso : (p : 𝟚 → A) (z : A) (g : p 𝟏 ≤ z)
    → Iso (Composite (p , refl , refl) g) (fiber (evaluate (p , z)) g)
  Iso.fun (composite-Iso p z g) (h , q , left , right) = q , right
  Iso.inv (composite-Iso p z g) (q , right) = q 𝟎 , q , refl , right
  Iso.rightInv (composite-Iso p z g) _ = refl
  Iso.leftInv (composite-Iso p z g) (h , q , left , right) k =
    left k , q , (λ j → left (k ∧ j)) , right

  normalize-endpoints :
    ((p : 𝟚 → A) (z : A) (g : p 𝟏 ≤ z)
      → isContr (Composite (p , refl , refl) g))
    → isSegal A
  normalize-endpoints normalized {z = z} (p , left , right) g =
    J (λ x left → {y : A} (right : p 𝟏 ≡ y) (g : y ≤ z)
        → isContr (Composite (p , left , right) g))
      (λ right g →
        J (λ y right → (g : y ≤ z) → isContr (Composite (p , refl , right) g))
          (normalized p z) right g)
      left right g

  segal≃contractible-fibers :
    isSegal A
    ≃ ((b : BoundaryData) (g : RightEdge b) → isContr (fiber (evaluate b) g))
  segal≃contractible-fibers =
    propBiimpl→Equiv
      (isPropImplicitΠ3 λ x y z → isPropΠ2 λ f g → isPropIsContr)
      (isPropΠ2 λ b g → isPropIsContr)
      (λ S (p , z) g →
        isOfHLevelRespectEquiv 0 (isoToEquiv (composite-Iso p z g))
          (S (p , refl , refl) g))
      (λ fibers → normalize-endpoints λ p z g →
        isOfHLevelRespectEquiv 0 (isoToEquiv (invIso (composite-Iso p z g)))
          (fibers (p , z) g))

  fiberwise≃total :
    ((b : BoundaryData) → isEquiv (evaluate b)) ≃ isEquiv restrict-columns
  fiberwise≃total =
    propBiimpl→Equiv
      (isPropΠ λ b → isPropIsEquiv (evaluate b))
      (isPropIsEquiv restrict-columns)
      (totalEquiv Columns RightEdge evaluate)
      (fiberEquiv Columns RightEdge evaluate)

  restriction≃ :
    isEquiv restrict-columns ≃ isEquiv (λ (t : Δ² → A) → t ∘ spine₂)
  restriction≃ =
    propBiimpl→Equiv (isPropIsEquiv _) (isPropIsEquiv _) to from
    where
    to : isEquiv restrict-columns → isEquiv (λ (t : Δ² → A) → t ∘ spine₂)
    to E =
      isEquiv[equivFunA≃B∘f]→isEquiv[f] (_∘ spine₂) (isoToEquiv spine-Iso)
        (subst isEquiv (sym restriction-square) (equivIsEquiv restriction-equiv))
      where
      restriction-equiv : (Δ² → A) ≃ Σ BoundaryData RightEdge
      restriction-equiv =
          (Δ² → A)
        ≃⟨ isoToEquiv triangle-Iso ⟩
          Σ BoundaryData Columns
        ≃⟨ restrict-columns , E ⟩
          Σ BoundaryData RightEdge
        ■

    from : isEquiv (λ (t : Δ² → A) → t ∘ spine₂) → isEquiv restrict-columns
    from E =
      isEquiv[f∘equivFunA≃B]→isEquiv[f] restrict-columns (isoToEquiv triangle-Iso)
        (subst isEquiv restriction-square (equivIsEquiv restriction-equiv))
      where
      restriction-equiv : (Δ² → A) ≃ Σ BoundaryData RightEdge
      restriction-equiv =
          (Δ² → A)
        ≃⟨ (_∘ spine₂) , E ⟩
          (Λ²₁ → A)
        ≃⟨ isoToEquiv spine-Iso ⟩
          Σ BoundaryData RightEdge
        ■
