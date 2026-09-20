module DPRLR.Simplicial.Product where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

HomP×-fst :
  {C : A → Type ℓ'} {D : A → Type ℓ''}
  {x y : A} {f : x ≤ y} {u : C x × D x} {v : C y × D y}
  → (λ z → C z × D z) ⊢ u ≤[ f ] v
  → C ⊢ fst u ≤[ f ] fst v
HomP×-fst q =
  (λ i → fst (q .fst i))
  , fst (PathPΣ (q .snd .fst))
  , fst (PathPΣ (q .snd .snd))

HomP×-snd :
  {C : A → Type ℓ'} {D : A → Type ℓ''}
  {x y : A} {f : x ≤ y} {u : C x × D x} {v : C y × D y}
  → (λ z → C z × D z) ⊢ u ≤[ f ] v
  → D ⊢ snd u ≤[ f ] snd v
HomP×-snd q =
  (λ i → snd (q .fst i))
  , snd (PathPΣ (q .snd .fst))
  , snd (PathPΣ (q .snd .snd))

HomP× :
  {C : A → Type ℓ'} {D : A → Type ℓ''}
  {x y : A} {f : x ≤ y}
  {uC : C x} {vC : C y} {uD : D x} {vD : D y}
  → C ⊢ uC ≤[ f ] vC
  → D ⊢ uD ≤[ f ] vD
  → (λ z → C z × D z) ⊢ (uC , uD) ≤[ f ] (vC , vD)
HomP× p q =
  (λ i → p .fst i , q .fst i)
  , ΣPathP (p .snd .fst , q .snd .fst)
  , ΣPathP (p .snd .snd , q .snd .snd)

Σ≤ :
  {A : Type ℓ} {B : A → Type ℓ'}
  {x y : A} {u : B x} {v : B y}
  (h : x ≤ y)
  → B ⊢ u ≤[ h ] v
  → (x , u) ≤ (y , v)
Σ≤ h h∙ =
  (λ i → hom-path h i , h∙ .fst i)
  , ΣPathP (left-endpoint h , h∙ .snd .fst)
  , ΣPathP (right-endpoint h , h∙ .snd .snd)

HomΣ-Iso :
  {B : A → Type ℓ'} {x y : Σ A B}
  → Iso (x ≤ y) (Σ (fst x ≤ fst y) (λ f → B ⊢ snd x ≤[ f ] snd y))
Iso.fun HomΣ-Iso h = hom-map fst h
  , (λ i → snd (hom-path h i))
  , (λ i → snd (left-endpoint h i))
  , (λ i → snd (right-endpoint h i))
Iso.inv HomΣ-Iso (f , q) = Σ≤ f q
Iso.rightInv HomΣ-Iso _ = refl
Iso.leftInv HomΣ-Iso _ = refl

HomΣ≃ :
  {B : A → Type ℓ'} {x y : Σ A B}
  → (x ≤ y) ≃ (Σ (fst x ≤ fst y) (λ f → B ⊢ snd x ≤[ f ] snd y))
HomΣ≃ = isoToEquiv HomΣ-Iso

HomPΣ-fst :
  {C : A → Type ℓ'} {D : (a : A) → C a → Type ℓ''}
  {x y : A} {f : x ≤ y}
  {u : Σ (C x) (D x)} {v : Σ (C y) (D y)}
  → (λ a → Σ (C a) (D a)) ⊢ u ≤[ f ] v
  → C ⊢ fst u ≤[ f ] fst v
HomPΣ-fst q =
  (λ i → fst (q .fst i))
  , fst (PathPΣ (q .snd .fst))
  , fst (PathPΣ (q .snd .snd))

HomPΣ-snd :
  {C : A → Type ℓ'} {D : (a : A) → C a → Type ℓ''}
  {x y : A} {f : x ≤ y}
  {u : Σ (C x) (D x)} {v : Σ (C y) (D y)}
  (q : (λ a → Σ (C a) (D a)) ⊢ u ≤[ f ] v)
  → (λ au → D (fst au) (snd au))
      ⊢ snd u ≤[ Σ≤ {B = C} f (HomPΣ-fst {C = C} {D = D} q) ] snd v
HomPΣ-snd {C = C} {D = D} {f = f} q =
  (λ i → snd (q .fst i))
  , snd (PathPΣ (q .snd .fst))
  , snd (PathPΣ (q .snd .snd))

HomPΣ :
  {C : A → Type ℓ'} {D : (a : A) → C a → Type ℓ''}
  {x y : A} {f : x ≤ y}
  {uC : C x} {vC : C y}
  {uD : D x uC} {vD : D y vC}
  (p : C ⊢ uC ≤[ f ] vC)
  → (λ au → D (fst au) (snd au)) ⊢ uD ≤[ Σ≤ f p ] vD
  → (λ a → Σ (C a) (D a)) ⊢ (uC , uD) ≤[ f ] (vC , vD)
HomPΣ {C = C} {D = D} {f = f} p q =
  (λ i → p .fst i , q .fst i)
  , ΣPathP (p .snd .fst , q .snd .fst)
  , ΣPathP (p .snd .snd , q .snd .snd)
