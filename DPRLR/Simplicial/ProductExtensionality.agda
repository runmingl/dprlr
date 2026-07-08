module DPRLR.Simplicial.ProductExtensionality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Interval

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

HomP×-Iso :
  {C : A → Type ℓ'} {D : A → Type ℓ''}
  {x y : A} {f : x ≤ y} {u : C x × D x} {v : C y × D y}
  → Iso
      ((λ z → C z × D z) ⊢ u ≤[ f ] v)
      ((C ⊢ fst u ≤[ f ] fst v) × (D ⊢ snd u ≤[ f ] snd v))
Iso.fun (HomP×-Iso {C = C} {D = D} {f = f}) q =
  HomP×-fst {C = C} {D = D} {f = f} q
  , HomP×-snd {C = C} {D = D} {f = f} q
Iso.inv (HomP×-Iso {C = C} {D = D} {f = f}) (p , q) =
  HomP× {C = C} {D = D} {f = f} p q
Iso.rightInv (HomP×-Iso {C = C} {D = D} {f = f}) _ =
  refl
Iso.leftInv (HomP×-Iso {C = C} {D = D} {f = f}) _ =
  refl

HomP×≃ :
  {C : A → Type ℓ'} {D : A → Type ℓ''}
  {x y : A} {f : x ≤ y} {u : C x × D x} {v : C y × D y}
  → ((λ z → C z × D z) ⊢ u ≤[ f ] v)
    ≃ ((C ⊢ fst u ≤[ f ] fst v) × (D ⊢ snd u ≤[ f ] snd v))
HomP×≃ {C = C} {D = D} {f = f} =
  isoToEquiv (HomP×-Iso {C = C} {D = D} {f = f})

HomPΣ-const :
  {B : Type ℓ''} {C : B → A → Type ℓ'}
  {b : B} {x y : A} {f : x ≤ y}
  {u : C b x} {v : C b y}
  → C b ⊢ u ≤[ f ] v
  → (λ a → Σ B (λ b → C b a)) ⊢ (b , u) ≤[ f ] (b , v)
HomPΣ-const q =
  (λ i → _ , q .fst i)
  , ΣPathP (refl , q .snd .fst)
  , ΣPathP (refl , q .snd .snd)

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

HomPΣ-Iso :
  {C : A → Type ℓ'} {D : (a : A) → C a → Type ℓ''}
  {x y : A} {f : x ≤ y}
  {u : Σ (C x) (D x)} {v : Σ (C y) (D y)}
  → Iso
      ((λ a → Σ (C a) (D a)) ⊢ u ≤[ f ] v)
      (Σ (C ⊢ fst u ≤[ f ] fst v)
        (λ p →
          (λ au → D (fst au) (snd au))
            ⊢ snd u ≤[ Σ≤ f p ] snd v))
Iso.fun (HomPΣ-Iso {C = C} {D = D} {f = f}) q =
  HomPΣ-fst {C = C} {D = D} {f = f} q
  , HomPΣ-snd {C = C} {D = D} {f = f} q
Iso.inv (HomPΣ-Iso {C = C} {D = D} {f = f}) (p , q) =
  HomPΣ {C = C} {D = D} {f = f} p q
Iso.rightInv (HomPΣ-Iso {C = C} {D = D} {f = f}) _ =
  refl
Iso.leftInv (HomPΣ-Iso {C = C} {D = D} {f = f}) _ =
  refl

HomPΣ≃ :
  {C : A → Type ℓ'} {D : (a : A) → C a → Type ℓ''}
  {x y : A} {f : x ≤ y}
  {u : Σ (C x) (D x)} {v : Σ (C y) (D y)}
  → ((λ a → Σ (C a) (D a)) ⊢ u ≤[ f ] v)
    ≃
    (Σ (C ⊢ fst u ≤[ f ] fst v)
      (λ p →
        (λ au → D (fst au) (snd au))
          ⊢ snd u ≤[ Σ≤ f p ] snd v))
HomPΣ≃ {C = C} {D = D} {f = f} =
  isoToEquiv (HomPΣ-Iso {C = C} {D = D} {f = f})

ΣLift :
  {B : Type ℓ''} {C : B → A → Type ℓ'}
  {x y : A} (f : x ≤ y)
  {b₀ b₁ : B}
  → b₀ ≤ b₁
  → C b₀ x
  → C b₁ y
  → Type ℓ'
ΣLift {C = C} f h u v =
  Σ ((i : 𝟚) → C (hom-path h i) (hom-path f i))
    (λ q →
      (PathP (λ i → C (left-endpoint h i) (left-endpoint f i)) (q 𝟎) u)
      ×
      (PathP (λ i → C (right-endpoint h i) (right-endpoint f i)) (q 𝟏) v))
