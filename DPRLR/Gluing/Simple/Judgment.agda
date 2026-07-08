module DPRLR.Gluing.Simple.Judgment where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Contravariant
open import DPRLR.Object.Simple.Model

module _ {ℓM : Level} (𝓜 : SimpleDirectedCwF ℓM) where
  infix 4 _≤ᵍ_

  open SimpleDirectedCwF 𝓜
    renaming
      ( Ctx to Ctxₘ
      ; Ty to Tyₘ
      ; Sub to Subₘ
      ; Tm to Tmₘ
      ; ε to εₘ
      ; _∘_ to _∘ₘ_
      ; _[_]Tm to _[_]Tmₘ
      )

  record GluCtx : Type (ℓ-suc ℓM) where
    field
      Γ° : Ctxₘ
      Γ∙ : Subₘ εₘ Γ° → Type ℓM

  open GluCtx public

  record GluSub (Γ Δ : GluCtx) : Type (ℓ-suc ℓM) where
    field
      σ° : Subₘ (Γ° Γ) (Γ° Δ)
      σ∙ : (γ° : Subₘ εₘ (Γ° Γ)) → Γ∙ Γ γ° → Γ∙ Δ (σ° ∘ₘ γ°)

  open GluSub public

  record GluTy : Type (ℓ-suc ℓM) where
    field
      A° : Tyₘ
      A∙ : Tmₘ εₘ A° → Type ℓM
      cA : isContravariant A∙

  open GluTy public

  record GluTm (Γ : GluCtx) (A : GluTy) : Type (ℓ-suc ℓM) where
    field
      M° : Tmₘ (Γ° Γ) (A° A)
      M∙ : (γ° : Subₘ εₘ (Γ° Γ)) (γ∙ : Γ∙ Γ γ°)
        → A∙ A (M° [ γ° ]Tmₘ)

  open GluTm public

  record _≤ᵍ_ {Γ : GluCtx} {A : GluTy}
    (M N : GluTm Γ A) : Type (ℓ-suc ℓM) where
    field
      r° : M° M ≤ M° N
      r∙ : (γ° : Subₘ εₘ (Γ° Γ)) (γ∙ : Γ∙ Γ γ°)
        → A∙ A ⊢ M∙ M γ° γ∙
          ≤[ hom-map (λ t → t [ γ° ]Tmₘ) r° ]
          M∙ N γ° γ∙

  open _≤ᵍ_ public

  ≤ᵍ→≤ :
    {Γ : GluCtx} {A : GluTy} {M N : GluTm Γ A}
    → M ≤ᵍ N
    → M ≤ N
  ≤ᵍ→≤ {M = M} {N = N} r =
    (λ i →
      record
        { M° = hom-path (_≤ᵍ_.r° r) i
        ; M∙ = λ γ° γ∙ →
            let (q , _) = _≤ᵍ_.r∙ r γ° γ∙ in q i
        })
    , left
    , right
    where
    left : _ ≡ M
    GluTm.M° (left i) = left-endpoint (_≤ᵍ_.r° r) i
    GluTm.M∙ (left i) γ° γ∙ =
      let (_ , l , _) = _≤ᵍ_.r∙ r γ° γ∙ in l i

    right : _ ≡ N
    GluTm.M° (right i) = right-endpoint (_≤ᵍ_.r° r) i
    GluTm.M∙ (right i) γ° γ∙ =
      let (_ , _ , r′) = _≤ᵍ_.r∙ r γ° γ∙ in r′ i

  ≤→≤ᵍ :
    {Γ : GluCtx} {A : GluTy} {M N : GluTm Γ A}
    → M ≤ N
    → M ≤ᵍ N
  _≤ᵍ_.r° (≤→≤ᵍ h) = hom-map GluTm.M° h
  _≤ᵍ_.r∙ (≤→≤ᵍ h) γ° γ∙ =
    (λ i → GluTm.M∙ (hom-path h i) γ° γ∙)
    , (λ i → GluTm.M∙ (left-endpoint h i) γ° γ∙)
    , (λ i → GluTm.M∙ (right-endpoint h i) γ° γ∙)

  ≤ᵍIso≤ :
    {Γ : GluCtx} {A : GluTy} (M N : GluTm Γ A)
    → Iso (M ≤ᵍ N) (M ≤ N)
  Iso.fun (≤ᵍIso≤ M N) = ≤ᵍ→≤
  Iso.inv (≤ᵍIso≤ M N) = ≤→≤ᵍ
  Iso.rightInv (≤ᵍIso≤ M N) h = refl
  Iso.leftInv (≤ᵍIso≤ M N) r = refl

  ≤ᵍ≃≤ :
    {Γ : GluCtx} {A : GluTy} (M N : GluTm Γ A)
    → (M ≤ᵍ N) ≃ (M ≤ N)
  ≤ᵍ≃≤ M N = isoToEquiv (≤ᵍIso≤ M N)
