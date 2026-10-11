open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels using (isSetΠ2)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Contravariant
open import DPRLR.Simplicial.PreorderLocalization
open import DPRLR.Object.Model.Model
open import DPRLR.Cubical.Path using (ΣPath→PathP)

module DPRLR.Gluing.LogicalRelations.Judgment
  {ℓS ℓM : Level} (𝓜 : SimpleCwF ℓS ℓM) where
  open import DPRLR.Gluing.Base 𝓜
  infix 4 _≤ᵍ_
  infixl 30 _∘₀_
  infixl 40 _[_]Tm₀

  record GluCtx : Type (ℓ-max ℓS (ℓ-suc ℓM)) where
    field
      Γ° : Ctxₘ
      Γ∙ : ⌞ Subₘ εₘ Γ° ⌟ → Type ℓM
      Γ∙-isSet : (γ° : ⌞ Subₘ εₘ Γ° ⌟) → isSet (Γ∙ γ°)
      cΓ : isContravariant Γ∙

  open GluCtx

  record GluSub (Γ Δ : GluCtx) : Type ℓM where
    field
      σ° : ⌞ Subₘ (Γ° Γ) (Γ° Δ) ⌟
      σ∙ : (γ° : ⌞ Subₘ εₘ (Γ° Γ) ⌟) → Γ∙ Γ γ° → Γ∙ Δ (σ° ∘ₘ γ°)

  open GluSub

  GluSub-isPreorder : (Γ Δ : GluCtx) → isPreorder (GluSub Γ Δ)
  GluSub-isPreorder Γ Δ =
    isPreorder≃
      (isoToEquiv (iso
        (λ (s° , s∙) → record { σ° = s° ; σ∙ = s∙ })
        (λ s → σ° s , σ∙ s)
        (λ _ → refl) (λ _ → refl)))
      (contravariant-total-isPreorder
        {C = λ s° → (γ° : ⌞ Subₘ εₘ (Γ° Γ) ⌟) → Γ∙ Γ γ° → Γ∙ Δ (s° ∘ₘ γ°)}
        (sub-localₘ (Γ° Γ) (Γ° Δ))
        (contravariant-Π λ γ° →
          contravariant-Π λ _ →
            contravariant-reindex (λ s° → s° ∘ₘ γ°) (cΓ Δ))
        (λ s° → isSetΠ2 λ γ° _ → Γ∙-isSet Δ (s° ∘ₘ γ°)))

  record GluTy : Type (ℓ-max ℓS (ℓ-suc ℓM)) where
    field
      A° : Tyₘ
      A∙ : ⌞ Tmₘ εₘ A° ⌟ → Type ℓM
      A∙-isSet : (M° : ⌞ Tmₘ εₘ A° ⌟) → isSet (A∙ M°)
      cA : isContravariant A∙

  open GluTy

  record GluTm (Γ : GluCtx) (A : GluTy) : Type ℓM where
    field
      M° : ⌞ Tmₘ (Γ° Γ) (A° A) ⌟
      M∙ : (γ° : ⌞ Subₘ εₘ (Γ° Γ) ⌟) (γ∙ : Γ∙ Γ γ°)
        → A∙ A (M° [ γ° ]Tmₘ)

  open GluTm

  GluTm-isPreorder : (Γ : GluCtx) (A : GluTy) → isPreorder (GluTm Γ A)
  GluTm-isPreorder Γ A =
    isPreorder≃
      (isoToEquiv (iso
        (λ (m° , m∙) → record { M° = m° ; M∙ = m∙ })
        (λ m → M° m , M∙ m)
        (λ _ → refl) (λ _ → refl)))
      (contravariant-total-isPreorder
        {C = λ m° → (γ° : ⌞ Subₘ εₘ (Γ° Γ) ⌟) (γ∙ : Γ∙ Γ γ°) → A∙ A (m° [ γ° ]Tmₘ)}
        (tm-localₘ (Γ° Γ) (A° A))
        (contravariant-Π λ γ° →
          contravariant-Π λ _ →
            contravariant-reindex (λ m° → m° [ γ° ]Tmₘ) (cA A))
        (λ m° → isSetΠ2 λ γ° _ → A∙-isSet A (m° [ γ° ]Tmₘ)))

  GluSub₀ : GluCtx → Type ℓM
  GluSub₀ Γ = Σ ⌞ Subₘ εₘ (Γ° Γ) ⌟ (Γ∙ Γ)

  GluTm₀ : GluTy → Type ℓM
  GluTm₀ A = Σ ⌞ Tmₘ εₘ (A° A) ⌟ (A∙ A)

  _∘₀_ : {Γ Δ : GluCtx} → GluSub Γ Δ → GluSub₀ Γ → GluSub₀ Δ
  σ ∘₀ (γ , γ∙) = σ° σ ∘ₘ γ , σ∙ σ γ γ∙

  _[_]Tm₀ : {Γ : GluCtx} {A : GluTy} → GluTm Γ A → GluSub₀ Γ → GluTm₀ A
  t [ γ , γ∙ ]Tm₀ = M° t [ γ ]Tmₘ , M∙ t γ γ∙

  GluSub-ext : {Γ Δ : GluCtx} {σ τ : GluSub Γ Δ}
    → (p : σ° σ ≡ σ° τ)
    → ((γ : GluSub₀ Γ) → σ ∘₀ γ ≡ τ ∘₀ γ) → σ ≡ τ
  σ° (GluSub-ext p e i) = p i
  σ∙ (GluSub-ext {Δ = Δ} p e i) γ γ∙ =
    ΣPath→PathP (sub-setₘ εₘ (Γ° Δ)) (λ j → p j ∘ₘ γ) (e (γ , γ∙)) i

  GluTm-ext : {Γ : GluCtx} {A : GluTy} {t u : GluTm Γ A}
    → (p : M° t ≡ M° u)
    → ((γ : GluSub₀ Γ) → t [ γ ]Tm₀ ≡ u [ γ ]Tm₀) → t ≡ u
  M° (GluTm-ext p e i) = p i
  M∙ (GluTm-ext {A = A} p e i) γ γ∙ =
    ΣPath→PathP (tm-setₘ εₘ (A° A)) (λ j → p j [ γ ]Tmₘ) (e (γ , γ∙)) i

  record _≤ᵍ_ {Γ : GluCtx} {A : GluTy}
    (M N : GluTm Γ A) : Type ℓM where
    field
      r° : M° M ≤ M° N
      r∙ : (γ° : ⌞ Subₘ εₘ (Γ° Γ) ⌟) (γ∙ : Γ∙ Γ γ°)
        → A∙ A ⊢ M∙ M γ° γ∙
          ≤[ hom-map (λ t → t [ γ° ]Tmₘ) r° ]
          M∙ N γ° γ∙

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
      let (_ , _ , endpoint) = _≤ᵍ_.r∙ r γ° γ∙ in endpoint i

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

  GluTm-hom : {Γ : GluCtx} {A : GluTy} {t u : GluTm Γ A}
    → M° t ≤ M° u
    → ((γ : GluSub₀ Γ) → t [ γ ]Tm₀ ≤ u [ γ ]Tm₀) → t ≤ u
  GluTm-hom {A = A} {t = t} {u = u} r h = ≤ᵍ→≤ record
    { r° = r
    ; r∙ = λ γ γ∙ →
        let e = h (γ , γ∙) in
        subst (λ f → A∙ A ⊢ M∙ t γ γ∙ ≤[ f ] M∙ u γ γ∙)
          (tm-thinₘ εₘ (A° A) _ _ (hom-map fst e)
            (hom-map (λ t → t [ γ ]Tmₘ) r))
          ((λ i → hom-path e i .snd)
          , (λ i → left-endpoint e i .snd)
          , (λ i → right-endpoint e i .snd))
    }
