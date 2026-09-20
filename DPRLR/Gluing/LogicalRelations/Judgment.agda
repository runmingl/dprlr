open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma using () renaming (fst to fstΣ ; snd to sndΣ)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Contravariant
open import DPRLR.Object.Model.Model using (SimpleDirectedCwF)
open import DPRLR.Cubical.Path using (ΣPath→PathP)

module DPRLR.Gluing.LogicalRelations.Judgment
  {ℓS ℓM : Level} (𝓜 : SimpleDirectedCwF ℓS ℓM) where
  infix 4 _≤ᵍ_
  infixl 30 _∘₀_
  infixl 40 _[_]Tm₀

  open SimpleDirectedCwF 𝓜
    renaming
      ( Ctx to Ctxₘ
      ; Ty to Tyₘ
      ; Sub to Subₘ
      ; Tm to Tmₘ
      ; ε to εₘ
      ; _∘_ to _∘ₘ_
      ; _[_]Tm to _[_]Tmₘ
      ; sub-set to sub-setₘ
      ; tm-set to tm-setₘ
      ; tm-thin to tm-thinₘ
      )

  record GluCtx : Type (ℓ-max ℓS (ℓ-suc ℓM)) where
    field
      Γ° : Ctxₘ
      Γ∙ : Subₘ εₘ Γ° → Type ℓM

  open GluCtx public

  record GluSub (Γ Δ : GluCtx) : Type ℓM where
    field
      σ° : Subₘ (Γ° Γ) (Γ° Δ)
      σ∙ : (γ° : Subₘ εₘ (Γ° Γ)) → Γ∙ Γ γ° → Γ∙ Δ (σ° ∘ₘ γ°)

  open GluSub public

  record GluTy : Type (ℓ-max ℓS (ℓ-suc ℓM)) where
    field
      A° : Tyₘ
      A∙ : Tmₘ εₘ A° → Type ℓM
      cA : isContravariant A∙

  open GluTy public

  record GluTm (Γ : GluCtx) (A : GluTy) : Type ℓM where
    field
      M° : Tmₘ (Γ° Γ) (A° A)
      M∙ : (γ° : Subₘ εₘ (Γ° Γ)) (γ∙ : Γ∙ Γ γ°)
        → A∙ A (M° [ γ° ]Tmₘ)

  open GluTm public

  GluSub₀ : GluCtx → Type ℓM
  GluSub₀ Γ = Σ (Subₘ εₘ (Γ° Γ)) (Γ∙ Γ)

  GluTm₀ : GluTy → Type ℓM
  GluTm₀ A = Σ (Tmₘ εₘ (A° A)) (A∙ A)

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
          (tm-thinₘ εₘ (A° A) _ _ (hom-map fstΣ e)
            (hom-map (λ t → t [ γ ]Tmₘ) r))
          ((λ i → hom-path e i .sndΣ)
          , (λ i → left-endpoint e i .sndΣ)
          , (λ i → right-endpoint e i .sndΣ))
    }
