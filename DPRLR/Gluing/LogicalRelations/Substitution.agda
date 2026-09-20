-- • ᵍ: operations on glued terms and substitutions in arbitrary contexts,
--   carrying logical-relation evidence for every closing substitution.
-- • ₀: closed base substitutions (GluSub₀) and terms (GluTm₀), each paired
--   with its logical-relation evidence.
-- • Role: ᵍ supplies the glued model; ₀ makes its laws easier to prove
--   pointwise.

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import DPRLR.Cubical.Path using (ΣPathP-subst ; ΣPath→PathP)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import DPRLR.Object.Model.Model using (SimpleDirectedCwF)

module DPRLR.Gluing.LogicalRelations.Substitution
  {ℓS ℓM : Level} (𝓜 : SimpleDirectedCwF ℓS ℓM) where
  open import DPRLR.Gluing.LogicalRelations.Judgment 𝓜

  infixl 40 _[_]Tmᵍ

  open SimpleDirectedCwF 𝓜
    renaming
      ( id to idₘ
      ; ε to εₘ
      ; ε-sub to ε-subₘ
      ; εη to εηₘ
      ; _▷_ to _▷ₘ_
      ; p to pₘ
      ; q to qₘ
      ; ⟨_,_⟩ to ⟨_,_⟩ₘ
      ; _∘_ to _∘ₘ_
      ; _[_]Tm to _[_]Tmₘ
      ; id-left to id-leftₘ
      ; id-right to id-rightₘ
      ; ∘-assoc to ∘-assocₘ
      ; sub-set to sub-setₘ
      ; Tm-id to Tm-idₘ
      ; Tm-∘ to Tm-∘ₘ
      ; tm-set to tm-setₘ
      ; p-⟨⟩ to p-⟨⟩ₘ
      ; q-⟨⟩ to q-⟨⟩ₘ
      ; ▷η to ▷ηₘ
      ; ⟨⟩-∘ to ⟨⟩-∘ₘ
      )

  εᵍ : GluCtx
  GluCtx.Γ° εᵍ = εₘ
  GluCtx.Γ∙ εᵍ _ = Unit*

  ε-subᵍ : {Γ : GluCtx} → GluSub Γ εᵍ
  GluSub.σ° ε-subᵍ = ε-subₘ
  GluSub.σ∙ ε-subᵍ _ _ = tt*

  εηᵍ :
    {Γ : GluCtx}
    (σ : GluSub Γ εᵍ)
    → σ ≡ ε-subᵍ
  GluSub.σ° (εηᵍ σ i) =
    εηₘ (GluSub.σ° σ) i
  GluSub.σ∙ (εηᵍ σ i) γ° γ∙ =
    isPropUnit* (GluSub.σ∙ σ γ° γ∙) tt* i

  idᵍ : (Γ : GluCtx) → GluSub Γ Γ
  GluSub.σ° (idᵍ Γ) = idₘ
  GluSub.σ∙ (idᵍ Γ) γ° γ∙ =
    subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙

  _∘ᵍ_ : {Γ Δ Θ : GluCtx} → GluSub Θ Δ → GluSub Γ Θ → GluSub Γ Δ
  GluSub.σ° (τ ∘ᵍ σ) = GluSub.σ° τ ∘ₘ GluSub.σ° σ
  GluSub.σ∙ (_∘ᵍ_ {Δ = Δ} τ σ) γ° γ∙ =
    subst (GluCtx.Γ∙ Δ)
      (sym (∘-assocₘ (GluSub.σ° τ) (GluSub.σ° σ) γ°))
      (GluSub.σ∙ τ
        (GluSub.σ° σ ∘ₘ γ°)
        (GluSub.σ∙ σ γ° γ∙))

  id-left₀ : (Γ : GluCtx) (γ : GluSub₀ Γ) → idᵍ Γ ∘₀ γ ≡ γ
  id-left₀ Γ (γ , γ∙) =
    sym (ΣPathP-subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ)) γ∙)

  ∘-assoc₀ : {Γ Δ Θ : GluCtx}
    (τ : GluSub Θ Δ) (σ : GluSub Γ Θ) (γ : GluSub₀ Γ)
    → (τ ∘ᵍ σ) ∘₀ γ ≡ τ ∘₀ (σ ∘₀ γ)
  ∘-assoc₀ {Δ = Δ} τ σ (γ , γ∙) =
    sym (ΣPathP-subst (GluCtx.Γ∙ Δ)
      (sym (∘-assocₘ (GluSub.σ° τ) (GluSub.σ° σ) γ))
      (GluSub.σ∙ τ _ (GluSub.σ∙ σ γ γ∙)))

  id-leftᵍ : {Γ Δ : GluCtx} (σ : GluSub Γ Δ) → idᵍ Δ ∘ᵍ σ ≡ σ
  id-leftᵍ {Δ = Δ} σ = GluSub-ext (id-leftₘ (GluSub.σ° σ)) λ γ →
      (idᵍ Δ ∘ᵍ σ) ∘₀ γ
    ≡⟨ ∘-assoc₀ (idᵍ Δ) σ γ ⟩
      idᵍ Δ ∘₀ (σ ∘₀ γ)
    ≡⟨ id-left₀ Δ (σ ∘₀ γ) ⟩
      σ ∘₀ γ
    ∎

  id-rightᵍ : {Γ Δ : GluCtx} (σ : GluSub Γ Δ) → σ ∘ᵍ idᵍ Γ ≡ σ
  id-rightᵍ {Γ = Γ} σ = GluSub-ext (id-rightₘ (GluSub.σ° σ)) λ γ →
      (σ ∘ᵍ idᵍ Γ) ∘₀ γ
    ≡⟨ ∘-assoc₀ σ (idᵍ Γ) γ ⟩
      σ ∘₀ (idᵍ Γ ∘₀ γ)
    ≡⟨ cong (σ ∘₀_) (id-left₀ Γ γ) ⟩
      σ ∘₀ γ
    ∎

  ∘-assocᵍ : {Γ Δ Θ Ξ : GluCtx}
    (ρ : GluSub Θ Ξ) (τ : GluSub Δ Θ) (σ : GluSub Γ Δ)
    → (ρ ∘ᵍ τ) ∘ᵍ σ ≡ ρ ∘ᵍ (τ ∘ᵍ σ)
  ∘-assocᵍ ρ τ σ =
    GluSub-ext (∘-assocₘ (GluSub.σ° ρ) (GluSub.σ° τ) (GluSub.σ° σ)) λ γ →
        ((ρ ∘ᵍ τ) ∘ᵍ σ) ∘₀ γ
      ≡⟨ ∘-assoc₀ (ρ ∘ᵍ τ) σ γ ⟩
        (ρ ∘ᵍ τ) ∘₀ (σ ∘₀ γ)
      ≡⟨ ∘-assoc₀ ρ τ (σ ∘₀ γ) ⟩
        ρ ∘₀ (τ ∘₀ (σ ∘₀ γ))
      ≡⟨ cong (ρ ∘₀_) (sym (∘-assoc₀ τ σ γ)) ⟩
        ρ ∘₀ ((τ ∘ᵍ σ) ∘₀ γ)
      ≡⟨ sym (∘-assoc₀ ρ (τ ∘ᵍ σ) γ) ⟩
        (ρ ∘ᵍ (τ ∘ᵍ σ)) ∘₀ γ
      ∎

  _[_]Tmᵍ :
    {Γ Δ : GluCtx} {A : GluTy}
    → GluTm Δ A
    → GluSub Γ Δ
    → GluTm Γ A
  GluTm.M° (M [ σ ]Tmᵍ) =
    GluTm.M° M [ GluSub.σ° σ ]Tmₘ
  GluTm.M∙ (_[_]Tmᵍ {A = A} M σ) γ° γ∙ =
    subst (GluTy.A∙ A)
      (sym (Tm-∘ₘ (GluTm.M° M) (GluSub.σ° σ) γ°))
      (GluTm.M∙ M
        (GluSub.σ° σ ∘ₘ γ°)
        (GluSub.σ∙ σ γ° γ∙))

  Tm-∘₀ : {Γ Δ : GluCtx} {A : GluTy}
    (t : GluTm Δ A) (σ : GluSub Γ Δ) (γ : GluSub₀ Γ)
    → (t [ σ ]Tmᵍ) [ γ ]Tm₀ ≡ t [ σ ∘₀ γ ]Tm₀
  Tm-∘₀ {A = A} t σ (γ , γ∙) =
    sym (ΣPathP-subst (GluTy.A∙ A) (sym (Tm-∘ₘ (GluTm.M° t) (GluSub.σ° σ) γ))
      (GluTm.M∙ t _ (GluSub.σ∙ σ γ γ∙)))

  Tm-idᵍ : {Γ : GluCtx} {A : GluTy} (t : GluTm Γ A)
    → t [ idᵍ Γ ]Tmᵍ ≡ t
  Tm-idᵍ {Γ = Γ} t = GluTm-ext (Tm-idₘ (GluTm.M° t)) λ γ →
      (t [ idᵍ Γ ]Tmᵍ) [ γ ]Tm₀
    ≡⟨ Tm-∘₀ t (idᵍ Γ) γ ⟩
      t [ idᵍ Γ ∘₀ γ ]Tm₀
    ≡⟨ cong (t [_]Tm₀) (id-left₀ Γ γ) ⟩
      t [ γ ]Tm₀
    ∎

  Tm-∘ᵍ : {Γ Δ Θ : GluCtx} {A : GluTy}
    (t : GluTm Θ A) (τ : GluSub Δ Θ) (σ : GluSub Γ Δ)
    → (t [ τ ]Tmᵍ) [ σ ]Tmᵍ ≡ t [ τ ∘ᵍ σ ]Tmᵍ
  Tm-∘ᵍ t τ σ =
    GluTm-ext (Tm-∘ₘ (GluTm.M° t) (GluSub.σ° τ) (GluSub.σ° σ)) λ γ →
        ((t [ τ ]Tmᵍ) [ σ ]Tmᵍ) [ γ ]Tm₀
      ≡⟨ Tm-∘₀ (t [ τ ]Tmᵍ) σ γ ⟩
        (t [ τ ]Tmᵍ) [ σ ∘₀ γ ]Tm₀
      ≡⟨ Tm-∘₀ t τ (σ ∘₀ γ) ⟩
        t [ τ ∘₀ (σ ∘₀ γ) ]Tm₀
      ≡⟨ cong (t [_]Tm₀) (sym (∘-assoc₀ τ σ γ)) ⟩
        t [ (τ ∘ᵍ σ) ∘₀ γ ]Tm₀
      ≡⟨ sym (Tm-∘₀ t (τ ∘ᵍ σ) γ) ⟩
        (t [ τ ∘ᵍ σ ]Tmᵍ) [ γ ]Tm₀
      ∎

  _▷ᵍ_ : GluCtx → GluTy → GluCtx
  GluCtx.Γ° (Γ ▷ᵍ A) =
    GluCtx.Γ° Γ ▷ₘ GluTy.A° A
  GluCtx.Γ∙ (Γ ▷ᵍ A) δ° =
    Σ (GluCtx.Γ∙ Γ (pₘ ∘ₘ δ°))
      (λ _ → GluTy.A∙ A (qₘ [ δ° ]Tmₘ))

  pᵍ : {Γ : GluCtx} {A : GluTy} → GluSub (Γ ▷ᵍ A) Γ
  GluSub.σ° pᵍ = pₘ
  GluSub.σ∙ pᵍ δ° δ∙ = fst δ∙

  qᵍ : {Γ : GluCtx} {A : GluTy} → GluTm (Γ ▷ᵍ A) A
  GluTm.M° qᵍ = qₘ
  GluTm.M∙ qᵍ δ° δ∙ = snd δ∙

  ⟨_,_⟩₀ : {Γ : GluCtx} {A : GluTy}
    → GluSub₀ Γ → GluTm₀ A → GluSub₀ (Γ ▷ᵍ A)
  ⟨_,_⟩₀ {Γ} {A} (γ , γ∙) (t , t∙) = ⟨ γ , t ⟩ₘ
    , subst (GluCtx.Γ∙ Γ) (sym (p-⟨⟩ₘ γ t)) γ∙
    , subst (GluTy.A∙ A) (sym (q-⟨⟩ₘ γ t)) t∙

  p-⟨⟩₀ : {Γ : GluCtx} {A : GluTy}
    (γ : GluSub₀ Γ) (t : GluTm₀ A)
    → pᵍ {Γ = Γ} {A = A} ∘₀ ⟨_,_⟩₀ {A = A} γ t ≡ γ
  p-⟨⟩₀ {Γ} (γ , γ∙) (t , t∙) =
    sym (ΣPathP-subst (GluCtx.Γ∙ Γ) (sym (p-⟨⟩ₘ γ t)) γ∙)

  q-⟨⟩₀ : {Γ : GluCtx} {A : GluTy}
    (γ : GluSub₀ Γ) (t : GluTm₀ A)
    → qᵍ {Γ = Γ} {A = A} [ ⟨_,_⟩₀ {A = A} γ t ]Tm₀ ≡ t
  q-⟨⟩₀ {A = A} (γ , γ∙) (t , t∙) =
    sym (ΣPathP-subst (GluTy.A∙ A) (sym (q-⟨⟩ₘ γ t)) t∙)

  ▷η₀ : {Γ : GluCtx} {A : GluTy} (δ : GluSub₀ (Γ ▷ᵍ A))
    → ⟨_,_⟩₀ {Γ} {A} (pᵍ {Γ} {A} ∘₀ δ) (qᵍ {Γ} {A} [ δ ]Tm₀) ≡ δ
  ▷η₀ {Γ} {A} (δ , δ∙) = ΣPathP (base , λ i → ctx i , arg i)
    where
    base : ⟨ pₘ ∘ₘ δ , qₘ [ δ ]Tmₘ ⟩ₘ ≡ δ
    base =
        ⟨ pₘ ∘ₘ δ , qₘ [ δ ]Tmₘ ⟩ₘ
      ≡⟨ sym (⟨⟩-∘ₘ pₘ qₘ δ) ⟩
        ⟨ pₘ , qₘ ⟩ₘ ∘ₘ δ
      ≡⟨ cong (λ σ → σ ∘ₘ δ) ▷ηₘ ⟩
        idₘ ∘ₘ δ
      ≡⟨ id-leftₘ δ ⟩
        δ
      ∎

    ctx : PathP (λ i → GluCtx.Γ∙ Γ (pₘ ∘ₘ base i))
      (subst (GluCtx.Γ∙ Γ) (sym (p-⟨⟩ₘ (pₘ ∘ₘ δ) (qₘ [ δ ]Tmₘ))) (fst δ∙))
      (fst δ∙)
    ctx = ΣPath→PathP (sub-setₘ εₘ (GluCtx.Γ° Γ)) (cong (pₘ ∘ₘ_) base)
      (p-⟨⟩₀ {Γ} {A} (pₘ ∘ₘ δ , fst δ∙) (qₘ [ δ ]Tmₘ , snd δ∙))

    arg : PathP (λ i → GluTy.A∙ A (qₘ [ base i ]Tmₘ))
      (subst (GluTy.A∙ A) (sym (q-⟨⟩ₘ (pₘ ∘ₘ δ) (qₘ [ δ ]Tmₘ))) (snd δ∙))
      (snd δ∙)
    arg = ΣPath→PathP (tm-setₘ εₘ (GluTy.A° A)) (cong (qₘ [_]Tmₘ) base)
      (q-⟨⟩₀ {Γ} {A} (pₘ ∘ₘ δ , fst δ∙) (qₘ [ δ ]Tmₘ , snd δ∙))

  ⟨_,_⟩ᵍ : {Γ Δ : GluCtx} {A : GluTy}
    → GluSub Γ Δ → GluTm Γ A → GluSub Γ (Δ ▷ᵍ A)
  GluSub.σ° ⟨ σ , t ⟩ᵍ = ⟨ GluSub.σ° σ , GluTm.M° t ⟩ₘ
  GluSub.σ∙ (⟨_,_⟩ᵍ {Δ = Δ} {A = A} σ t) γ γ∙ =
    subst (GluCtx.Γ∙ (Δ ▷ᵍ A)) (sym (⟨⟩-∘ₘ (GluSub.σ° σ) (GluTm.M° t) γ))
      (snd (⟨_,_⟩₀ {A = A} (σ ∘₀ (γ , γ∙)) (t [ γ , γ∙ ]Tm₀)))

  ⟨⟩-∘₀ : {Γ Δ : GluCtx} {A : GluTy}
    (σ : GluSub Γ Δ) (t : GluTm Γ A) (γ : GluSub₀ Γ)
    → ⟨ σ , t ⟩ᵍ ∘₀ γ ≡ ⟨_,_⟩₀ {A = A} (σ ∘₀ γ) (t [ γ ]Tm₀)
  ⟨⟩-∘₀ {Δ = Δ} {A = A} σ t (γ , γ∙) =
    sym (ΣPathP-subst (GluCtx.Γ∙ (Δ ▷ᵍ A))
      (sym (⟨⟩-∘ₘ (GluSub.σ° σ) (GluTm.M° t) γ))
      (snd (⟨_,_⟩₀ {A = A} (σ ∘₀ (γ , γ∙)) (t [ γ , γ∙ ]Tm₀))))

  liftᵍ : {Γ Δ : GluCtx} {A : GluTy}
    → GluSub Γ Δ → GluSub (Γ ▷ᵍ A) (Δ ▷ᵍ A)
  liftᵍ {Γ} {A = A} σ = ⟨ σ ∘ᵍ pᵍ {Γ} {A} , qᵍ {Γ} {A} ⟩ᵍ

  lift-⟨⟩₀ : {Γ Δ : GluCtx} {A : GluTy}
    (σ : GluSub Γ Δ) (γ : GluSub₀ Γ) (t : GluTm₀ A)
    → liftᵍ {A = A} σ ∘₀ ⟨_,_⟩₀ {A = A} γ t
      ≡ ⟨_,_⟩₀ {A = A} (σ ∘₀ γ) t
  lift-⟨⟩₀ {Γ} {A = A} σ γ t =
      liftᵍ {A = A} σ ∘₀ δ
    ≡⟨ ⟨⟩-∘₀ (σ ∘ᵍ pᵍ {Γ} {A}) (qᵍ {Γ} {A}) δ ⟩
      ⟨_,_⟩₀ {A = A} ((σ ∘ᵍ pᵍ {Γ} {A}) ∘₀ δ) (qᵍ {Γ} {A} [ δ ]Tm₀)
    ≡⟨ cong (λ θ → ⟨_,_⟩₀ {A = A} θ (qᵍ {Γ} {A} [ δ ]Tm₀))
         (∘-assoc₀ σ (pᵍ {Γ} {A}) δ) ⟩
      ⟨_,_⟩₀ {A = A} (σ ∘₀ (pᵍ {Γ} {A} ∘₀ δ)) (qᵍ {Γ} {A} [ δ ]Tm₀)
    ≡⟨ cong₂ (⟨_,_⟩₀ {A = A})
         (cong (σ ∘₀_) (p-⟨⟩₀ {A = A} γ t)) (q-⟨⟩₀ {A = A} γ t) ⟩
      ⟨_,_⟩₀ {A = A} (σ ∘₀ γ) t
    ∎
    where
    δ : GluSub₀ (Γ ▷ᵍ A)
    δ = ⟨_,_⟩₀ {A = A} γ t

  ⟨id⟩-∘₀ : {Γ : GluCtx} {A : GluTy}
    (t : GluTm Γ A) (γ : GluSub₀ Γ)
    → ⟨ idᵍ Γ , t ⟩ᵍ ∘₀ γ ≡ ⟨_,_⟩₀ {A = A} γ (t [ γ ]Tm₀)
  ⟨id⟩-∘₀ {Γ} {A} t γ =
      ⟨ idᵍ Γ , t ⟩ᵍ ∘₀ γ
    ≡⟨ ⟨⟩-∘₀ (idᵍ Γ) t γ ⟩
      ⟨_,_⟩₀ {A = A} (idᵍ Γ ∘₀ γ) (t [ γ ]Tm₀)
    ≡⟨ cong (λ δ → ⟨_,_⟩₀ {A = A} δ (t [ γ ]Tm₀)) (id-left₀ Γ γ) ⟩
      ⟨_,_⟩₀ {A = A} γ (t [ γ ]Tm₀)
    ∎

  p-⟨⟩ᵍ : {Γ Δ : GluCtx} {A : GluTy}
    (σ : GluSub Γ Δ) (t : GluTm Γ A) → pᵍ {A = A} ∘ᵍ ⟨ σ , t ⟩ᵍ ≡ σ
  p-⟨⟩ᵍ {Δ = Δ} {A = A} σ t = GluSub-ext (p-⟨⟩ₘ (GluSub.σ° σ) (GluTm.M° t)) λ γ →
      (pᵍ {Δ} {A} ∘ᵍ ⟨ σ , t ⟩ᵍ) ∘₀ γ
    ≡⟨ ∘-assoc₀ (pᵍ {Δ} {A}) ⟨ σ , t ⟩ᵍ γ ⟩
      pᵍ {Δ} {A} ∘₀ (⟨ σ , t ⟩ᵍ ∘₀ γ)
    ≡⟨ cong (pᵍ {Δ} {A} ∘₀_) (⟨⟩-∘₀ σ t γ) ⟩
      pᵍ {Δ} {A} ∘₀ ⟨_,_⟩₀ {A = A} (σ ∘₀ γ) (t [ γ ]Tm₀)
    ≡⟨ p-⟨⟩₀ {A = A} (σ ∘₀ γ) (t [ γ ]Tm₀) ⟩
      σ ∘₀ γ
    ∎

  q-⟨⟩ᵍ : {Γ Δ : GluCtx} {A : GluTy}
    (σ : GluSub Γ Δ) (t : GluTm Γ A) → qᵍ {Δ} {A} [ ⟨ σ , t ⟩ᵍ ]Tmᵍ ≡ t
  q-⟨⟩ᵍ {Δ = Δ} {A = A} σ t = GluTm-ext (q-⟨⟩ₘ (GluSub.σ° σ) (GluTm.M° t)) λ γ →
      (qᵍ {Δ} {A} [ ⟨ σ , t ⟩ᵍ ]Tmᵍ) [ γ ]Tm₀
    ≡⟨ Tm-∘₀ (qᵍ {Δ} {A}) ⟨ σ , t ⟩ᵍ γ ⟩
      qᵍ {Δ} {A} [ ⟨ σ , t ⟩ᵍ ∘₀ γ ]Tm₀
    ≡⟨ cong (qᵍ {Δ} {A} [_]Tm₀) (⟨⟩-∘₀ σ t γ) ⟩
      qᵍ {Δ} {A} [ ⟨_,_⟩₀ {A = A} (σ ∘₀ γ) (t [ γ ]Tm₀) ]Tm₀
    ≡⟨ q-⟨⟩₀ {A = A} (σ ∘₀ γ) (t [ γ ]Tm₀) ⟩
      t [ γ ]Tm₀
    ∎

  ▷ηᵍ : {Γ : GluCtx} {A : GluTy}
    → ⟨ pᵍ {Γ = Γ} {A = A} , qᵍ {Γ} {A} ⟩ᵍ ≡ idᵍ (Γ ▷ᵍ A)
  ▷ηᵍ {Γ} {A} = GluSub-ext ▷ηₘ λ δ →
      ⟨ pᵍ {Γ} {A} , qᵍ {Γ} {A} ⟩ᵍ ∘₀ δ
    ≡⟨ ⟨⟩-∘₀ (pᵍ {Γ} {A}) (qᵍ {Γ} {A}) δ ⟩
      ⟨_,_⟩₀ {A = A} (pᵍ {Γ} {A} ∘₀ δ) (qᵍ {Γ} {A} [ δ ]Tm₀)
    ≡⟨ ▷η₀ {Γ} {A} δ ⟩
      δ
    ≡⟨ sym (id-left₀ (Γ ▷ᵍ A) δ) ⟩
      idᵍ (Γ ▷ᵍ A) ∘₀ δ
    ∎

  ⟨⟩-∘ᵍ : {Γ Δ Θ : GluCtx} {A : GluTy}
    (σ : GluSub Γ Δ) (t : GluTm Γ A) (ρ : GluSub Θ Γ)
    → ⟨ σ , t ⟩ᵍ ∘ᵍ ρ ≡ ⟨ σ ∘ᵍ ρ , t [ ρ ]Tmᵍ ⟩ᵍ
  ⟨⟩-∘ᵍ {A = A} σ t ρ =
    GluSub-ext (⟨⟩-∘ₘ (GluSub.σ° σ) (GluTm.M° t) (GluSub.σ° ρ)) λ γ →
        (⟨ σ , t ⟩ᵍ ∘ᵍ ρ) ∘₀ γ
      ≡⟨ ∘-assoc₀ ⟨ σ , t ⟩ᵍ ρ γ ⟩
        ⟨ σ , t ⟩ᵍ ∘₀ (ρ ∘₀ γ)
      ≡⟨ ⟨⟩-∘₀ σ t (ρ ∘₀ γ) ⟩
        ⟨_,_⟩₀ {A = A} (σ ∘₀ (ρ ∘₀ γ)) (t [ ρ ∘₀ γ ]Tm₀)
      ≡⟨ cong₂ (⟨_,_⟩₀ {A = A}) (sym (∘-assoc₀ σ ρ γ)) (sym (Tm-∘₀ t ρ γ)) ⟩
        ⟨_,_⟩₀ {A = A} ((σ ∘ᵍ ρ) ∘₀ γ) ((t [ ρ ]Tmᵍ) [ γ ]Tm₀)
      ≡⟨ sym (⟨⟩-∘₀ (σ ∘ᵍ ρ) (t [ ρ ]Tmᵍ) γ) ⟩
        ⟨ σ ∘ᵍ ρ , t [ ρ ]Tmᵍ ⟩ᵍ ∘₀ γ
      ∎
