module DPRLR.Gluing.Simple.Substitution where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import DPRLR.Object.Simple.Model
open import DPRLR.Gluing.Simple.Judgment

module _ {ℓM : Level} (𝓜 : SimpleDirectedCwF ℓM) where
  infixl 40 _[_]Tmᵍ

  open SimpleDirectedCwF 𝓜
    renaming
      ( Ctx to Ctxₘ
      ; Ty to Tyₘ
      ; Sub to Subₘ
      ; Tm to Tmₘ
      ; id to idₘ
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

  εᵍ : GluCtx 𝓜
  GluCtx.Γ° εᵍ = εₘ
  GluCtx.Γ∙ εᵍ _ = Unit*

  ε-subᵍ : {Γ : GluCtx 𝓜} → GluSub 𝓜 Γ εᵍ
  GluSub.σ° ε-subᵍ = ε-subₘ
  GluSub.σ∙ ε-subᵍ _ _ = tt*

  εηᵍ :
    {Γ : GluCtx 𝓜}
    (σ : GluSub 𝓜 Γ εᵍ)
    → σ ≡ ε-subᵍ
  GluSub.σ° (εηᵍ σ i) =
    εηₘ (GluSub.σ° σ) i
  GluSub.σ∙ (εηᵍ σ i) γ° γ∙ =
    isPropUnit* (GluSub.σ∙ σ γ° γ∙) tt* i

  idᵍ : (Γ : GluCtx 𝓜) → GluSub 𝓜 Γ Γ
  GluSub.σ° (idᵍ Γ) = idₘ
  GluSub.σ∙ (idᵍ Γ) γ° γ∙ =
    subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙

  _∘ᵍ_ : {Γ Δ Θ : GluCtx 𝓜} → GluSub 𝓜 Θ Δ → GluSub 𝓜 Γ Θ → GluSub 𝓜 Γ Δ
  GluSub.σ° (τ ∘ᵍ σ) = GluSub.σ° τ ∘ₘ GluSub.σ° σ
  GluSub.σ∙ (_∘ᵍ_ {Δ = Δ} τ σ) γ° γ∙ =
    subst (GluCtx.Γ∙ Δ)
      (sym (∘-assocₘ (GluSub.σ° τ) (GluSub.σ° σ) γ°))
      (GluSub.σ∙ τ
        (GluSub.σ° σ ∘ₘ γ°)
        (GluSub.σ∙ σ γ° γ∙))

  id-leftᵍ :
    {Γ Δ : GluCtx 𝓜}
    (σ : GluSub 𝓜 Γ Δ)
    → idᵍ Δ ∘ᵍ σ ≡ σ
  GluSub.σ° (id-leftᵍ σ i) =
    id-leftₘ (GluSub.σ° σ) i
  GluSub.σ∙ (id-leftᵍ {Γ = Γ} {Δ = Δ} σ i) γ° γ∙ =
    path i
    where
    v = GluSub.σ∙ σ γ° γ∙

    P :
      (idₘ ∘ₘ GluSub.σ° σ) ∘ₘ γ°
      ≡ GluSub.σ° σ ∘ₘ γ°
    P i = id-leftₘ (GluSub.σ° σ) i ∘ₘ γ°

    Q :
      GluSub.σ° σ ∘ₘ γ°
      ≡ (idₘ ∘ₘ GluSub.σ° σ) ∘ₘ γ°
    Q =
      sym (id-leftₘ (GluSub.σ° σ ∘ₘ γ°))
      ∙ sym (∘-assocₘ idₘ (GluSub.σ° σ) γ°)

    Q≡symP :
      Q ≡ sym P
    Q≡symP =
      sub-setₘ εₘ (GluCtx.Γ° Δ)
        (GluSub.σ° σ ∘ₘ γ°)
        ((idₘ ∘ₘ GluSub.σ° σ) ∘ₘ γ°)
        Q
        (sym P)

    actual :
      GluCtx.Γ∙ Δ ((idₘ ∘ₘ GluSub.σ° σ) ∘ₘ γ°)
    actual =
      subst (GluCtx.Γ∙ Δ)
        (sym (∘-assocₘ idₘ (GluSub.σ° σ) γ°))
        (subst (GluCtx.Γ∙ Δ)
          (sym (id-leftₘ (GluSub.σ° σ ∘ₘ γ°)))
          v)

    actual≡substQ :
      actual ≡ subst (GluCtx.Γ∙ Δ) Q v
    actual≡substQ =
      sym
        (substComposite
          (GluCtx.Γ∙ Δ)
          (sym (id-leftₘ (GluSub.σ° σ ∘ₘ γ°)))
          (sym (∘-assocₘ idₘ (GluSub.σ° σ) γ°))
          v)

    path-symP :
      PathP
        (λ i → GluCtx.Γ∙ Δ (P i))
        (subst (GluCtx.Γ∙ Δ) (sym P) v)
        v
    path-symP i =
      subst-filler (GluCtx.Γ∙ Δ) (sym P) v (~ i)

    path-Q :
      PathP
        (λ i → GluCtx.Γ∙ Δ (P i))
        (subst (GluCtx.Γ∙ Δ) Q v)
        v
    path-Q =
      subst
        (λ q →
          PathP
            (λ i → GluCtx.Γ∙ Δ (P i))
            (subst (GluCtx.Γ∙ Δ) q v)
            v)
        (sym Q≡symP)
        path-symP

    path :
      PathP
        (λ i → GluCtx.Γ∙ Δ (P i))
        actual
        v
    path =
      subst
        (λ u →
          PathP
            (λ i → GluCtx.Γ∙ Δ (P i))
            u
            v)
        (sym actual≡substQ)
        path-Q

  id-rightᵍ :
    {Γ Δ : GluCtx 𝓜}
    (σ : GluSub 𝓜 Γ Δ)
    → σ ∘ᵍ idᵍ Γ ≡ σ
  GluSub.σ° (id-rightᵍ σ i) =
    id-rightₘ (GluSub.σ° σ) i
  GluSub.σ∙ (id-rightᵍ {Γ = Γ} {Δ = Δ} σ i) γ° γ∙ =
    path i
    where
    v = GluSub.σ∙ σ γ° γ∙

    idγ : Subₘ εₘ (GluCtx.Γ° Γ)
    idγ = idₘ ∘ₘ γ°

    idγ-path :
      idγ ≡ γ°
    idγ-path =
      id-leftₘ γ°

    idγ∙ :
      GluCtx.Γ∙ Γ idγ
    idγ∙ =
      subst (GluCtx.Γ∙ Γ) (sym idγ-path) γ∙

    w :
      GluCtx.Γ∙ Δ (GluSub.σ° σ ∘ₘ idγ)
    w =
      GluSub.σ∙ σ idγ idγ∙

    actual :
      GluCtx.Γ∙ Δ ((GluSub.σ° σ ∘ₘ idₘ) ∘ₘ γ°)
    actual =
      subst (GluCtx.Γ∙ Δ)
        (sym (∘-assocₘ (GluSub.σ° σ) idₘ γ°))
        w

    P :
      (GluSub.σ° σ ∘ₘ idₘ) ∘ₘ γ°
      ≡ GluSub.σ° σ ∘ₘ γ°
    P i = id-rightₘ (GluSub.σ° σ) i ∘ₘ γ°

    Q :
      (GluSub.σ° σ ∘ₘ idₘ) ∘ₘ γ°
      ≡ GluSub.σ° σ ∘ₘ γ°
    Q =
      ∘-assocₘ (GluSub.σ° σ) idₘ γ°
      ∙ cong (λ δ → GluSub.σ° σ ∘ₘ δ) idγ-path

    Q≡P :
      Q ≡ P
    Q≡P =
      sub-setₘ εₘ (GluCtx.Γ° Δ)
        ((GluSub.σ° σ ∘ₘ idₘ) ∘ₘ γ°)
        (GluSub.σ° σ ∘ₘ γ°)
        Q
        P

    step₁ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (∘-assocₘ (GluSub.σ° σ) idₘ γ° i))
        actual
        w
    step₁ i =
      subst-filler
        (GluCtx.Γ∙ Δ)
        (sym (∘-assocₘ (GluSub.σ° σ) idₘ γ°))
        w
        (~ i)

    γ∙-path :
      PathP
        (λ i → GluCtx.Γ∙ Γ (idγ-path i))
        idγ∙
        γ∙
    γ∙-path i =
      subst-filler (GluCtx.Γ∙ Γ) (sym idγ-path) γ∙ (~ i)

    step₂ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (GluSub.σ° σ ∘ₘ idγ-path i))
        w
        v
    step₂ i =
      GluSub.σ∙ σ (idγ-path i) (γ∙-path i)

    path-Q :
      PathP
        (λ i → GluCtx.Γ∙ Δ (Q i))
        actual
        v
    path-Q =
      compPathP' {B = GluCtx.Γ∙ Δ} step₁ step₂

    path :
      PathP
        (λ i → GluCtx.Γ∙ Δ (P i))
        actual
        v
    path =
      subst
        (λ q →
          PathP
            (λ i → GluCtx.Γ∙ Δ (q i))
            actual
            v)
        Q≡P
        path-Q

  ∘-assocᵍ :
    {Γ Δ Θ Ξ : GluCtx 𝓜}
    (ρ : GluSub 𝓜 Θ Ξ)
    (τ : GluSub 𝓜 Δ Θ)
    (σ : GluSub 𝓜 Γ Δ)
    → (ρ ∘ᵍ τ) ∘ᵍ σ ≡ ρ ∘ᵍ (τ ∘ᵍ σ)
  GluSub.σ° (∘-assocᵍ ρ τ σ i) =
    ∘-assocₘ (GluSub.σ° ρ) (GluSub.σ° τ) (GluSub.σ° σ) i
  GluSub.σ∙
    (∘-assocᵍ {Γ = Γ} {Δ = Δ} {Θ = Θ} {Ξ = Ξ} ρ τ σ i)
    γ° γ∙ =
    path i
    where
    ρ₀ = GluSub.σ° ρ
    τ₀ = GluSub.σ° τ
    σ₀ = GluSub.σ° σ

    σγ : Subₘ εₘ (GluCtx.Γ° Δ)
    σγ = σ₀ ∘ₘ γ°

    τσγ : Subₘ εₘ (GluCtx.Γ° Θ)
    τσγ = τ₀ ∘ₘ σγ

    τ∘σγ : Subₘ εₘ (GluCtx.Γ° Θ)
    τ∘σγ = (τ₀ ∘ₘ σ₀) ∘ₘ γ°

    σγ∙ :
      GluCtx.Γ∙ Δ σγ
    σγ∙ =
      GluSub.σ∙ σ γ° γ∙

    τσγ∙ :
      GluCtx.Γ∙ Θ τσγ
    τσγ∙ =
      GluSub.σ∙ τ σγ σγ∙

    base :
      GluCtx.Γ∙ Ξ (ρ₀ ∘ₘ τσγ)
    base =
      GluSub.σ∙ ρ τσγ τσγ∙

    left-mid :
      GluCtx.Γ∙ Ξ ((ρ₀ ∘ₘ τ₀) ∘ₘ σγ)
    left-mid =
      subst (GluCtx.Γ∙ Ξ)
        (sym (∘-assocₘ ρ₀ τ₀ σγ))
        base

    actual-left :
      GluCtx.Γ∙ Ξ (((ρ₀ ∘ₘ τ₀) ∘ₘ σ₀) ∘ₘ γ°)
    actual-left =
      subst (GluCtx.Γ∙ Ξ)
        (sym (∘-assocₘ (ρ₀ ∘ₘ τ₀) σ₀ γ°))
        left-mid

    τ-path :
      τσγ ≡ τ∘σγ
    τ-path =
      sym (∘-assocₘ τ₀ σ₀ γ°)

    τ∘σγ∙ :
      GluCtx.Γ∙ Θ τ∘σγ
    τ∘σγ∙ =
      subst (GluCtx.Γ∙ Θ) τ-path τσγ∙

    right-mid :
      GluCtx.Γ∙ Ξ (ρ₀ ∘ₘ τ∘σγ)
    right-mid =
      GluSub.σ∙ ρ τ∘σγ τ∘σγ∙

    actual-right :
      GluCtx.Γ∙ Ξ ((ρ₀ ∘ₘ (τ₀ ∘ₘ σ₀)) ∘ₘ γ°)
    actual-right =
      subst (GluCtx.Γ∙ Ξ)
        (sym (∘-assocₘ ρ₀ (τ₀ ∘ₘ σ₀) γ°))
        right-mid

    P :
      ((ρ₀ ∘ₘ τ₀) ∘ₘ σ₀) ∘ₘ γ°
      ≡ (ρ₀ ∘ₘ (τ₀ ∘ₘ σ₀)) ∘ₘ γ°
    P i = ∘-assocₘ ρ₀ τ₀ σ₀ i ∘ₘ γ°

    Q-left :
      ((ρ₀ ∘ₘ τ₀) ∘ₘ σ₀) ∘ₘ γ°
      ≡ ρ₀ ∘ₘ τσγ
    Q-left =
      ∘-assocₘ (ρ₀ ∘ₘ τ₀) σ₀ γ°
      ∙ ∘-assocₘ ρ₀ τ₀ σγ

    Q-right :
      ρ₀ ∘ₘ τσγ
      ≡ (ρ₀ ∘ₘ (τ₀ ∘ₘ σ₀)) ∘ₘ γ°
    Q-right =
      cong (λ δ → ρ₀ ∘ₘ δ) τ-path
      ∙ sym (∘-assocₘ ρ₀ (τ₀ ∘ₘ σ₀) γ°)

    Q :
      ((ρ₀ ∘ₘ τ₀) ∘ₘ σ₀) ∘ₘ γ°
      ≡ (ρ₀ ∘ₘ (τ₀ ∘ₘ σ₀)) ∘ₘ γ°
    Q =
      Q-left ∙ Q-right

    Q≡P :
      Q ≡ P
    Q≡P =
      sub-setₘ εₘ (GluCtx.Γ° Ξ)
        (((ρ₀ ∘ₘ τ₀) ∘ₘ σ₀) ∘ₘ γ°)
        ((ρ₀ ∘ₘ (τ₀ ∘ₘ σ₀)) ∘ₘ γ°)
        Q
        P

    left-step₁ :
      PathP
        (λ i →
          GluCtx.Γ∙ Ξ (∘-assocₘ (ρ₀ ∘ₘ τ₀) σ₀ γ° i))
        actual-left
        left-mid
    left-step₁ i =
      subst-filler
        (GluCtx.Γ∙ Ξ)
        (sym (∘-assocₘ (ρ₀ ∘ₘ τ₀) σ₀ γ°))
        left-mid
        (~ i)

    left-step₂ :
      PathP
        (λ i → GluCtx.Γ∙ Ξ (∘-assocₘ ρ₀ τ₀ σγ i))
        left-mid
        base
    left-step₂ i =
      subst-filler
        (GluCtx.Γ∙ Ξ)
        (sym (∘-assocₘ ρ₀ τ₀ σγ))
        base
        (~ i)

    left-path :
      PathP
        (λ i → GluCtx.Γ∙ Ξ (Q-left i))
        actual-left
        base
    left-path =
      compPathP' {B = GluCtx.Γ∙ Ξ} left-step₁ left-step₂

    τ∙-path :
      PathP
        (λ i → GluCtx.Γ∙ Θ (τ-path i))
        τσγ∙
        τ∘σγ∙
    τ∙-path =
      subst-filler (GluCtx.Γ∙ Θ) τ-path τσγ∙

    right-step₁ :
      PathP
        (λ i → GluCtx.Γ∙ Ξ (ρ₀ ∘ₘ τ-path i))
        base
        right-mid
    right-step₁ i =
      GluSub.σ∙ ρ (τ-path i) (τ∙-path i)

    right-step₂ :
      PathP
        (λ i →
          GluCtx.Γ∙ Ξ
            (sym (∘-assocₘ ρ₀ (τ₀ ∘ₘ σ₀) γ°) i))
        right-mid
        actual-right
    right-step₂ =
      subst-filler
        (GluCtx.Γ∙ Ξ)
        (sym (∘-assocₘ ρ₀ (τ₀ ∘ₘ σ₀) γ°))
        right-mid

    right-path :
      PathP
        (λ i → GluCtx.Γ∙ Ξ (Q-right i))
        base
        actual-right
    right-path =
      compPathP' {B = GluCtx.Γ∙ Ξ} right-step₁ right-step₂

    path-Q :
      PathP
        (λ i → GluCtx.Γ∙ Ξ (Q i))
        actual-left
        actual-right
    path-Q =
      compPathP' {B = GluCtx.Γ∙ Ξ} left-path right-path

    path :
      PathP
        (λ i → GluCtx.Γ∙ Ξ (P i))
        actual-left
        actual-right
    path =
      subst
        (λ q →
          PathP
            (λ i → GluCtx.Γ∙ Ξ (q i))
            actual-left
            actual-right)
        Q≡P
        path-Q

  _[_]Tmᵍ :
    {Γ Δ : GluCtx 𝓜} {A : GluTy 𝓜}
    → GluTm 𝓜 Δ A
    → GluSub 𝓜 Γ Δ
    → GluTm 𝓜 Γ A
  GluTm.M° (M [ σ ]Tmᵍ) =
    GluTm.M° M [ GluSub.σ° σ ]Tmₘ
  GluTm.M∙ (_[_]Tmᵍ {A = A} M σ) γ° γ∙ =
    subst (GluTy.A∙ A)
      (sym (Tm-∘ₘ (GluTm.M° M) (GluSub.σ° σ) γ°))
      (GluTm.M∙ M
        (GluSub.σ° σ ∘ₘ γ°)
        (GluSub.σ∙ σ γ° γ∙))

  Tm-idᵍ :
    {Γ : GluCtx 𝓜} {A : GluTy 𝓜}
    (M : GluTm 𝓜 Γ A)
    → M [ idᵍ Γ ]Tmᵍ ≡ M
  GluTm.M° (Tm-idᵍ M i) =
    Tm-idₘ (GluTm.M° M) i
  GluTm.M∙ (Tm-idᵍ {Γ = Γ} {A = A} M i) γ° γ∙ =
    path i
    where
    v = GluTm.M∙ M γ° γ∙

    idγ : Subₘ εₘ (GluCtx.Γ° Γ)
    idγ = idₘ ∘ₘ γ°

    idγ-path :
      idγ ≡ γ°
    idγ-path =
      id-leftₘ γ°

    idγ∙ :
      GluCtx.Γ∙ Γ idγ
    idγ∙ =
      subst (GluCtx.Γ∙ Γ) (sym idγ-path) γ∙

    w :
      GluTy.A∙ A (GluTm.M° M [ idγ ]Tmₘ)
    w =
      GluTm.M∙ M idγ idγ∙

    actual :
      GluTy.A∙ A ((GluTm.M° M [ idₘ ]Tmₘ) [ γ° ]Tmₘ)
    actual =
      subst (GluTy.A∙ A)
        (sym (Tm-∘ₘ (GluTm.M° M) idₘ γ°))
        w

    P :
      (GluTm.M° M [ idₘ ]Tmₘ) [ γ° ]Tmₘ
      ≡ GluTm.M° M [ γ° ]Tmₘ
    P i = Tm-idₘ (GluTm.M° M) i [ γ° ]Tmₘ

    Q :
      (GluTm.M° M [ idₘ ]Tmₘ) [ γ° ]Tmₘ
      ≡ GluTm.M° M [ γ° ]Tmₘ
    Q =
      Tm-∘ₘ (GluTm.M° M) idₘ γ°
      ∙ cong (λ δ → GluTm.M° M [ δ ]Tmₘ) idγ-path

    Q≡P :
      Q ≡ P
    Q≡P =
      tm-setₘ εₘ (GluTy.A° A)
        ((GluTm.M° M [ idₘ ]Tmₘ) [ γ° ]Tmₘ)
        (GluTm.M° M [ γ° ]Tmₘ)
        Q
        P

    step₁ :
      PathP
        (λ i → GluTy.A∙ A (Tm-∘ₘ (GluTm.M° M) idₘ γ° i))
        actual
        w
    step₁ i =
      subst-filler
        (GluTy.A∙ A)
        (sym (Tm-∘ₘ (GluTm.M° M) idₘ γ°))
        w
        (~ i)

    γ∙-path :
      PathP
        (λ i → GluCtx.Γ∙ Γ (idγ-path i))
        idγ∙
        γ∙
    γ∙-path i =
      subst-filler (GluCtx.Γ∙ Γ) (sym idγ-path) γ∙ (~ i)

    step₂ :
      PathP
        (λ i → GluTy.A∙ A (GluTm.M° M [ idγ-path i ]Tmₘ))
        w
        v
    step₂ i =
      GluTm.M∙ M (idγ-path i) (γ∙-path i)

    path-Q :
      PathP
        (λ i → GluTy.A∙ A (Q i))
        actual
        v
    path-Q =
      compPathP' {B = GluTy.A∙ A} step₁ step₂

    path :
      PathP
        (λ i → GluTy.A∙ A (P i))
        actual
        v
    path =
      subst
        (λ q →
          PathP
            (λ i → GluTy.A∙ A (q i))
            actual
            v)
        Q≡P
        path-Q

  Tm-∘ᵍ :
    {Γ Δ Θ : GluCtx 𝓜} {A : GluTy 𝓜}
    (M : GluTm 𝓜 Θ A)
    (τ : GluSub 𝓜 Δ Θ)
    (σ : GluSub 𝓜 Γ Δ)
    → (M [ τ ]Tmᵍ) [ σ ]Tmᵍ ≡ M [ τ ∘ᵍ σ ]Tmᵍ
  GluTm.M° (Tm-∘ᵍ M τ σ i) =
    Tm-∘ₘ (GluTm.M° M) (GluSub.σ° τ) (GluSub.σ° σ) i
  GluTm.M∙
    (Tm-∘ᵍ {Γ = Γ} {Δ = Δ} {Θ = Θ} {A = A} M τ σ i)
    γ° γ∙ =
    path i
    where
    M₀ = GluTm.M° M
    τ₀ = GluSub.σ° τ
    σ₀ = GluSub.σ° σ

    σγ : Subₘ εₘ (GluCtx.Γ° Δ)
    σγ = σ₀ ∘ₘ γ°

    τσγ : Subₘ εₘ (GluCtx.Γ° Θ)
    τσγ = τ₀ ∘ₘ σγ

    τ∘σγ : Subₘ εₘ (GluCtx.Γ° Θ)
    τ∘σγ = (τ₀ ∘ₘ σ₀) ∘ₘ γ°

    σγ∙ :
      GluCtx.Γ∙ Δ σγ
    σγ∙ =
      GluSub.σ∙ σ γ° γ∙

    τσγ∙ :
      GluCtx.Γ∙ Θ τσγ
    τσγ∙ =
      GluSub.σ∙ τ σγ σγ∙

    base :
      GluTy.A∙ A (M₀ [ τσγ ]Tmₘ)
    base =
      GluTm.M∙ M τσγ τσγ∙

    left-mid :
      GluTy.A∙ A ((M₀ [ τ₀ ]Tmₘ) [ σγ ]Tmₘ)
    left-mid =
      subst (GluTy.A∙ A)
        (sym (Tm-∘ₘ M₀ τ₀ σγ))
        base

    actual-left :
      GluTy.A∙ A (((M₀ [ τ₀ ]Tmₘ) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    actual-left =
      subst (GluTy.A∙ A)
        (sym (Tm-∘ₘ (M₀ [ τ₀ ]Tmₘ) σ₀ γ°))
        left-mid

    τ-path :
      τσγ ≡ τ∘σγ
    τ-path =
      sym (∘-assocₘ τ₀ σ₀ γ°)

    τ∘σγ∙ :
      GluCtx.Γ∙ Θ τ∘σγ
    τ∘σγ∙ =
      subst (GluCtx.Γ∙ Θ) τ-path τσγ∙

    right-mid :
      GluTy.A∙ A (M₀ [ τ∘σγ ]Tmₘ)
    right-mid =
      GluTm.M∙ M τ∘σγ τ∘σγ∙

    actual-right :
      GluTy.A∙ A ((M₀ [ τ₀ ∘ₘ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    actual-right =
      subst (GluTy.A∙ A)
        (sym (Tm-∘ₘ M₀ (τ₀ ∘ₘ σ₀) γ°))
        right-mid

    P :
      ((M₀ [ τ₀ ]Tmₘ) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ (M₀ [ τ₀ ∘ₘ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    P i = Tm-∘ₘ M₀ τ₀ σ₀ i [ γ° ]Tmₘ

    Q-left :
      ((M₀ [ τ₀ ]Tmₘ) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ M₀ [ τσγ ]Tmₘ
    Q-left =
      Tm-∘ₘ (M₀ [ τ₀ ]Tmₘ) σ₀ γ°
      ∙ Tm-∘ₘ M₀ τ₀ σγ

    Q-right :
      M₀ [ τσγ ]Tmₘ
      ≡ (M₀ [ τ₀ ∘ₘ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    Q-right =
      cong (λ δ → M₀ [ δ ]Tmₘ) τ-path
      ∙ sym (Tm-∘ₘ M₀ (τ₀ ∘ₘ σ₀) γ°)

    Q :
      ((M₀ [ τ₀ ]Tmₘ) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ (M₀ [ τ₀ ∘ₘ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    Q =
      Q-left ∙ Q-right

    Q≡P :
      Q ≡ P
    Q≡P =
      tm-setₘ εₘ (GluTy.A° A)
        (((M₀ [ τ₀ ]Tmₘ) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        ((M₀ [ τ₀ ∘ₘ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        Q
        P

    left-step₁ :
      PathP
        (λ i →
          GluTy.A∙ A
            (Tm-∘ₘ (M₀ [ τ₀ ]Tmₘ) σ₀ γ° i))
        actual-left
        left-mid
    left-step₁ i =
      subst-filler
        (GluTy.A∙ A)
        (sym (Tm-∘ₘ (M₀ [ τ₀ ]Tmₘ) σ₀ γ°))
        left-mid
        (~ i)

    left-step₂ :
      PathP
        (λ i → GluTy.A∙ A (Tm-∘ₘ M₀ τ₀ σγ i))
        left-mid
        base
    left-step₂ i =
      subst-filler
        (GluTy.A∙ A)
        (sym (Tm-∘ₘ M₀ τ₀ σγ))
        base
        (~ i)

    left-path :
      PathP
        (λ i → GluTy.A∙ A (Q-left i))
        actual-left
        base
    left-path =
      compPathP' {B = GluTy.A∙ A} left-step₁ left-step₂

    τ∙-path :
      PathP
        (λ i → GluCtx.Γ∙ Θ (τ-path i))
        τσγ∙
        τ∘σγ∙
    τ∙-path =
      subst-filler (GluCtx.Γ∙ Θ) τ-path τσγ∙

    right-step₁ :
      PathP
        (λ i → GluTy.A∙ A (M₀ [ τ-path i ]Tmₘ))
        base
        right-mid
    right-step₁ i =
      GluTm.M∙ M (τ-path i) (τ∙-path i)

    right-step₂ :
      PathP
        (λ i →
          GluTy.A∙ A
            (sym (Tm-∘ₘ M₀ (τ₀ ∘ₘ σ₀) γ°) i))
        right-mid
        actual-right
    right-step₂ =
      subst-filler
        (GluTy.A∙ A)
        (sym (Tm-∘ₘ M₀ (τ₀ ∘ₘ σ₀) γ°))
        right-mid

    right-path :
      PathP
        (λ i → GluTy.A∙ A (Q-right i))
        base
        actual-right
    right-path =
      compPathP' {B = GluTy.A∙ A} right-step₁ right-step₂

    path-Q :
      PathP
        (λ i → GluTy.A∙ A (Q i))
        actual-left
        actual-right
    path-Q =
      compPathP' {B = GluTy.A∙ A} left-path right-path

    path :
      PathP
        (λ i → GluTy.A∙ A (P i))
        actual-left
        actual-right
    path =
      subst
        (λ q →
          PathP
            (λ i → GluTy.A∙ A (q i))
            actual-left
            actual-right)
        Q≡P
        path-Q

  _▷ᵍ_ : GluCtx 𝓜 → GluTy 𝓜 → GluCtx 𝓜
  GluCtx.Γ° (Γ ▷ᵍ A) =
    GluCtx.Γ° Γ ▷ₘ GluTy.A° A
  GluCtx.Γ∙ (Γ ▷ᵍ A) δ° =
    Σ (GluCtx.Γ∙ Γ (pₘ ∘ₘ δ°))
      (λ _ → GluTy.A∙ A (qₘ [ δ° ]Tmₘ))

  pᵍ : {Γ : GluCtx 𝓜} {A : GluTy 𝓜} → GluSub 𝓜 (Γ ▷ᵍ A) Γ
  GluSub.σ° pᵍ = pₘ
  GluSub.σ∙ pᵍ δ° δ∙ = fst δ∙

  qᵍ : {Γ : GluCtx 𝓜} {A : GluTy 𝓜} → GluTm 𝓜 (Γ ▷ᵍ A) A
  GluTm.M° qᵍ = qₘ
  GluTm.M∙ qᵍ δ° δ∙ = snd δ∙

  ⟨_,_⟩ᵍ :
    {Γ Δ : GluCtx 𝓜} {A : GluTy 𝓜}
    → (σ : GluSub 𝓜 Γ Δ)
    → GluTm 𝓜 Γ A
    → GluSub 𝓜 Γ (Δ ▷ᵍ A)
  GluSub.σ° (⟨ σ , M ⟩ᵍ) =
    ⟨ GluSub.σ° σ , GluTm.M° M ⟩ₘ
  GluSub.σ∙ (⟨_,_⟩ᵍ {Δ = Δ} {A = A} σ M) γ° γ∙ =
    transport
      (λ i → GluCtx.Γ∙ (Δ ▷ᵍ A) (pairγ≡direct (~ i)))
      direct∙
    where
    pairγ =
      ⟨ GluSub.σ° σ , GluTm.M° M ⟩ₘ ∘ₘ γ°

    directγ =
      ⟨ GluSub.σ° σ ∘ₘ γ° , GluTm.M° M [ γ° ]Tmₘ ⟩ₘ

    pairγ≡direct :
      pairγ ≡ directγ
    pairγ≡direct =
      ⟨⟩-∘ₘ (GluSub.σ° σ) (GluTm.M° M) γ°

    p-direct :
      pₘ ∘ₘ directγ ≡ GluSub.σ° σ ∘ₘ γ°
    p-direct =
      p-⟨⟩ₘ (GluSub.σ° σ ∘ₘ γ°) (GluTm.M° M [ γ° ]Tmₘ)

    q-path :
      qₘ [ directγ ]Tmₘ ≡ GluTm.M° M [ γ° ]Tmₘ
    q-path =
      q-⟨⟩ₘ (GluSub.σ° σ ∘ₘ γ°) (GluTm.M° M [ γ° ]Tmₘ)

    direct∙ :
      GluCtx.Γ∙ (Δ ▷ᵍ A) directγ
    direct∙ =
      subst (GluCtx.Γ∙ Δ) (sym p-direct) (GluSub.σ∙ σ γ° γ∙)
      ,
      subst (GluTy.A∙ A) (sym q-path) (GluTm.M∙ M γ° γ∙)

  liftᵍ :
    {Γ Δ : GluCtx 𝓜} {A : GluTy 𝓜}
    → GluSub 𝓜 Γ Δ
    → GluSub 𝓜 (Γ ▷ᵍ A) (Δ ▷ᵍ A)
  liftᵍ {Γ = Γ} {A = A} σ =
    ⟨ σ ∘ᵍ pᵍ {Γ = Γ} {A = A}
    , qᵍ {Γ = Γ} {A = A}
    ⟩ᵍ

  p-⟨⟩ᵍ :
    {Γ Δ : GluCtx 𝓜} {A : GluTy 𝓜}
    (σ : GluSub 𝓜 Γ Δ)
    (M : GluTm 𝓜 Γ A)
    → pᵍ {A = A} ∘ᵍ ⟨ σ , M ⟩ᵍ ≡ σ
  GluSub.σ° (p-⟨⟩ᵍ σ M i) =
    p-⟨⟩ₘ (GluSub.σ° σ) (GluTm.M° M) i
  GluSub.σ∙ (p-⟨⟩ᵍ {Γ = Γ} {Δ = Δ} {A = A} σ M i) γ° γ∙ =
    path i
    where
    σ₀ = GluSub.σ° σ
    M₀ = GluTm.M° M

    pairγ =
      ⟨ σ₀ , M₀ ⟩ₘ ∘ₘ γ°

    directγ =
      ⟨ σ₀ ∘ₘ γ° , M₀ [ γ° ]Tmₘ ⟩ₘ

    pairγ≡direct :
      pairγ ≡ directγ
    pairγ≡direct =
      ⟨⟩-∘ₘ σ₀ M₀ γ°

    p-direct :
      pₘ ∘ₘ directγ ≡ σ₀ ∘ₘ γ°
    p-direct =
      p-⟨⟩ₘ (σ₀ ∘ₘ γ°) (M₀ [ γ° ]Tmₘ)

    q-path :
      qₘ [ directγ ]Tmₘ ≡ M₀ [ γ° ]Tmₘ
    q-path =
      q-⟨⟩ₘ (σ₀ ∘ₘ γ°) (M₀ [ γ° ]Tmₘ)

    direct∙ :
      GluCtx.Γ∙ (Δ ▷ᵍ A) directγ
    direct∙ =
      subst (GluCtx.Γ∙ Δ) (sym p-direct) (GluSub.σ∙ σ γ° γ∙)
      ,
      subst (GluTy.A∙ A) (sym q-path) (GluTm.M∙ M γ° γ∙)

    pair∙ :
      GluCtx.Γ∙ (Δ ▷ᵍ A) pairγ
    pair∙ =
      transport
        (λ i → GluCtx.Γ∙ (Δ ▷ᵍ A) (pairγ≡direct (~ i)))
        direct∙

    actual :
      GluCtx.Γ∙ Δ ((pₘ ∘ₘ ⟨ σ₀ , M₀ ⟩ₘ) ∘ₘ γ°)
    actual =
      subst (GluCtx.Γ∙ Δ)
        (sym (∘-assocₘ pₘ ⟨ σ₀ , M₀ ⟩ₘ γ°))
        (fst pair∙)

    target :
      GluCtx.Γ∙ Δ (σ₀ ∘ₘ γ°)
    target =
      GluSub.σ∙ σ γ° γ∙

    P :
      (pₘ ∘ₘ ⟨ σ₀ , M₀ ⟩ₘ) ∘ₘ γ°
      ≡ σ₀ ∘ₘ γ°
    P i =
      p-⟨⟩ₘ σ₀ M₀ i ∘ₘ γ°

    Q₁ :
      (pₘ ∘ₘ ⟨ σ₀ , M₀ ⟩ₘ) ∘ₘ γ°
      ≡ pₘ ∘ₘ pairγ
    Q₁ =
      ∘-assocₘ pₘ ⟨ σ₀ , M₀ ⟩ₘ γ°

    Q₂ :
      pₘ ∘ₘ pairγ ≡ pₘ ∘ₘ directγ
    Q₂ =
      cong (λ δ → pₘ ∘ₘ δ) pairγ≡direct

    Q :
      (pₘ ∘ₘ ⟨ σ₀ , M₀ ⟩ₘ) ∘ₘ γ°
      ≡ σ₀ ∘ₘ γ°
    Q =
      (Q₁ ∙ Q₂) ∙ p-direct

    Q≡P :
      Q ≡ P
    Q≡P =
      sub-setₘ εₘ (GluCtx.Γ° Δ)
        ((pₘ ∘ₘ ⟨ σ₀ , M₀ ⟩ₘ) ∘ₘ γ°)
        (σ₀ ∘ₘ γ°)
        Q
        P

    step₁ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (Q₁ i))
        actual
        (fst pair∙)
    step₁ i =
      subst-filler
        (GluCtx.Γ∙ Δ)
        (sym (∘-assocₘ pₘ ⟨ σ₀ , M₀ ⟩ₘ γ°))
        (fst pair∙)
        (~ i)

    pair∙-filler :
      PathP
        (λ i → GluCtx.Γ∙ (Δ ▷ᵍ A) (pairγ≡direct (~ i)))
        direct∙
        pair∙
    pair∙-filler =
      transport-filler
        (λ i → GluCtx.Γ∙ (Δ ▷ᵍ A) (pairγ≡direct (~ i)))
        direct∙

    step₂ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (Q₂ i))
        (fst pair∙)
        (fst direct∙)
    step₂ i =
      fst (pair∙-filler (~ i))

    step₃ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (p-direct i))
        (fst direct∙)
        target
    step₃ i =
      subst-filler
        (GluCtx.Γ∙ Δ)
        (sym p-direct)
        target
        (~ i)

    path-Q₁₂ :
      PathP
        (λ i → GluCtx.Γ∙ Δ ((Q₁ ∙ Q₂) i))
        actual
        (fst direct∙)
    path-Q₁₂ =
      compPathP' {B = GluCtx.Γ∙ Δ} step₁ step₂

    path-Q :
      PathP
        (λ i → GluCtx.Γ∙ Δ (Q i))
        actual
        target
    path-Q =
      compPathP' {B = GluCtx.Γ∙ Δ} path-Q₁₂ step₃

    path :
      PathP
        (λ i → GluCtx.Γ∙ Δ (P i))
        actual
        target
    path =
      subst
        (λ q →
          PathP
            (λ i → GluCtx.Γ∙ Δ (q i))
            actual
            target)
        Q≡P
        path-Q

  q-⟨⟩ᵍ :
    {Γ Δ : GluCtx 𝓜} {A : GluTy 𝓜}
    (σ : GluSub 𝓜 Γ Δ)
    (M : GluTm 𝓜 Γ A)
    → _[_]Tmᵍ
        {Γ = Γ}
        {Δ = Δ ▷ᵍ A}
        {A = A}
        (qᵍ {Γ = Δ} {A = A})
        (⟨_,_⟩ᵍ {Γ = Γ} {Δ = Δ} {A = A} σ M)
      ≡ M
  GluTm.M° (q-⟨⟩ᵍ σ M i) =
    q-⟨⟩ₘ (GluSub.σ° σ) (GluTm.M° M) i
  GluTm.M∙ (q-⟨⟩ᵍ {Γ = Γ} {Δ = Δ} {A = A} σ M i) γ° γ∙ =
    path i
    where
    σ₀ = GluSub.σ° σ
    M₀ = GluTm.M° M

    pairSub =
      ⟨ σ₀ , M₀ ⟩ₘ

    pairγ =
      pairSub ∘ₘ γ°

    directγ =
      ⟨ σ₀ ∘ₘ γ° , M₀ [ γ° ]Tmₘ ⟩ₘ

    pairγ≡direct :
      pairγ ≡ directγ
    pairγ≡direct =
      ⟨⟩-∘ₘ σ₀ M₀ γ°

    p-direct :
      pₘ ∘ₘ directγ ≡ σ₀ ∘ₘ γ°
    p-direct =
      p-⟨⟩ₘ (σ₀ ∘ₘ γ°) (M₀ [ γ° ]Tmₘ)

    q-path :
      qₘ [ directγ ]Tmₘ ≡ M₀ [ γ° ]Tmₘ
    q-path =
      q-⟨⟩ₘ (σ₀ ∘ₘ γ°) (M₀ [ γ° ]Tmₘ)

    direct∙ :
      GluCtx.Γ∙ (Δ ▷ᵍ A) directγ
    direct∙ =
      subst (GluCtx.Γ∙ Δ) (sym p-direct) (GluSub.σ∙ σ γ° γ∙)
      ,
      subst (GluTy.A∙ A) (sym q-path) (GluTm.M∙ M γ° γ∙)

    pair∙ :
      GluCtx.Γ∙ (Δ ▷ᵍ A) pairγ
    pair∙ =
      transport
        (λ i → GluCtx.Γ∙ (Δ ▷ᵍ A) (pairγ≡direct (~ i)))
        direct∙

    actual :
      GluTy.A∙ A ((qₘ [ pairSub ]Tmₘ) [ γ° ]Tmₘ)
    actual =
      subst (GluTy.A∙ A)
        (sym (Tm-∘ₘ qₘ pairSub γ°))
        (snd pair∙)

    target :
      GluTy.A∙ A (M₀ [ γ° ]Tmₘ)
    target =
      GluTm.M∙ M γ° γ∙

    P :
      (qₘ [ pairSub ]Tmₘ) [ γ° ]Tmₘ
      ≡ M₀ [ γ° ]Tmₘ
    P i =
      q-⟨⟩ₘ σ₀ M₀ i [ γ° ]Tmₘ

    Q₁ :
      (qₘ [ pairSub ]Tmₘ) [ γ° ]Tmₘ
      ≡ qₘ [ pairγ ]Tmₘ
    Q₁ =
      Tm-∘ₘ qₘ pairSub γ°

    Q₂ :
      qₘ [ pairγ ]Tmₘ ≡ qₘ [ directγ ]Tmₘ
    Q₂ =
      cong (λ δ → qₘ [ δ ]Tmₘ) pairγ≡direct

    Q :
      (qₘ [ pairSub ]Tmₘ) [ γ° ]Tmₘ
      ≡ M₀ [ γ° ]Tmₘ
    Q =
      (Q₁ ∙ Q₂) ∙ q-path

    Q≡P :
      Q ≡ P
    Q≡P =
      tm-setₘ εₘ (GluTy.A° A)
        ((qₘ [ pairSub ]Tmₘ) [ γ° ]Tmₘ)
        (M₀ [ γ° ]Tmₘ)
        Q
        P

    step₁ :
      PathP
        (λ i → GluTy.A∙ A (Q₁ i))
        actual
        (snd pair∙)
    step₁ i =
      subst-filler
        (GluTy.A∙ A)
        (sym (Tm-∘ₘ qₘ pairSub γ°))
        (snd pair∙)
        (~ i)

    pair∙-filler :
      PathP
        (λ i → GluCtx.Γ∙ (Δ ▷ᵍ A) (pairγ≡direct (~ i)))
        direct∙
        pair∙
    pair∙-filler =
      transport-filler
        (λ i → GluCtx.Γ∙ (Δ ▷ᵍ A) (pairγ≡direct (~ i)))
        direct∙

    step₂ :
      PathP
        (λ i → GluTy.A∙ A (Q₂ i))
        (snd pair∙)
        (snd direct∙)
    step₂ i =
      snd (pair∙-filler (~ i))

    step₃ :
      PathP
        (λ i → GluTy.A∙ A (q-path i))
        (snd direct∙)
        target
    step₃ i =
      subst-filler
        (GluTy.A∙ A)
        (sym q-path)
        target
        (~ i)

    path-Q₁₂ :
      PathP
        (λ i → GluTy.A∙ A ((Q₁ ∙ Q₂) i))
        actual
        (snd direct∙)
    path-Q₁₂ =
      compPathP' {B = GluTy.A∙ A} step₁ step₂

    path-Q :
      PathP
        (λ i → GluTy.A∙ A (Q i))
        actual
        target
    path-Q =
      compPathP' {B = GluTy.A∙ A} path-Q₁₂ step₃

    path :
      PathP
        (λ i → GluTy.A∙ A (P i))
        actual
        target
    path =
      subst
        (λ q →
          PathP
            (λ i → GluTy.A∙ A (q i))
            actual
            target)
        Q≡P
        path-Q

  ▷ηᵍ :
    {Γ : GluCtx 𝓜} {A : GluTy 𝓜}
    → ⟨_,_⟩ᵍ
        {Γ = Γ ▷ᵍ A}
        {Δ = Γ}
        {A = A}
        (pᵍ {Γ = Γ} {A = A})
        (qᵍ {Γ = Γ} {A = A})
      ≡ idᵍ (Γ ▷ᵍ A)
  GluSub.σ° (▷ηᵍ {Γ = Γ} {A = A} i) =
    ▷ηₘ {Γ = GluCtx.Γ° Γ} {A = GluTy.A° A} i
  GluSub.σ∙ (▷ηᵍ {Γ = Γ} {A = A} i) γ° γ∙ =
    path i
    where
    pairSub =
      ⟨ pₘ , qₘ ⟩ₘ

    pairγ =
      pairSub ∘ₘ γ°

    directγ =
      ⟨ pₘ ∘ₘ γ° , qₘ [ γ° ]Tmₘ ⟩ₘ

    idγ =
      idₘ ∘ₘ γ°

    fiber :
      Subₘ εₘ (GluCtx.Γ° Γ ▷ₘ GluTy.A° A)
      → Type ℓM
    fiber =
      GluCtx.Γ∙ (Γ ▷ᵍ A)

    pairγ≡direct :
      pairγ ≡ directγ
    pairγ≡direct =
      ⟨⟩-∘ₘ pₘ qₘ γ°

    p-direct :
      pₘ ∘ₘ directγ ≡ pₘ ∘ₘ γ°
    p-direct =
      p-⟨⟩ₘ (pₘ ∘ₘ γ°) (qₘ [ γ° ]Tmₘ)

    q-path :
      qₘ [ directγ ]Tmₘ ≡ qₘ [ γ° ]Tmₘ
    q-path =
      q-⟨⟩ₘ (pₘ ∘ₘ γ°) (qₘ [ γ° ]Tmₘ)

    direct∙ :
      fiber directγ
    direct∙ =
      subst (GluCtx.Γ∙ Γ) (sym p-direct) (fst γ∙)
      ,
      subst (GluTy.A∙ A) (sym q-path) (snd γ∙)

    pair∙ :
      fiber pairγ
    pair∙ =
      transport
        (λ i → fiber (pairγ≡direct (~ i)))
        direct∙

    idγ-path :
      idγ ≡ γ°
    idγ-path =
      id-leftₘ γ°

    directγ≡γ :
      directγ ≡ γ°
    directγ≡γ =
      sym pairγ≡direct
      ∙ cong (λ δ → δ ∘ₘ γ°)
          (▷ηₘ {Γ = GluCtx.Γ° Γ} {A = GluTy.A° A})
      ∙ idγ-path

    p-directγ≡γ :
      cong (λ δ → pₘ ∘ₘ δ) directγ≡γ ≡ p-direct
    p-directγ≡γ =
      sub-setₘ εₘ (GluCtx.Γ° Γ)
        (pₘ ∘ₘ directγ)
        (pₘ ∘ₘ γ°)
        (cong (λ δ → pₘ ∘ₘ δ) directγ≡γ)
        p-direct

    q-directγ≡γ :
      cong (λ δ → qₘ [ δ ]Tmₘ) directγ≡γ ≡ q-path
    q-directγ≡γ =
      tm-setₘ εₘ (GluTy.A° A)
        (qₘ [ directγ ]Tmₘ)
        (qₘ [ γ° ]Tmₘ)
        (cong (λ δ → qₘ [ δ ]Tmₘ) directγ≡γ)
        q-path

    p-direct-path :
      PathP
        (λ i → GluCtx.Γ∙ Γ (pₘ ∘ₘ directγ≡γ i))
        (fst direct∙)
        (fst γ∙)
    p-direct-path =
      subst
        (λ p →
          PathP
            (λ i → GluCtx.Γ∙ Γ (p i))
            (fst direct∙)
            (fst γ∙))
        (sym p-directγ≡γ)
        (λ i →
          subst-filler
            (GluCtx.Γ∙ Γ)
            (sym p-direct)
            (fst γ∙)
            (~ i))

    q-direct-path :
      PathP
        (λ i → GluTy.A∙ A (qₘ [ directγ≡γ i ]Tmₘ))
        (snd direct∙)
        (snd γ∙)
    q-direct-path =
      subst
        (λ p →
          PathP
            (λ i → GluTy.A∙ A (p i))
            (snd direct∙)
            (snd γ∙))
        (sym q-directγ≡γ)
        (λ i →
          subst-filler
            (GluTy.A∙ A)
            (sym q-path)
            (snd γ∙)
            (~ i))

    direct∙≡γ∙ :
      PathP
        (λ i → fiber (directγ≡γ i))
        direct∙
        γ∙
    direct∙≡γ∙ i =
      p-direct-path i , q-direct-path i

    γ≡idγ :
      γ° ≡ idγ
    γ≡idγ =
      sym idγ-path

    target :
      fiber idγ
    target =
      subst fiber γ≡idγ γ∙

    pair∙-filler :
      PathP
        (λ i → fiber (pairγ≡direct (~ i)))
        direct∙
        pair∙
    pair∙-filler =
      transport-filler
        (λ i → fiber (pairγ≡direct (~ i)))
        direct∙

    step₁ :
      PathP
        (λ i → fiber (pairγ≡direct i))
        pair∙
        direct∙
    step₁ i =
      pair∙-filler (~ i)

    step₂ :
      PathP
        (λ i → fiber (directγ≡γ i))
        direct∙
        γ∙
    step₂ =
      direct∙≡γ∙

    step₃ :
      PathP
        (λ i → fiber (γ≡idγ i))
        γ∙
        target
    step₃ =
      subst-filler fiber γ≡idγ γ∙

    Q :
      pairγ ≡ idγ
    Q =
      (pairγ≡direct ∙ directγ≡γ) ∙ γ≡idγ

    P :
      pairγ ≡ idγ
    P i =
      ▷ηₘ {Γ = GluCtx.Γ° Γ} {A = GluTy.A° A} i ∘ₘ γ°

    Q≡P :
      Q ≡ P
    Q≡P =
      sub-setₘ εₘ (GluCtx.Γ° Γ ▷ₘ GluTy.A° A)
        pairγ
        idγ
        Q
        P

    path-Q₁₂ :
      PathP
        (λ i → fiber ((pairγ≡direct ∙ directγ≡γ) i))
        pair∙
        γ∙
    path-Q₁₂ =
      compPathP' {B = fiber} step₁ step₂

    path-Q :
      PathP
        (λ i → fiber (Q i))
        pair∙
        target
    path-Q =
      compPathP' {B = fiber} path-Q₁₂ step₃

    path :
      PathP
        (λ i → fiber (P i))
        pair∙
        target
    path =
      subst
        (λ q →
          PathP
            (λ i → fiber (q i))
            pair∙
            target)
        Q≡P
        path-Q

  ⟨⟩-∘ᵍ :
    {Γ Δ Θ : GluCtx 𝓜} {A : GluTy 𝓜}
    (σ : GluSub 𝓜 Γ Δ)
    (M : GluTm 𝓜 Γ A)
    (ρ : GluSub 𝓜 Θ Γ)
    → ⟨ σ , M ⟩ᵍ ∘ᵍ ρ
      ≡ ⟨ σ ∘ᵍ ρ , M [ ρ ]Tmᵍ ⟩ᵍ
  GluSub.σ° (⟨⟩-∘ᵍ σ M ρ i) =
    ⟨⟩-∘ₘ (GluSub.σ° σ) (GluTm.M° M) (GluSub.σ° ρ) i
  GluSub.σ∙ (⟨⟩-∘ᵍ {Γ = Γ} {Δ = Δ} {Θ = Θ} {A = A} σ M ρ i) γ° γ∙ =
    path i
    where
    σ₀ = GluSub.σ° σ
    M₀ = GluTm.M° M
    ρ₀ = GluSub.σ° ρ

    ργ =
      ρ₀ ∘ₘ γ°

    ργ∙ :
      GluCtx.Γ∙ Γ ργ
    ργ∙ =
      GluSub.σ∙ ρ γ° γ∙

    fiber :
      Subₘ εₘ (GluCtx.Γ° Δ ▷ₘ GluTy.A° A)
      → Type ℓM
    fiber =
      GluCtx.Γ∙ (Δ ▷ᵍ A)

    leftSub =
      ⟨ σ₀ , M₀ ⟩ₘ

    leftStart =
      (leftSub ∘ₘ ρ₀) ∘ₘ γ°

    leftPairγ =
      leftSub ∘ₘ ργ

    leftDirectγ =
      ⟨ σ₀ ∘ₘ ργ , M₀ [ ργ ]Tmₘ ⟩ₘ

    rightSub =
      ⟨ σ₀ ∘ₘ ρ₀ , M₀ [ ρ₀ ]Tmₘ ⟩ₘ

    rightPairγ =
      rightSub ∘ₘ γ°

    rightDirectγ =
      ⟨ (σ₀ ∘ₘ ρ₀) ∘ₘ γ° , (M₀ [ ρ₀ ]Tmₘ) [ γ° ]Tmₘ ⟩ₘ

    assoc-left :
      leftStart ≡ leftPairγ
    assoc-left =
      ∘-assocₘ leftSub ρ₀ γ°

    leftPairγ≡direct :
      leftPairγ ≡ leftDirectγ
    leftPairγ≡direct =
      ⟨⟩-∘ₘ σ₀ M₀ ργ

    rightPairγ≡direct :
      rightPairγ ≡ rightDirectγ
    rightPairγ≡direct =
      ⟨⟩-∘ₘ (σ₀ ∘ₘ ρ₀) (M₀ [ ρ₀ ]Tmₘ) γ°

    sub-assoc :
      (σ₀ ∘ₘ ρ₀) ∘ₘ γ° ≡ σ₀ ∘ₘ ργ
    sub-assoc =
      ∘-assocₘ σ₀ ρ₀ γ°

    tm-assoc :
      (M₀ [ ρ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ M₀ [ ργ ]Tmₘ
    tm-assoc =
      Tm-∘ₘ M₀ ρ₀ γ°

    directγ≡directγ :
      leftDirectγ ≡ rightDirectγ
    directγ≡directγ i =
      ⟨ sym sub-assoc i , sym tm-assoc i ⟩ₘ

    p-left :
      pₘ ∘ₘ leftDirectγ ≡ σ₀ ∘ₘ ργ
    p-left =
      p-⟨⟩ₘ (σ₀ ∘ₘ ργ) (M₀ [ ργ ]Tmₘ)

    q-left :
      qₘ [ leftDirectγ ]Tmₘ ≡ M₀ [ ργ ]Tmₘ
    q-left =
      q-⟨⟩ₘ (σ₀ ∘ₘ ργ) (M₀ [ ργ ]Tmₘ)

    leftDirect∙ :
      fiber leftDirectγ
    leftDirect∙ =
      subst (GluCtx.Γ∙ Δ) (sym p-left) (GluSub.σ∙ σ ργ ργ∙)
      ,
      subst (GluTy.A∙ A) (sym q-left) (GluTm.M∙ M ργ ργ∙)

    leftPair∙ :
      fiber leftPairγ
    leftPair∙ =
      transport
        (λ i → fiber (leftPairγ≡direct (~ i)))
        leftDirect∙

    actual-left :
      fiber leftStart
    actual-left =
      subst fiber (sym assoc-left) leftPair∙

    rightSub∙ :
      GluCtx.Γ∙ Δ ((σ₀ ∘ₘ ρ₀) ∘ₘ γ°)
    rightSub∙ =
      subst (GluCtx.Γ∙ Δ)
        (sym sub-assoc)
        (GluSub.σ∙ σ ργ ργ∙)

    rightM∙ :
      GluTy.A∙ A ((M₀ [ ρ₀ ]Tmₘ) [ γ° ]Tmₘ)
    rightM∙ =
      subst (GluTy.A∙ A)
        (sym tm-assoc)
        (GluTm.M∙ M ργ ργ∙)

    p-right :
      pₘ ∘ₘ rightDirectγ ≡ (σ₀ ∘ₘ ρ₀) ∘ₘ γ°
    p-right =
      p-⟨⟩ₘ
        ((σ₀ ∘ₘ ρ₀) ∘ₘ γ°)
        ((M₀ [ ρ₀ ]Tmₘ) [ γ° ]Tmₘ)

    q-right :
      qₘ [ rightDirectγ ]Tmₘ ≡ (M₀ [ ρ₀ ]Tmₘ) [ γ° ]Tmₘ
    q-right =
      q-⟨⟩ₘ
        ((σ₀ ∘ₘ ρ₀) ∘ₘ γ°)
        ((M₀ [ ρ₀ ]Tmₘ) [ γ° ]Tmₘ)

    rightDirect∙ :
      fiber rightDirectγ
    rightDirect∙ =
      subst (GluCtx.Γ∙ Δ) (sym p-right) rightSub∙
      ,
      subst (GluTy.A∙ A) (sym q-right) rightM∙

    rightPair∙ :
      fiber rightPairγ
    rightPair∙ =
      transport
        (λ i → fiber (rightPairγ≡direct (~ i)))
        rightDirect∙

    p-direct-path :
      cong (λ δ → pₘ ∘ₘ δ) directγ≡directγ
      ≡ (p-left ∙ sym sub-assoc) ∙ sym p-right
    p-direct-path =
      sub-setₘ εₘ (GluCtx.Γ° Δ)
        (pₘ ∘ₘ leftDirectγ)
        (pₘ ∘ₘ rightDirectγ)
        (cong (λ δ → pₘ ∘ₘ δ) directγ≡directγ)
        ((p-left ∙ sym sub-assoc) ∙ sym p-right)

    q-direct-path :
      cong (λ δ → qₘ [ δ ]Tmₘ) directγ≡directγ
      ≡ (q-left ∙ sym tm-assoc) ∙ sym q-right
    q-direct-path =
      tm-setₘ εₘ (GluTy.A° A)
        (qₘ [ leftDirectγ ]Tmₘ)
        (qₘ [ rightDirectγ ]Tmₘ)
        (cong (λ δ → qₘ [ δ ]Tmₘ) directγ≡directγ)
        ((q-left ∙ sym tm-assoc) ∙ sym q-right)

    p-step₁ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (p-left i))
        (fst leftDirect∙)
        (GluSub.σ∙ σ ργ ργ∙)
    p-step₁ i =
      subst-filler
        (GluCtx.Γ∙ Δ)
        (sym p-left)
        (GluSub.σ∙ σ ργ ργ∙)
        (~ i)

    p-step₂ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (sym sub-assoc i))
        (GluSub.σ∙ σ ργ ργ∙)
        rightSub∙
    p-step₂ =
      subst-filler
        (GluCtx.Γ∙ Δ)
        (sym sub-assoc)
        (GluSub.σ∙ σ ργ ργ∙)

    p-step₁₂ :
      PathP
        (λ i → GluCtx.Γ∙ Δ ((p-left ∙ sym sub-assoc) i))
        (fst leftDirect∙)
        rightSub∙
    p-step₁₂ =
      compPathP' {B = GluCtx.Γ∙ Δ} p-step₁ p-step₂

    p-step₃ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (sym p-right i))
        rightSub∙
        (fst rightDirect∙)
    p-step₃ =
      subst-filler
        (GluCtx.Γ∙ Δ)
        (sym p-right)
        rightSub∙

    p-path-Q :
      PathP
        (λ i → GluCtx.Γ∙ Δ (((p-left ∙ sym sub-assoc) ∙ sym p-right) i))
        (fst leftDirect∙)
        (fst rightDirect∙)
    p-path-Q =
      compPathP' {B = GluCtx.Γ∙ Δ} p-step₁₂ p-step₃

    p-path :
      PathP
        (λ i → GluCtx.Γ∙ Δ (pₘ ∘ₘ directγ≡directγ i))
        (fst leftDirect∙)
        (fst rightDirect∙)
    p-path =
      subst
        (λ p →
          PathP
            (λ i → GluCtx.Γ∙ Δ (p i))
            (fst leftDirect∙)
            (fst rightDirect∙))
        (sym p-direct-path)
        p-path-Q

    q-step₁ :
      PathP
        (λ i → GluTy.A∙ A (q-left i))
        (snd leftDirect∙)
        (GluTm.M∙ M ργ ργ∙)
    q-step₁ i =
      subst-filler
        (GluTy.A∙ A)
        (sym q-left)
        (GluTm.M∙ M ργ ργ∙)
        (~ i)

    q-step₂ :
      PathP
        (λ i → GluTy.A∙ A (sym tm-assoc i))
        (GluTm.M∙ M ργ ργ∙)
        rightM∙
    q-step₂ =
      subst-filler
        (GluTy.A∙ A)
        (sym tm-assoc)
        (GluTm.M∙ M ργ ργ∙)

    q-step₁₂ :
      PathP
        (λ i → GluTy.A∙ A ((q-left ∙ sym tm-assoc) i))
        (snd leftDirect∙)
        rightM∙
    q-step₁₂ =
      compPathP' {B = GluTy.A∙ A} q-step₁ q-step₂

    q-step₃ :
      PathP
        (λ i → GluTy.A∙ A (sym q-right i))
        rightM∙
        (snd rightDirect∙)
    q-step₃ =
      subst-filler
        (GluTy.A∙ A)
        (sym q-right)
        rightM∙

    q-path-Q :
      PathP
        (λ i → GluTy.A∙ A (((q-left ∙ sym tm-assoc) ∙ sym q-right) i))
        (snd leftDirect∙)
        (snd rightDirect∙)
    q-path-Q =
      compPathP' {B = GluTy.A∙ A} q-step₁₂ q-step₃

    q-path :
      PathP
        (λ i → GluTy.A∙ A (qₘ [ directγ≡directγ i ]Tmₘ))
        (snd leftDirect∙)
        (snd rightDirect∙)
    q-path =
      subst
        (λ p →
          PathP
            (λ i → GluTy.A∙ A (p i))
            (snd leftDirect∙)
            (snd rightDirect∙))
        (sym q-direct-path)
        q-path-Q

    direct∙-path :
      PathP
        (λ i → fiber (directγ≡directγ i))
        leftDirect∙
        rightDirect∙
    direct∙-path i =
      p-path i , q-path i

    leftPair∙-filler :
      PathP
        (λ i → fiber (leftPairγ≡direct (~ i)))
        leftDirect∙
        leftPair∙
    leftPair∙-filler =
      transport-filler
        (λ i → fiber (leftPairγ≡direct (~ i)))
        leftDirect∙

    rightPair∙-filler :
      PathP
        (λ i → fiber (rightPairγ≡direct (~ i)))
        rightDirect∙
        rightPair∙
    rightPair∙-filler =
      transport-filler
        (λ i → fiber (rightPairγ≡direct (~ i)))
        rightDirect∙

    step₁ :
      PathP
        (λ i → fiber (assoc-left i))
        actual-left
        leftPair∙
    step₁ i =
      subst-filler fiber (sym assoc-left) leftPair∙ (~ i)

    step₂ :
      PathP
        (λ i → fiber (leftPairγ≡direct i))
        leftPair∙
        leftDirect∙
    step₂ i =
      leftPair∙-filler (~ i)

    step₁₂ :
      PathP
        (λ i → fiber ((assoc-left ∙ leftPairγ≡direct) i))
        actual-left
        leftDirect∙
    step₁₂ =
      compPathP' {B = fiber} step₁ step₂

    step₃ :
      PathP
        (λ i → fiber (directγ≡directγ i))
        leftDirect∙
        rightDirect∙
    step₃ =
      direct∙-path

    step₁₂₃ :
      PathP
        (λ i → fiber (((assoc-left ∙ leftPairγ≡direct) ∙ directγ≡directγ) i))
        actual-left
        rightDirect∙
    step₁₂₃ =
      compPathP' {B = fiber} step₁₂ step₃

    step₄ :
      PathP
        (λ i → fiber (sym rightPairγ≡direct i))
        rightDirect∙
        rightPair∙
    step₄ =
      rightPair∙-filler

    Q :
      leftStart ≡ rightPairγ
    Q =
      ((assoc-left ∙ leftPairγ≡direct) ∙ directγ≡directγ)
      ∙ sym rightPairγ≡direct

    P :
      leftStart ≡ rightPairγ
    P i =
      ⟨⟩-∘ₘ σ₀ M₀ ρ₀ i ∘ₘ γ°

    Q≡P :
      Q ≡ P
    Q≡P =
      sub-setₘ εₘ (GluCtx.Γ° Δ ▷ₘ GluTy.A° A)
        leftStart
        rightPairγ
        Q
        P

    path-Q :
      PathP
        (λ i → fiber (Q i))
        actual-left
        rightPair∙
    path-Q =
      compPathP' {B = fiber} step₁₂₃ step₄

    path :
      PathP
        (λ i → fiber (P i))
        actual-left
        rightPair∙
    path =
      subst
        (λ q →
          PathP
            (λ i → fiber (q i))
            actual-left
            rightPair∙)
        Q≡P
        path-Q
