module DPRLR.Gluing.Simple.Function where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Contravariant
open import DPRLR.Simplicial.FunctionExtensionality
open import DPRLR.Object.Simple.Model
open import DPRLR.Gluing.Simple.Judgment
open import DPRLR.Gluing.Simple.Substitution

module _ {ℓM : Level} (𝓜 : SimpleDirectedCwF ℓM) where

  open SimpleDirectedCwF 𝓜
    renaming
      ( Ctx to Ctxₘ
      ; Ty to Tyₘ
      ; Sub to Subₘ
      ; Tm to Tmₘ
      ; id to idₘ
      ; ε to εₘ
      ; _▷_ to _▷ₘ_
      ; p to pₘ
      ; q to qₘ
      ; ⟨_,_⟩ to ⟨_,_⟩ₘ
      ; _∘_ to _∘ₘ_
      ; _[_]Tm to _[_]Tmₘ
      ; id-left to id-leftₘ
      ; ∘-assoc to ∘-assocₘ
      ; Tm-∘ to Tm-∘ₘ
      ; p-⟨⟩ to p-⟨⟩ₘ
      ; q-⟨⟩ to q-⟨⟩ₘ
      ; ⟨⟩-∘ to ⟨⟩-∘ₘ
      ; _⇒ᵗʸ_ to _⇒ₘ_
      ; lam to lamₘ
      ; app to appₘ
      ; lam[] to lam[]ₘ
      ; app[] to app[]ₘ
      ; β⇒ to β⇒ₘ
      ; β⇒-subst to β⇒-substₘ
      ; η⇒ to η⇒ₘ
      ; tm-set to tm-setₘ
      ; sub-set to sub-setₘ
      ; tm-thin to tm-thinₘ
      )

  FUN∙ :
    (A B : GluTy 𝓜)
    → Tmₘ εₘ (GluTy.A° A ⇒ₘ GluTy.A° B)
    → Type ℓM
  FUN∙ A B F =
    (M° : Tmₘ εₘ (GluTy.A° A))
    → GluTy.A∙ A M°
    → GluTy.A∙ B (appₘ F M°)

  FUN-contravariant :
    (A B : GluTy 𝓜)
    → isContravariant (FUN∙ A B)
  FUN-contravariant A B =
    contravariant-Π λ M° →
      contravariant-Π λ _ →
        contravariant-reindex
          (λ F → appₘ F M°)
          (GluTy.cA B)

  FUN :
    (A B : GluTy 𝓜)
    → GluTy 𝓜
  GluTy.A° (FUN A B) = GluTy.A° A ⇒ₘ GluTy.A° B
  GluTy.A∙ (FUN A B) = FUN∙ A B
  GluTy.cA (FUN A B) = FUN-contravariant A B

  FUN∙-subst :
    (A B : GluTy 𝓜)
    {F G : Tmₘ εₘ (GluTy.A° A ⇒ₘ GluTy.A° B)}
    (p : F ≡ G)
    (F∙ : FUN∙ A B F)
    (M : Tmₘ εₘ (GluTy.A° A))
    (M∙ : GluTy.A∙ A M)
    → subst (FUN∙ A B) p F∙ M M∙
      ≡ subst (GluTy.A∙ B) (cong (λ H → appₘ H M) p) (F∙ M M∙)
  FUN∙-subst A B {F = F} p =
    J
      (λ G p →
        (F∙ : FUN∙ A B F)
        (M : Tmₘ εₘ (GluTy.A° A))
        (M∙ : GluTy.A∙ A M)
        → subst (FUN∙ A B) p F∙ M M∙
          ≡ subst (GluTy.A∙ B) (cong (λ H → appₘ H M) p) (F∙ M M∙))
      base
      p
    where
    base :
      (F∙ : FUN∙ A B F)
      (M : Tmₘ εₘ (GluTy.A° A))
      (M∙ : GluTy.A∙ A M)
      → subst (FUN∙ A B) refl F∙ M M∙
        ≡ subst (GluTy.A∙ B) (cong (λ H → appₘ H M) refl) (F∙ M M∙)
    base F∙ M M∙ =
      cong (λ F∙′ → F∙′ M M∙) (substRefl {B = FUN∙ A B} F∙)
      ∙ sym (substRefl {B = GluTy.A∙ B} (F∙ M M∙))

  APP :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    → GluTm 𝓜 Γ (FUN A B)
    → GluTm 𝓜 Γ A
    → GluTm 𝓜 Γ B
  GluTm.M° (APP F M) = appₘ (GluTm.M° F) (GluTm.M° M)
  GluTm.M∙ (APP {A = A} {B = B} F M) γ° γ∙ =
    subst
      (GluTy.A∙ B)
      (sym (app[]ₘ (GluTm.M° F) (GluTm.M° M) γ°))
      (GluTm.M∙ F γ° γ∙
        (GluTm.M° M [ γ° ]Tmₘ)
        (GluTm.M∙ M γ° γ∙))

  APP[] :
    {Γ Δ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (F : GluTm 𝓜 Δ (FUN A B))
    (M : GluTm 𝓜 Δ A)
    (σ : GluSub 𝓜 Γ Δ)
    → _[_]Tmᵍ 𝓜 (APP {A = A} {B = B} F M) σ
      ≡ APP {A = A} {B = B}
          (_[_]Tmᵍ 𝓜 F σ)
          (_[_]Tmᵍ 𝓜 M σ)
  GluTm.M° (APP[] F M σ i) =
    app[]ₘ (GluTm.M° F) (GluTm.M° M) (GluSub.σ° σ) i
  GluTm.M∙ (APP[] {Γ = Γ} {Δ = Δ} {A = A} {B = B} F M σ i) γ° γ∙ =
    path i
    where
    C = GluTy.A∙ B
    F₀ = GluTm.M° F
    M₀ = GluTm.M° M
    σ₀ = GluSub.σ° σ

    σγ =
      σ₀ ∘ₘ γ°

    F∙σγ =
      GluTm.M∙ F σγ (GluSub.σ∙ σ γ° γ∙)

    M∙σγ =
      GluTm.M∙ M σγ (GluSub.σ∙ σ γ° γ∙)

    compApp :
      (appₘ F₀ M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ appₘ F₀ M₀ [ σγ ]Tmₘ
    compApp =
      Tm-∘ₘ (appₘ F₀ M₀) σ₀ γ°

    appσγ :
      appₘ F₀ M₀ [ σγ ]Tmₘ
      ≡ appₘ (F₀ [ σγ ]Tmₘ) (M₀ [ σγ ]Tmₘ)
    appσγ =
      app[]ₘ F₀ M₀ σγ

    compF :
      (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ F₀ [ σγ ]Tmₘ
    compF =
      Tm-∘ₘ F₀ σ₀ γ°

    compM :
      (M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ M₀ [ σγ ]Tmₘ
    compM =
      Tm-∘ₘ M₀ σ₀ γ°

    appTarget :
      appₘ (F₀ [ σ₀ ]Tmₘ) (M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ appₘ ((F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
          ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    appTarget =
      app[]ₘ (F₀ [ σ₀ ]Tmₘ) (M₀ [ σ₀ ]Tmₘ) γ°

    arg-path :
      M₀ [ σγ ]Tmₘ ≡ (M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    arg-path =
      sym compM

    F-path :
      F₀ [ σγ ]Tmₘ ≡ (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    F-path =
      sym compF

    app-components :
      appₘ (F₀ [ σγ ]Tmₘ) (M₀ [ σγ ]Tmₘ)
      ≡ appₘ ((F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
          ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    app-components =
      (λ i → appₘ (F₀ [ σγ ]Tmₘ) (arg-path i))
      ∙
      (λ i →
        appₘ (F-path i)
          ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ))

    M∙target :
      GluTy.A∙ A ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    M∙target =
      subst (GluTy.A∙ A) arg-path M∙σγ

    right-fun :
      FUN∙ A B ((F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    right-fun =
      subst (FUN∙ A B) F-path F∙σγ

    actual :
      C ((appₘ F₀ M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    actual =
      subst C (sym compApp)
        (subst C (sym appσγ)
          (F∙σγ (M₀ [ σγ ]Tmₘ) M∙σγ))

    target :
      C (appₘ (F₀ [ σ₀ ]Tmₘ) (M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    target =
      subst C (sym appTarget) (right-fun _ M∙target)

    step₁ :
      PathP
        (λ i → C (compApp i))
        actual
        (subst C (sym appσγ)
          (F∙σγ (M₀ [ σγ ]Tmₘ) M∙σγ))
    step₁ i =
      subst-filler
        C
        (sym compApp)
        (subst C (sym appσγ)
          (F∙σγ (M₀ [ σγ ]Tmₘ) M∙σγ))
        (~ i)

    step₂ :
      PathP
        (λ i → C (appσγ i))
        (subst C (sym appσγ)
          (F∙σγ (M₀ [ σγ ]Tmₘ) M∙σγ))
        (F∙σγ (M₀ [ σγ ]Tmₘ) M∙σγ)
    step₂ i =
      subst-filler
        C
        (sym appσγ)
        (F∙σγ (M₀ [ σγ ]Tmₘ) M∙σγ)
        (~ i)

    step₁₂ :
      PathP
        (λ i → C ((compApp ∙ appσγ) i))
        actual
        (F∙σγ (M₀ [ σγ ]Tmₘ) M∙σγ)
    step₁₂ =
      compPathP' {B = C} step₁ step₂

    arg-path∙ :
      PathP
        (λ i → GluTy.A∙ A (arg-path i))
        M∙σγ
        M∙target
    arg-path∙ =
      subst-filler (GluTy.A∙ A) arg-path M∙σγ

    step₃a :
      PathP
        (λ i → C (appₘ (F₀ [ σγ ]Tmₘ) (arg-path i)))
        (F∙σγ (M₀ [ σγ ]Tmₘ) M∙σγ)
        (F∙σγ ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target)
    step₃a i =
      F∙σγ (arg-path i) (arg-path∙ i)

    step₃b-base :
      PathP
        (λ i →
          C (appₘ (F-path i) ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)))
        (F∙σγ ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target)
        (subst C
          (cong (λ H → appₘ H ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)) F-path)
          (F∙σγ ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target))
    step₃b-base =
      subst-filler
        C
        (cong (λ H → appₘ H ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)) F-path)
        (F∙σγ ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target)

    step₃b :
      PathP
        (λ i →
          C (appₘ (F-path i) ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)))
        (F∙σγ ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target)
        (right-fun ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target)
    step₃b =
      subst
        (λ u →
          PathP
            (λ i →
              C (appₘ (F-path i) ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)))
            (F∙σγ ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target)
            u)
        (sym
          (FUN∙-subst A B
            F-path
            F∙σγ
            ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
            M∙target))
        step₃b-base

    step₃ :
      PathP
        (λ i → C (app-components i))
        (F∙σγ (M₀ [ σγ ]Tmₘ) M∙σγ)
        (right-fun ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target)
    step₃ =
      compPathP' {B = C} step₃a step₃b

    step₁₂₃ :
      PathP
        (λ i → C (((compApp ∙ appσγ) ∙ app-components) i))
        actual
        (right-fun ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target)
    step₁₂₃ =
      compPathP' {B = C} step₁₂ step₃

    step₄-base :
      PathP
        (λ i → C (sym appTarget i))
        (right-fun ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target)
        target
    step₄-base =
      subst-filler
        C
        (sym appTarget)
        (right-fun ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) M∙target)

    Q :
      (appₘ F₀ M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ appₘ (F₀ [ σ₀ ]Tmₘ) (M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    Q =
      (((compApp ∙ appσγ) ∙ app-components) ∙ sym appTarget)

    R :
      (appₘ F₀ M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ appₘ (F₀ [ σ₀ ]Tmₘ) (M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    R i =
      app[]ₘ F₀ M₀ σ₀ i [ γ° ]Tmₘ

    Q≡R :
      Q ≡ R
    Q≡R =
      tm-setₘ εₘ (GluTy.A° B)
        ((appₘ F₀ M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        (appₘ (F₀ [ σ₀ ]Tmₘ) (M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        Q
        R

    path-Q :
      PathP
        (λ i → C (Q i))
        actual
        target
    path-Q =
      compPathP' {B = C} step₁₂₃ step₄-base

    path :
      PathP
        (λ i → C (R i))
        actual
        target
    path =
      subst
        (λ q →
          PathP
            (λ i → C (q i))
            actual
            target)
        Q≡R
        path-Q

  extend-fiber :
    {Γ : GluCtx 𝓜}
    (A : GluTy 𝓜)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    (γ∙ : GluCtx.Γ∙ Γ γ°)
    (M° : Tmₘ εₘ (GluTy.A° A))
    → GluTy.A∙ A M°
    → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) ⟨ γ° , M° ⟩ₘ
  extend-fiber {Γ = Γ} A γ° γ∙ M° M∙ =
    transport
      (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (directγ≡extγ i))
      direct∙
    where
    directγ =
      ⟨ idₘ ∘ₘ γ° , M° ⟩ₘ

    directγ≡extγ :
      directγ ≡ ⟨ γ° , M° ⟩ₘ
    directγ≡extγ i =
      ⟨ id-leftₘ γ° i , M° ⟩ₘ

    p-direct :
      pₘ ∘ₘ directγ ≡ idₘ ∘ₘ γ°
    p-direct =
      p-⟨⟩ₘ (idₘ ∘ₘ γ°) M°

    q-direct :
      qₘ [ directγ ]Tmₘ ≡ M°
    q-direct =
      q-⟨⟩ₘ (idₘ ∘ₘ γ°) M°

    direct∙ :
      GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) directγ
    direct∙ =
      subst (GluCtx.Γ∙ Γ) (sym p-direct)
        (subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙)
      ,
      subst (GluTy.A∙ A) (sym q-direct) M∙

    p-ext :
      pₘ ∘ₘ ⟨ γ° , M° ⟩ₘ ≡ γ°
    p-ext =
      p-⟨⟩ₘ γ° M°

    q-ext :
      qₘ [ ⟨ γ° , M° ⟩ₘ ]Tmₘ ≡ M°
    q-ext =
      q-⟨⟩ₘ γ° M°

  extend-fiber-p :
    {Γ : GluCtx 𝓜}
    (A : GluTy 𝓜)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    (γ∙ : GluCtx.Γ∙ Γ γ°)
    (M° : Tmₘ εₘ (GluTy.A° A))
    (M∙ : GluTy.A∙ A M°)
    → PathP
        (λ i → GluCtx.Γ∙ Γ (p-⟨⟩ₘ γ° M° i))
        (fst (extend-fiber {Γ = Γ} A γ° γ∙ M° M∙))
        γ∙
  extend-fiber-p {Γ = Γ} A γ° γ∙ M° M∙ =
    subst
      (λ p →
        PathP
          (λ i → GluCtx.Γ∙ Γ (p i))
          (fst ext∙)
          γ∙)
      Q≡P
      path-Q
    where
    directγ =
      ⟨ idₘ ∘ₘ γ° , M° ⟩ₘ

    extγ =
      ⟨ γ° , M° ⟩ₘ

    directγ≡extγ :
      directγ ≡ extγ
    directγ≡extγ i =
      ⟨ id-leftₘ γ° i , M° ⟩ₘ

    p-direct :
      pₘ ∘ₘ directγ ≡ idₘ ∘ₘ γ°
    p-direct =
      p-⟨⟩ₘ (idₘ ∘ₘ γ°) M°

    q-direct :
      qₘ [ directγ ]Tmₘ ≡ M°
    q-direct =
      q-⟨⟩ₘ (idₘ ∘ₘ γ°) M°

    direct∙ :
      GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) directγ
    direct∙ =
      subst (GluCtx.Γ∙ Γ) (sym p-direct)
        (subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙)
      ,
      subst (GluTy.A∙ A) (sym q-direct) M∙

    ext∙ :
      GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) extγ
    ext∙ =
      extend-fiber {Γ = Γ} A γ° γ∙ M° M∙

    ext∙-filler :
      PathP
        (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (directγ≡extγ i))
        direct∙
        ext∙
    ext∙-filler =
      transport-filler
        (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (directγ≡extγ i))
        direct∙

    step₁ :
      PathP
        (λ i → GluCtx.Γ∙ Γ (pₘ ∘ₘ sym directγ≡extγ i))
        (fst ext∙)
        (fst direct∙)
    step₁ i =
      fst (ext∙-filler (~ i))

    step₂ :
      PathP
        (λ i → GluCtx.Γ∙ Γ (p-direct i))
        (fst direct∙)
        (subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙)
    step₂ i =
      subst-filler
        (GluCtx.Γ∙ Γ)
        (sym p-direct)
        (subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙)
        (~ i)

    step₃ :
      PathP
        (λ i → GluCtx.Γ∙ Γ (id-leftₘ γ° i))
        (subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙)
        γ∙
    step₃ i =
      subst-filler
        (GluCtx.Γ∙ Γ)
        (sym (id-leftₘ γ°))
        γ∙
        (~ i)

    Q :
      pₘ ∘ₘ extγ ≡ γ°
    Q =
      (cong (λ δ → pₘ ∘ₘ δ) (sym directγ≡extγ) ∙ p-direct)
      ∙ id-leftₘ γ°

    P :
      pₘ ∘ₘ extγ ≡ γ°
    P =
      p-⟨⟩ₘ γ° M°

    Q≡P :
      Q ≡ P
    Q≡P =
      sub-setₘ εₘ (GluCtx.Γ° Γ)
        (pₘ ∘ₘ extγ)
        γ°
        Q
        P

    path-Q₁₂ :
      PathP
        (λ i → GluCtx.Γ∙ Γ
          ((cong (λ δ → pₘ ∘ₘ δ) (sym directγ≡extγ) ∙ p-direct) i))
        (fst ext∙)
        (subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙)
    path-Q₁₂ =
      compPathP' {B = GluCtx.Γ∙ Γ} step₁ step₂

    path-Q :
      PathP
        (λ i → GluCtx.Γ∙ Γ (Q i))
        (fst ext∙)
        γ∙
    path-Q =
      compPathP' {B = GluCtx.Γ∙ Γ} path-Q₁₂ step₃

  extend-fiber-q :
    {Γ : GluCtx 𝓜}
    (A : GluTy 𝓜)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    (γ∙ : GluCtx.Γ∙ Γ γ°)
    (M° : Tmₘ εₘ (GluTy.A° A))
    (M∙ : GluTy.A∙ A M°)
    → PathP
        (λ i → GluTy.A∙ A (q-⟨⟩ₘ γ° M° i))
        (snd (extend-fiber {Γ = Γ} A γ° γ∙ M° M∙))
        M∙
  extend-fiber-q {Γ = Γ} A γ° γ∙ M° M∙ =
    subst
      (λ p →
        PathP
          (λ i → GluTy.A∙ A (p i))
          (snd ext∙)
          M∙)
      Q≡P
      path-Q
    where
    directγ =
      ⟨ idₘ ∘ₘ γ° , M° ⟩ₘ

    extγ =
      ⟨ γ° , M° ⟩ₘ

    directγ≡extγ :
      directγ ≡ extγ
    directγ≡extγ i =
      ⟨ id-leftₘ γ° i , M° ⟩ₘ

    p-direct :
      pₘ ∘ₘ directγ ≡ idₘ ∘ₘ γ°
    p-direct =
      p-⟨⟩ₘ (idₘ ∘ₘ γ°) M°

    q-direct :
      qₘ [ directγ ]Tmₘ ≡ M°
    q-direct =
      q-⟨⟩ₘ (idₘ ∘ₘ γ°) M°

    direct∙ :
      GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) directγ
    direct∙ =
      subst (GluCtx.Γ∙ Γ) (sym p-direct)
        (subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙)
      ,
      subst (GluTy.A∙ A) (sym q-direct) M∙

    ext∙ :
      GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) extγ
    ext∙ =
      extend-fiber {Γ = Γ} A γ° γ∙ M° M∙

    ext∙-filler :
      PathP
        (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (directγ≡extγ i))
        direct∙
        ext∙
    ext∙-filler =
      transport-filler
        (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (directγ≡extγ i))
        direct∙

    step₁ :
      PathP
        (λ i → GluTy.A∙ A (qₘ [ sym directγ≡extγ i ]Tmₘ))
        (snd ext∙)
        (snd direct∙)
    step₁ i =
      snd (ext∙-filler (~ i))

    step₂ :
      PathP
        (λ i → GluTy.A∙ A (q-direct i))
        (snd direct∙)
        M∙
    step₂ i =
      subst-filler
        (GluTy.A∙ A)
        (sym q-direct)
        M∙
        (~ i)

    Q :
      qₘ [ extγ ]Tmₘ ≡ M°
    Q =
      cong (λ δ → qₘ [ δ ]Tmₘ) (sym directγ≡extγ)
      ∙ q-direct

    P :
      qₘ [ extγ ]Tmₘ ≡ M°
    P =
      q-⟨⟩ₘ γ° M°

    Q≡P :
      Q ≡ P
    Q≡P =
      tm-setₘ εₘ (GluTy.A° A)
        (qₘ [ extγ ]Tmₘ)
        M°
        Q
        P

    path-Q :
      PathP
        (λ i → GluTy.A∙ A (Q i))
        (snd ext∙)
        M∙
    path-Q =
      compPathP' {B = GluTy.A∙ A} step₁ step₂

  lift-extend-path :
    {Γ Δ : GluCtx 𝓜}
    {A : GluTy 𝓜}
    (σ : GluSub 𝓜 Γ Δ)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    (M° : Tmₘ εₘ (GluTy.A° A))
    → GluSub.σ° (liftᵍ 𝓜 {A = A} σ) ∘ₘ ⟨ γ° , M° ⟩ₘ
      ≡ ⟨ GluSub.σ° σ ∘ₘ γ° , M° ⟩ₘ
  lift-extend-path σ γ° M° =
    ⟨⟩-∘ₘ (GluSub.σ° σ ∘ₘ pₘ) qₘ ⟨ γ° , M° ⟩ₘ
    ∙ (λ i → ⟨ p-path i , q-path i ⟩ₘ)
    where
    p-path :
      (GluSub.σ° σ ∘ₘ pₘ) ∘ₘ ⟨ γ° , M° ⟩ₘ
      ≡ GluSub.σ° σ ∘ₘ γ°
    p-path =
      ∘-assocₘ (GluSub.σ° σ) pₘ ⟨ γ° , M° ⟩ₘ
      ∙ cong (λ δ → GluSub.σ° σ ∘ₘ δ)
          (p-⟨⟩ₘ γ° M°)

    q-path :
      qₘ [ ⟨ γ° , M° ⟩ₘ ]Tmₘ ≡ M°
    q-path =
      q-⟨⟩ₘ γ° M°

  lift-extend-fiber :
    {Γ Δ : GluCtx 𝓜}
    {A : GluTy 𝓜}
    (σ : GluSub 𝓜 Γ Δ)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    (γ∙ : GluCtx.Γ∙ Γ γ°)
    (M° : Tmₘ εₘ (GluTy.A° A))
    (M∙ : GluTy.A∙ A M°)
    → PathP
        (λ i →
          GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Δ A)
            (lift-extend-path {A = A} σ γ° M° i))
        (GluSub.σ∙ (liftᵍ 𝓜 {A = A} σ)
          ⟨ γ° , M° ⟩ₘ
          (extend-fiber {Γ = Γ} A γ° γ∙ M° M∙))
        (extend-fiber {Γ = Δ} A
          (GluSub.σ° σ ∘ₘ γ°)
          (GluSub.σ∙ σ γ° γ∙)
          M°
          M∙)
  lift-extend-fiber {Γ = Γ} {Δ = Δ} {A = A} σ γ° γ∙ M° M∙ =
    subst
      (λ q →
        PathP
          (λ i → fiber (q i))
          source
          target)
      Q≡P
      path-Q
    where
    σ₀ = GluSub.σ° σ

    σγ =
      σ₀ ∘ₘ γ°

    extγ =
      ⟨ γ° , M° ⟩ₘ

    sourcePair =
      GluSub.σ° (liftᵍ 𝓜 {A = A} σ) ∘ₘ extγ

    sourceDirect =
      ⟨ (σ₀ ∘ₘ pₘ) ∘ₘ extγ , qₘ [ extγ ]Tmₘ ⟩ₘ

    targetDirect =
      ⟨ idₘ ∘ₘ σγ , M° ⟩ₘ

    targetPair =
      ⟨ σγ , M° ⟩ₘ

    fiber :
      Subₘ εₘ (GluCtx.Γ° Δ ▷ₘ GluTy.A° A)
      → Type ℓM
    fiber =
      GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Δ A)

    ext∙ :
      GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) extγ
    ext∙ =
      extend-fiber {Γ = Γ} A γ° γ∙ M° M∙

    source :
      fiber sourcePair
    source =
      GluSub.σ∙ (liftᵍ 𝓜 {A = A} σ) extγ ext∙

    target :
      fiber targetPair
    target =
      extend-fiber {Γ = Δ} A σγ (GluSub.σ∙ σ γ° γ∙) M° M∙

    pairγ≡direct :
      sourcePair ≡ sourceDirect
    pairγ≡direct =
      ⟨⟩-∘ₘ (σ₀ ∘ₘ pₘ) qₘ extγ

    assocσp :
      (σ₀ ∘ₘ pₘ) ∘ₘ extγ ≡ σ₀ ∘ₘ (pₘ ∘ₘ extγ)
    assocσp =
      ∘-assocₘ σ₀ pₘ extγ

    p-ext :
      pₘ ∘ₘ extγ ≡ γ°
    p-ext =
      p-⟨⟩ₘ γ° M°

    q-ext :
      qₘ [ extγ ]Tmₘ ≡ M°
    q-ext =
      q-⟨⟩ₘ γ° M°

    σ-p-ext :
      σ₀ ∘ₘ (pₘ ∘ₘ extγ) ≡ σγ
    σ-p-ext =
      cong (λ δ → σ₀ ∘ₘ δ) p-ext

    p-path :
      (σ₀ ∘ₘ pₘ) ∘ₘ extγ ≡ σγ
    p-path =
      assocσp ∙ σ-p-ext

    directγ≡targetDirect :
      sourceDirect ≡ targetDirect
    directγ≡targetDirect i =
      ⟨ (p-path ∙ sym (id-leftₘ σγ)) i , q-ext i ⟩ₘ

    targetDirect≡targetPair :
      targetDirect ≡ targetPair
    targetDirect≡targetPair i =
      ⟨ id-leftₘ σγ i , M° ⟩ₘ

    p-source-direct :
      pₘ ∘ₘ sourceDirect ≡ (σ₀ ∘ₘ pₘ) ∘ₘ extγ
    p-source-direct =
      p-⟨⟩ₘ ((σ₀ ∘ₘ pₘ) ∘ₘ extγ) (qₘ [ extγ ]Tmₘ)

    q-source-direct :
      qₘ [ sourceDirect ]Tmₘ ≡ qₘ [ extγ ]Tmₘ
    q-source-direct =
      q-⟨⟩ₘ ((σ₀ ∘ₘ pₘ) ∘ₘ extγ) (qₘ [ extγ ]Tmₘ)

    p-target-direct :
      pₘ ∘ₘ targetDirect ≡ idₘ ∘ₘ σγ
    p-target-direct =
      p-⟨⟩ₘ (idₘ ∘ₘ σγ) M°

    q-target-direct :
      qₘ [ targetDirect ]Tmₘ ≡ M°
    q-target-direct =
      q-⟨⟩ₘ (idₘ ∘ₘ σγ) M°

    σpSub =
      _∘ᵍ_ 𝓜 σ (pᵍ 𝓜 {Γ = Γ} {A = A})

    σp-on-ext :
      GluCtx.Γ∙ Δ (σ₀ ∘ₘ (pₘ ∘ₘ extγ))
    σp-on-ext =
      GluSub.σ∙ σ (pₘ ∘ₘ extγ) (fst ext∙)

    σp∙ :
      GluCtx.Γ∙ Δ ((σ₀ ∘ₘ pₘ) ∘ₘ extγ)
    σp∙ =
      GluSub.σ∙ σpSub extγ ext∙

    sourceDirect∙ :
      fiber sourceDirect
    sourceDirect∙ =
      subst (GluCtx.Γ∙ Δ) (sym p-source-direct) σp∙
      ,
      subst (GluTy.A∙ A) (sym q-source-direct) (snd ext∙)

    source-filler :
      PathP
        (λ i → fiber (pairγ≡direct (~ i)))
        sourceDirect∙
        source
    source-filler =
      transport-filler
        (λ i → fiber (pairγ≡direct (~ i)))
        sourceDirect∙

    σγ∙ :
      GluCtx.Γ∙ Δ σγ
    σγ∙ =
      GluSub.σ∙ σ γ° γ∙

    targetDirect∙ :
      fiber targetDirect
    targetDirect∙ =
      subst (GluCtx.Γ∙ Δ) (sym p-target-direct)
        (subst (GluCtx.Γ∙ Δ) (sym (id-leftₘ σγ)) σγ∙)
      ,
      subst (GluTy.A∙ A) (sym q-target-direct) M∙

    target-filler :
      PathP
        (λ i → fiber (targetDirect≡targetPair i))
        targetDirect∙
        target
    target-filler =
      transport-filler
        (λ i → fiber (targetDirect≡targetPair i))
        targetDirect∙

    step₁ :
      PathP
        (λ i → fiber (pairγ≡direct i))
        source
        sourceDirect∙
    step₁ i =
      source-filler (~ i)

    p-step₁ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (p-source-direct i))
        (fst sourceDirect∙)
        σp∙
    p-step₁ i =
      subst-filler
        (GluCtx.Γ∙ Δ)
        (sym p-source-direct)
        σp∙
        (~ i)

    p-step₂a :
      PathP
        (λ i → GluCtx.Γ∙ Δ (assocσp i))
        σp∙
        σp-on-ext
    p-step₂a i =
      subst-filler
        (GluCtx.Γ∙ Δ)
        (sym assocσp)
        σp-on-ext
        (~ i)

    p-step₂b :
      PathP
        (λ i → GluCtx.Γ∙ Δ (σ-p-ext i))
        σp-on-ext
        σγ∙
    p-step₂b i =
      GluSub.σ∙ σ (p-ext i)
        (extend-fiber-p {Γ = Γ} A γ° γ∙ M° M∙ i)

    p-step₂ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (p-path i))
        σp∙
        σγ∙
    p-step₂ =
      compPathP' {B = GluCtx.Γ∙ Δ} p-step₂a p-step₂b

    p-step₃ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (sym (id-leftₘ σγ) i))
        σγ∙
        (subst (GluCtx.Γ∙ Δ) (sym (id-leftₘ σγ)) σγ∙)
    p-step₃ =
      subst-filler
        (GluCtx.Γ∙ Δ)
        (sym (id-leftₘ σγ))
        σγ∙

    p-step₂₃ :
      PathP
        (λ i → GluCtx.Γ∙ Δ ((p-path ∙ sym (id-leftₘ σγ)) i))
        σp∙
        (subst (GluCtx.Γ∙ Δ) (sym (id-leftₘ σγ)) σγ∙)
    p-step₂₃ =
      compPathP' {B = GluCtx.Γ∙ Δ} p-step₂ p-step₃

    p-step₄ :
      PathP
        (λ i → GluCtx.Γ∙ Δ (sym p-target-direct i))
        (subst (GluCtx.Γ∙ Δ) (sym (id-leftₘ σγ)) σγ∙)
        (fst targetDirect∙)
    p-step₄ =
      subst-filler
        (GluCtx.Γ∙ Δ)
        (sym p-target-direct)
        (subst (GluCtx.Γ∙ Δ) (sym (id-leftₘ σγ)) σγ∙)

    p-step₂₃₄ :
      PathP
        (λ i →
          GluCtx.Γ∙ Δ
            (((p-path ∙ sym (id-leftₘ σγ)) ∙ sym p-target-direct) i))
        σp∙
        (fst targetDirect∙)
    p-step₂₃₄ =
      compPathP' {B = GluCtx.Γ∙ Δ} p-step₂₃ p-step₄

    p-Q :
      pₘ ∘ₘ sourceDirect ≡ pₘ ∘ₘ targetDirect
    p-Q =
      p-source-direct
      ∙ ((p-path ∙ sym (id-leftₘ σγ)) ∙ sym p-target-direct)

    p-path-Q :
      PathP
        (λ i → GluCtx.Γ∙ Δ (p-Q i))
        (fst sourceDirect∙)
        (fst targetDirect∙)
    p-path-Q =
      compPathP' {B = GluCtx.Γ∙ Δ} p-step₁ p-step₂₃₄

    p-cong≡Q :
      cong (λ δ → pₘ ∘ₘ δ) directγ≡targetDirect ≡ p-Q
    p-cong≡Q =
      sub-setₘ εₘ (GluCtx.Γ° Δ)
        (pₘ ∘ₘ sourceDirect)
        (pₘ ∘ₘ targetDirect)
        (cong (λ δ → pₘ ∘ₘ δ) directγ≡targetDirect)
        p-Q

    p-pathP :
      PathP
        (λ i → GluCtx.Γ∙ Δ (pₘ ∘ₘ directγ≡targetDirect i))
        (fst sourceDirect∙)
        (fst targetDirect∙)
    p-pathP =
      subst
        (λ p →
          PathP
            (λ i → GluCtx.Γ∙ Δ (p i))
            (fst sourceDirect∙)
            (fst targetDirect∙))
        (sym p-cong≡Q)
        p-path-Q

    q-step₁ :
      PathP
        (λ i → GluTy.A∙ A (q-source-direct i))
        (snd sourceDirect∙)
        (snd ext∙)
    q-step₁ i =
      subst-filler
        (GluTy.A∙ A)
        (sym q-source-direct)
        (snd ext∙)
        (~ i)

    q-step₂ :
      PathP
        (λ i → GluTy.A∙ A (q-ext i))
        (snd ext∙)
        M∙
    q-step₂ =
      extend-fiber-q {Γ = Γ} A γ° γ∙ M° M∙

    q-step₁₂ :
      PathP
        (λ i → GluTy.A∙ A ((q-source-direct ∙ q-ext) i))
        (snd sourceDirect∙)
        M∙
    q-step₁₂ =
      compPathP' {B = GluTy.A∙ A} q-step₁ q-step₂

    q-step₃ :
      PathP
        (λ i → GluTy.A∙ A (sym q-target-direct i))
        M∙
        (snd targetDirect∙)
    q-step₃ =
      subst-filler
        (GluTy.A∙ A)
        (sym q-target-direct)
        M∙

    q-Q :
      qₘ [ sourceDirect ]Tmₘ ≡ qₘ [ targetDirect ]Tmₘ
    q-Q =
      (q-source-direct ∙ q-ext) ∙ sym q-target-direct

    q-path-Q :
      PathP
        (λ i → GluTy.A∙ A (q-Q i))
        (snd sourceDirect∙)
        (snd targetDirect∙)
    q-path-Q =
      compPathP' {B = GluTy.A∙ A} q-step₁₂ q-step₃

    q-cong≡Q :
      cong (λ δ → qₘ [ δ ]Tmₘ) directγ≡targetDirect ≡ q-Q
    q-cong≡Q =
      tm-setₘ εₘ (GluTy.A° A)
        (qₘ [ sourceDirect ]Tmₘ)
        (qₘ [ targetDirect ]Tmₘ)
        (cong (λ δ → qₘ [ δ ]Tmₘ) directγ≡targetDirect)
        q-Q

    q-pathP :
      PathP
        (λ i → GluTy.A∙ A (qₘ [ directγ≡targetDirect i ]Tmₘ))
        (snd sourceDirect∙)
        (snd targetDirect∙)
    q-pathP =
      subst
        (λ q →
          PathP
            (λ i → GluTy.A∙ A (q i))
            (snd sourceDirect∙)
            (snd targetDirect∙))
        (sym q-cong≡Q)
        q-path-Q

    step₂ :
      PathP
        (λ i → fiber (directγ≡targetDirect i))
        sourceDirect∙
        targetDirect∙
    step₂ =
      ΣPathP (p-pathP , q-pathP)

    step₁₂ :
      PathP
        (λ i → fiber ((pairγ≡direct ∙ directγ≡targetDirect) i))
        source
        targetDirect∙
    step₁₂ =
      compPathP' {B = fiber} step₁ step₂

    step₃ :
      PathP
        (λ i → fiber (targetDirect≡targetPair i))
        targetDirect∙
        target
    step₃ =
      target-filler

    Q :
      sourcePair ≡ targetPair
    Q =
      (pairγ≡direct ∙ directγ≡targetDirect) ∙ targetDirect≡targetPair

    P :
      sourcePair ≡ targetPair
    P =
      lift-extend-path {A = A} σ γ° M°

    Q≡P :
      Q ≡ P
    Q≡P =
      sub-setₘ εₘ (GluCtx.Γ° Δ ▷ₘ GluTy.A° A)
        sourcePair
        targetPair
        Q
        P

    path-Q :
      PathP
        (λ i → fiber (Q i))
        source
        target
    path-Q =
      compPathP' {B = fiber} step₁₂ step₃

  lam-contractum∙ :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (N : GluTm 𝓜 (_▷ᵍ_ 𝓜 Γ A) B)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    (γ∙ : GluCtx.Γ∙ Γ γ°)
    (M° : Tmₘ εₘ (GluTy.A° A))
    (M∙ : GluTy.A∙ A M°)
    → GluTy.A∙ B (GluTm.M° N [ ⟨ γ° , M° ⟩ₘ ]Tmₘ)
  lam-contractum∙ {Γ = Γ} {A = A} N γ° γ∙ M° M∙ =
    GluTm.M∙ N
      ⟨ γ° , M° ⟩ₘ
      (extend-fiber {Γ = Γ} A γ° γ∙ M° M∙)

  LAM :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    → GluTm 𝓜 (_▷ᵍ_ 𝓜 Γ A) B
    → GluTm 𝓜 Γ (FUN A B)
  GluTm.M° (LAM N) = lamₘ (GluTm.M° N)
  GluTm.M∙ (LAM {A = A} {B = B} N) γ° γ∙ = lam∙
    where
    lam∙ :
      (M° : Tmₘ εₘ (GluTy.A° A))
      → GluTy.A∙ A M°
      → GluTy.A∙ B (appₘ (lamₘ (GluTm.M° N) [ γ° ]Tmₘ) M°)
    lam∙ M° M∙ =
      contrav-transport
        (GluTy.cA B)
        (β⇒-substₘ (GluTm.M° N) γ° M°)
        (lam-contractum∙ {A = A} N γ° γ∙ M° M∙)

  LAM[] :
    {Γ Δ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (N : GluTm 𝓜 (_▷ᵍ_ 𝓜 Δ A) B)
    (σ : GluSub 𝓜 Γ Δ)
    → _[_]Tmᵍ 𝓜 (LAM {A = A} {B = B} N) σ
      ≡ LAM {A = A} {B = B}
          (_[_]Tmᵍ 𝓜 N (liftᵍ 𝓜 {A = A} σ))
  GluTm.M° (LAM[] N σ i) =
    lam[]ₘ (GluTm.M° N) (GluSub.σ° σ) i
  GluTm.M∙ (LAM[] {Γ = Γ} {Δ = Δ} {A = A} {B = B} N σ i) γ° γ∙ Mγ Mγ∙ =
    path i
    where
    C = GluTy.A∙ B
    N₀ = GluTm.M° N
    σ₀ = GluSub.σ° σ

    σγ :
      Subₘ εₘ (GluCtx.Γ° Δ)
    σγ =
      σ₀ ∘ₘ γ°

    σγ∙ :
      GluCtx.Γ∙ Δ σγ
    σγ∙ =
      GluSub.σ∙ σ γ° γ∙

    liftσ :
      Subₘ (GluCtx.Γ° Γ ▷ₘ GluTy.A° A)
        (GluCtx.Γ° Δ ▷ₘ GluTy.A° A)
    liftσ =
      GluSub.σ° (liftᵍ 𝓜 {A = A} σ)

    Nσ :
      GluTm 𝓜 (_▷ᵍ_ 𝓜 Γ A) B
    Nσ =
      _[_]Tmᵍ 𝓜 N (liftᵍ 𝓜 {A = A} σ)

    extΓ :
      Subₘ εₘ (GluCtx.Γ° Γ ▷ₘ GluTy.A° A)
    extΓ =
      ⟨ γ° , Mγ ⟩ₘ

    extΓ∙ :
      GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) extΓ
    extΓ∙ =
      extend-fiber {Γ = Γ} A γ° γ∙ Mγ Mγ∙

    extΔ :
      Subₘ εₘ (GluCtx.Γ° Δ ▷ₘ GluTy.A° A)
    extΔ =
      ⟨ σγ , Mγ ⟩ₘ

    extΔ∙ :
      GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Δ A) extΔ
    extΔ∙ =
      extend-fiber {Γ = Δ} A σγ σγ∙ Mγ Mγ∙

    sourceTerm :
      Tmₘ εₘ (GluTy.A° B)
    sourceTerm =
      appₘ (lamₘ N₀ [ σγ ]Tmₘ) Mγ

    targetTerm :
      Tmₘ εₘ (GluTy.A° B)
    targetTerm =
      appₘ (lamₘ (N₀ [ liftσ ]Tmₘ) [ γ° ]Tmₘ) Mγ

    sourceContractTerm :
      Tmₘ εₘ (GluTy.A° B)
    sourceContractTerm =
      N₀ [ extΔ ]Tmₘ

    targetContractTerm :
      Tmₘ εₘ (GluTy.A° B)
    targetContractTerm =
      (N₀ [ liftσ ]Tmₘ) [ extΓ ]Tmₘ

    compLam :
      (lamₘ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ lamₘ N₀ [ σγ ]Tmₘ
    compLam =
      Tm-∘ₘ (lamₘ N₀) σ₀ γ°

    leftPathBack :
      sourceTerm
      ≡ appₘ ((lamₘ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) Mγ
    leftPathBack =
      cong (λ H → appₘ H Mγ) (sym compLam)

    sourceHom :
      sourceTerm ≤ sourceContractTerm
    sourceHom =
      β⇒-substₘ N₀ σγ Mγ

    targetHom :
      targetTerm ≤ targetContractTerm
    targetHom =
      β⇒-substₘ (N₀ [ liftσ ]Tmₘ) γ° Mγ

    sourceContract∙ :
      C sourceContractTerm
    sourceContract∙ =
      lam-contractum∙ {Γ = Δ} {A = A} N σγ σγ∙ Mγ Mγ∙

    targetContract∙ :
      C targetContractTerm
    targetContract∙ =
      lam-contractum∙ {Γ = Γ} {A = A}
        Nσ
        γ°
        γ∙
        Mγ
        Mγ∙

    source :
      C sourceTerm
    source =
      contrav-transport
        (GluTy.cA B)
        sourceHom
        sourceContract∙

    target :
      C targetTerm
    target =
      contrav-transport
        (GluTy.cA B)
        targetHom
        targetContract∙

    actual :
      C (appₘ ((lamₘ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) Mγ)
    actual =
      subst (FUN∙ A B)
        (sym compLam)
        (GluTm.M∙ (LAM {Γ = Δ} {A = A} {B = B} N) σγ σγ∙)
        Mγ
        Mγ∙

    actual≡subst :
      actual ≡ subst C leftPathBack source
    actual≡subst =
      FUN∙-subst A B
        (sym compLam)
        (GluTm.M∙ (LAM {Γ = Δ} {A = A} {B = B} N) σγ σγ∙)
        Mγ
        Mγ∙

    rawLiftγ :
      Subₘ (εₘ ▷ₘ GluTy.A° A) (GluCtx.Γ° Γ ▷ₘ GluTy.A° A)
    rawLiftγ =
      ⟨ γ° ∘ₘ pₘ , qₘ ⟩ₘ

    rawLiftσγ :
      Subₘ (εₘ ▷ₘ GluTy.A° A) (GluCtx.Γ° Δ ▷ₘ GluTy.A° A)
    rawLiftσγ =
      ⟨ σγ ∘ₘ pₘ , qₘ ⟩ₘ

    lift-compose-path :
      liftσ ∘ₘ rawLiftγ ≡ rawLiftσγ
    lift-compose-path =
      ⟨⟩-∘ₘ (σ₀ ∘ₘ pₘ) qₘ rawLiftγ
      ∙ (λ i → ⟨ p-path i , q-path i ⟩ₘ)
      where
      p-path :
        (σ₀ ∘ₘ pₘ) ∘ₘ rawLiftγ
        ≡ σγ ∘ₘ pₘ
      p-path =
        ∘-assocₘ σ₀ pₘ rawLiftγ
        ∙ cong (λ δ → σ₀ ∘ₘ δ)
            (p-⟨⟩ₘ (γ° ∘ₘ pₘ) qₘ)
        ∙ sym (∘-assocₘ σ₀ γ° pₘ)

      q-path :
        qₘ [ rawLiftγ ]Tmₘ ≡ qₘ
      q-path =
        q-⟨⟩ₘ (γ° ∘ₘ pₘ) qₘ

    body-path :
      N₀ [ rawLiftσγ ]Tmₘ
      ≡ (N₀ [ liftσ ]Tmₘ) [ rawLiftγ ]Tmₘ
    body-path =
      sym (cong (λ δ → N₀ [ δ ]Tmₘ) lift-compose-path)
      ∙ sym (Tm-∘ₘ N₀ liftσ rawLiftγ)

    lam-rest :
      lamₘ N₀ [ σγ ]Tmₘ
      ≡ lamₘ (N₀ [ liftσ ]Tmₘ) [ γ° ]Tmₘ
    lam-rest =
      lam[]ₘ N₀ σγ
      ∙ cong lamₘ body-path
      ∙ sym (lam[]ₘ (N₀ [ liftσ ]Tmₘ) γ°)

    source-app-path :
      sourceTerm ≡ targetTerm
    source-app-path =
      cong (λ F → appₘ F Mγ) lam-rest

    contractum-path :
      targetContractTerm ≡ sourceContractTerm
    contractum-path =
      Tm-∘ₘ N₀ liftσ extΓ
      ∙ cong (λ δ → N₀ [ δ ]Tmₘ)
          (lift-extend-path {A = A} σ γ° Mγ)

    target-step₁ :
      PathP
        (λ i → C (Tm-∘ₘ N₀ liftσ extΓ i))
        targetContract∙
        (GluTm.M∙ N
          (liftσ ∘ₘ extΓ)
          (GluSub.σ∙ (liftᵍ 𝓜 {A = A} σ) extΓ extΓ∙))
    target-step₁ i =
      subst-filler
        C
        (sym (Tm-∘ₘ N₀ liftσ extΓ))
        (GluTm.M∙ N
          (liftσ ∘ₘ extΓ)
          (GluSub.σ∙ (liftᵍ 𝓜 {A = A} σ) extΓ extΓ∙))
        (~ i)

    target-step₂ :
      PathP
        (λ i →
          C (N₀ [ lift-extend-path {A = A} σ γ° Mγ i ]Tmₘ))
        (GluTm.M∙ N
          (liftσ ∘ₘ extΓ)
          (GluSub.σ∙ (liftᵍ 𝓜 {A = A} σ) extΓ extΓ∙))
        sourceContract∙
    target-step₂ i =
      GluTm.M∙ N
        (lift-extend-path {A = A} σ γ° Mγ i)
        (lift-extend-fiber {A = A} σ γ° γ∙ Mγ Mγ∙ i)

    contractum-pathP :
      PathP
        (λ i → C (contractum-path i))
        targetContract∙
        sourceContract∙
    contractum-pathP =
      compPathP' {B = C} target-step₁ target-step₂

    targetContract≡subst :
      targetContract∙ ≡ subst C (sym contractum-path) sourceContract∙
    targetContract≡subst =
      fromPathP⁻ contractum-pathP

    hom-eq :
      subst (λ w → targetTerm ≤ w) contractum-path targetHom
      ≡ subst (λ w → w ≤ sourceContractTerm) source-app-path sourceHom
    hom-eq =
      tm-thinₘ εₘ (GluTy.A° B)
        targetTerm
        sourceContractTerm
        (subst (λ w → targetTerm ≤ w) contractum-path targetHom)
        (subst (λ w → w ≤ sourceContractTerm) source-app-path sourceHom)

    step₁-base :
      PathP
        (λ i → C (sym leftPathBack i))
        (subst C leftPathBack source)
        source
    step₁-base i =
      subst-filler C leftPathBack source (~ i)

    step₁ :
      PathP
        (λ i → C (sym leftPathBack i))
        actual
        source
    step₁ =
      subst
        (λ u →
          PathP
            (λ i → C (sym leftPathBack i))
            u
            source)
        (sym actual≡subst)
        step₁-base

    step₂-base :
      PathP
        (λ i → C (source-app-path i))
        source
        (contrav-transport
          (GluTy.cA B)
          targetHom
          (subst C (sym contractum-path) sourceContract∙))
    step₂-base =
      contravariant-transport-pathP
        (GluTy.cA B)
        source-app-path
        (sym contractum-path)
        sourceHom
        targetHom
        sourceContract∙
        hom-eq

    step₂ :
      PathP
        (λ i → C (source-app-path i))
        source
        target
    step₂ =
      subst
        (λ u →
          PathP
            (λ i → C (source-app-path i))
            source
            u)
        (cong
          (contrav-transport (GluTy.cA B) targetHom)
          (sym targetContract≡subst))
        step₂-base

    Q :
      appₘ ((lamₘ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) Mγ
      ≡ targetTerm
    Q =
      sym leftPathBack ∙ source-app-path

    R :
      appₘ ((lamₘ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) Mγ
      ≡ targetTerm
    R i =
      appₘ (lam[]ₘ N₀ σ₀ i [ γ° ]Tmₘ) Mγ

    Q≡R :
      Q ≡ R
    Q≡R =
      tm-setₘ εₘ (GluTy.A° B)
        (appₘ ((lamₘ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) Mγ)
        targetTerm
        Q
        R

    path-Q :
      PathP
        (λ i → C (Q i))
        actual
        target
    path-Q =
      compPathP' {B = C} step₁ step₂

    path :
      PathP
        (λ i → C (R i))
        actual
        target
    path =
      subst
        (λ q →
          PathP
            (λ i → C (q i))
            actual
            target)
        Q≡R
        path-Q

  private
    FUN-preserves-β-data :
      {Γ : GluCtx 𝓜}
      {A B : GluTy 𝓜}
      (N : GluTm 𝓜 (_▷ᵍ_ 𝓜 Γ A) B)
      (M : GluTm 𝓜 Γ A)
      → _≤ᵍ_ 𝓜 {Γ = Γ} {A = B}
          (APP {A = A} {B = B} (LAM {A = A} {B = B} N) M)
          (_[_]Tmᵍ 𝓜 N (⟨_,_⟩ᵍ 𝓜 (idᵍ 𝓜 Γ) M))
    _≤ᵍ_.r° (FUN-preserves-β-data N M) =
      β⇒ₘ (GluTm.M° N) (GluTm.M° M)
    _≤ᵍ_.r∙ (FUN-preserves-β-data {Γ = Γ} {A = A} {B = B} N M) γ° γ∙ =
      contravariant-universal-from
        (GluTy.cA B)
        source-eq
      where
      C = GluTy.A∙ B

      Mγ = GluTm.M° M [ γ° ]Tmₘ
      Mγ∙ = GluTm.M∙ M γ° γ∙
      N₀ = GluTm.M° N
      M₀ = GluTm.M° M

      pairSub =
        ⟨_,_⟩ᵍ 𝓜 (idᵍ 𝓜 Γ) M

      sourceTerm =
        appₘ (lamₘ N₀) M₀ [ γ° ]Tmₘ

      app-path :
        sourceTerm ≡ appₘ (lamₘ N₀ [ γ° ]Tmₘ) Mγ
      app-path =
        app[]ₘ (lamₘ N₀) M₀ γ°

      pairγ =
        ⟨ idₘ , M₀ ⟩ₘ ∘ₘ γ°

      directγ =
        ⟨ idₘ ∘ₘ γ° , Mγ ⟩ₘ

      extγ =
        ⟨ γ° , Mγ ⟩ₘ

      pairγ≡directγ :
        pairγ ≡ directγ
      pairγ≡directγ =
        ⟨⟩-∘ₘ idₘ M₀ γ°

      directγ≡extγ :
        directγ ≡ extγ
      directγ≡extγ i =
        ⟨ id-leftₘ γ° i , Mγ ⟩ₘ

      pairγ≡extγ :
        pairγ ≡ extγ
      pairγ≡extγ =
        pairγ≡directγ ∙ directγ≡extγ

      target-comp :
        GluTm.M° (_[_]Tmᵍ 𝓜 N pairSub) [ γ° ]Tmₘ
        ≡ N₀ [ pairγ ]Tmₘ
      target-comp =
        Tm-∘ₘ N₀ ⟨ idₘ , M₀ ⟩ₘ γ°

      target-path :
        GluTm.M° (_[_]Tmᵍ 𝓜 N pairSub) [ γ° ]Tmₘ
        ≡ N₀ [ extγ ]Tmₘ
      target-path =
        target-comp
        ∙ cong (λ ρ → N₀ [ ρ ]Tmₘ) pairγ≡extγ

      β-step :
        appₘ (lamₘ N₀ [ γ° ]Tmₘ) Mγ
        ≤ N₀ [ extγ ]Tmₘ
      β-step =
        β⇒-substₘ N₀ γ° Mγ

      βγ :
        sourceTerm
        ≤ GluTm.M° (_[_]Tmᵍ 𝓜 N pairSub) [ γ° ]Tmₘ
      βγ =
        hom-map (λ t → t [ γ° ]Tmₘ) (β⇒ₘ N₀ M₀)

      target∙ =
        GluTm.M∙ (_[_]Tmᵍ 𝓜 N pairSub) γ° γ∙

      direct∙ =
        lam-contractum∙ {Γ = Γ} {A = A} N γ° γ∙ Mγ Mγ∙

      p-direct :
        pₘ ∘ₘ directγ ≡ idₘ ∘ₘ γ°
      p-direct =
        p-⟨⟩ₘ (idₘ ∘ₘ γ°) Mγ

      q-direct :
        qₘ [ directγ ]Tmₘ ≡ Mγ
      q-direct =
        q-⟨⟩ₘ (idₘ ∘ₘ γ°) Mγ

      directCtx∙ :
        GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) directγ
      directCtx∙ =
        subst (GluCtx.Γ∙ Γ) (sym p-direct)
          (subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙)
        ,
        subst (GluTy.A∙ A) (sym q-direct) Mγ∙

      pairCtx∙ :
        GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) pairγ
      pairCtx∙ =
        transport
          (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (pairγ≡directγ (~ i)))
          directCtx∙

      pairCtx∙-filler :
        PathP
          (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (pairγ≡directγ (~ i)))
          directCtx∙
          pairCtx∙
      pairCtx∙-filler =
        transport-filler
          (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (pairγ≡directγ (~ i)))
          directCtx∙

      extCtx∙-filler :
        PathP
          (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (directγ≡extγ i))
          directCtx∙
          (extend-fiber {Γ = Γ} A γ° γ∙ Mγ Mγ∙)
      extCtx∙-filler =
        transport-filler
          (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (directγ≡extγ i))
          directCtx∙

      target-step₁ :
        PathP
          (λ i → C (target-comp i))
          target∙
          (GluTm.M∙ N pairγ pairCtx∙)
      target-step₁ =
        toPathP
          (transportTransport⁻
            (cong C target-comp)
            (GluTm.M∙ N pairγ pairCtx∙))

      target-step₂a :
        PathP
          (λ i → C (N₀ [ pairγ≡directγ i ]Tmₘ))
          (GluTm.M∙ N pairγ pairCtx∙)
          (GluTm.M∙ N directγ directCtx∙)
      target-step₂a i =
        GluTm.M∙ N (pairγ≡directγ i) (pairCtx∙-filler (~ i))

      target-step₂b :
        PathP
          (λ i → C (N₀ [ directγ≡extγ i ]Tmₘ))
          (GluTm.M∙ N directγ directCtx∙)
          direct∙
      target-step₂b i =
        GluTm.M∙ N (directγ≡extγ i) (extCtx∙-filler i)

      target-step₂ :
        PathP
          (λ i → C (N₀ [ pairγ≡extγ i ]Tmₘ))
          (GluTm.M∙ N pairγ pairCtx∙)
          direct∙
      target-step₂ =
        compPathP' {B = λ δ → C (N₀ [ δ ]Tmₘ)}
          target-step₂a
          target-step₂b

      target-pathP :
        PathP
          (λ i → C (target-path i))
          target∙
          direct∙
      target-pathP =
        compPathP' {B = C}
          target-step₁
          target-step₂

      target-eq :
        target∙ ≡ subst C (sym target-path) direct∙
      target-eq =
        fromPathP⁻ target-pathP

      β-source :
        sourceTerm ≤ N₀ [ extγ ]Tmₘ
      β-source =
        subst (λ t → t ≤ N₀ [ extγ ]Tmₘ) (sym app-path) β-step

      β-target :
        sourceTerm ≤ N₀ [ extγ ]Tmₘ
      β-target =
        subst (λ t → sourceTerm ≤ t) target-path βγ

      β-source≡target :
        β-source ≡ β-target
      β-source≡target =
        tm-thinₘ εₘ (GluTy.A° B)
          sourceTerm
          (N₀ [ extγ ]Tmₘ)
          β-source
          β-target

      β-step≡source-push :
        β-step ≡ subst (λ t → t ≤ N₀ [ extγ ]Tmₘ) app-path β-source
      β-step≡source-push =
        tm-thinₘ εₘ (GluTy.A° B)
          (appₘ (lamₘ N₀ [ γ° ]Tmₘ) Mγ)
          (N₀ [ extγ ]Tmₘ)
          β-step
          (subst (λ t → t ≤ N₀ [ extγ ]Tmₘ) app-path β-source)

      source-eq :
        GluTm.M∙ (APP {A = A} {B = B} (LAM {A = A} {B = B} N) M) γ° γ∙
        ≡ contrav-transport (GluTy.cA B) βγ target∙
      source-eq =
        cong
          (λ h →
            subst C (sym app-path)
              (contrav-transport (GluTy.cA B) h direct∙))
          β-step≡source-push
        ∙ contravariant-transport-source-subst
            (GluTy.cA B)
            (sym app-path)
            β-source
            direct∙
        ∙ cong
            (λ h → contrav-transport (GluTy.cA B) h direct∙)
            β-source≡target
        ∙ sym
            (contravariant-transport-target-subst
              (GluTy.cA B)
              (sym target-path)
              βγ
              direct∙)
        ∙ cong
            (contrav-transport (GluTy.cA B) βγ)
            (sym target-eq)

  FUN-preserves-β :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (N : GluTm 𝓜 (_▷ᵍ_ 𝓜 Γ A) B)
    (M : GluTm 𝓜 Γ A)
    → APP {A = A} {B = B} (LAM {A = A} {B = B} N) M
      ≤ _[_]Tmᵍ 𝓜 N (⟨_,_⟩ᵍ 𝓜 (idᵍ 𝓜 Γ) M)
  FUN-preserves-β {A = A} {B = B} N M =
    ≤ᵍ→≤ 𝓜 (FUN-preserves-β-data {A = A} {B = B} N M)

  FUNη-body :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (F : GluTm 𝓜 Γ (FUN A B))
    → GluTm 𝓜 (_▷ᵍ_ 𝓜 Γ A) B
  FUNη-body {Γ = Γ} {A = A} {B = B} F =
    APP {A = A} {B = B}
      (_[_]Tmᵍ 𝓜 F (pᵍ 𝓜 {Γ = Γ} {A = A}))
      (qᵍ 𝓜 {Γ = Γ} {A = A})

  private
    FUN-preserves-η-data :
      {Γ : GluCtx 𝓜}
      {A B : GluTy 𝓜}
      (F : GluTm 𝓜 Γ (FUN A B))
      → _≤ᵍ_ 𝓜 {Γ = Γ} {A = FUN A B}
          (LAM {A = A} {B = B}
            (APP {A = A} {B = B}
              (_[_]Tmᵍ 𝓜 F (pᵍ 𝓜 {Γ = Γ} {A = A}))
              (qᵍ 𝓜 {Γ = Γ} {A = A})))
          F
    _≤ᵍ_.r° (FUN-preserves-η-data F) =
      η⇒ₘ (GluTm.M° F)
    _≤ᵍ_.r∙ (FUN-preserves-η-data {Γ = Γ} {A = A} {B = B} F) γ° γ∙ =
      HomPΠ
        {P =
          λ Fγ Mγ →
            (Mγ∙ : GluTy.A∙ A Mγ)
            → GluTy.A∙ B (appₘ Fγ Mγ)}
        {h = ηγ}
        λ Mγ →
          HomPΠ
            {P =
              λ Fγ Mγ∙ →
                GluTy.A∙ B (appₘ Fγ Mγ)}
            {h = ηγ}
            λ Mγ∙ →
              contravariant-universal-from
                (contravariant-reindex
                  (λ Fγ → appₘ Fγ Mγ)
                  (GluTy.cA B))
                (pointwise-eq Mγ Mγ∙)
      where
      ηγ =
        hom-map (λ t → t [ γ° ]Tmₘ) (η⇒ₘ (GluTm.M° F))

      pointwise-eq :
        (Mγ : Tmₘ εₘ (GluTy.A° A))
        (Mγ∙ : GluTy.A∙ A Mγ)
        → GluTm.M∙ (LAM {A = A} {B = B} (FUNη-body {A = A} {B = B} F)) γ° γ∙ Mγ Mγ∙
          ≡ contrav-transport
              (contravariant-reindex
                (λ Fγ → appₘ Fγ Mγ)
                (GluTy.cA B))
              ηγ
              (GluTm.M∙ F γ° γ∙ Mγ Mγ∙)
      pointwise-eq Mγ Mγ∙ =
        cong
          (λ v → contrav-transport (GluTy.cA B) β-step v)
          contractum-eq
        ∙ contravariant-transport-target-subst
            (GluTy.cA B)
            target-path
            β-step
            target∙
        ∙ cong
            (λ h → contrav-transport (GluTy.cA B) h target∙)
            β-step≡η-step
        where
        C = GluTy.A∙ B
        F₀ = GluTm.M° F
        body = FUNη-body {Γ = Γ} {A = A} {B = B} F
        body₀ = GluTm.M° body

        extγ =
          ⟨ γ° , Mγ ⟩ₘ

        targetTerm =
          appₘ (F₀ [ γ° ]Tmₘ) Mγ

        contractumTerm =
          body₀ [ extγ ]Tmₘ

        p-ext :
          pₘ ∘ₘ extγ ≡ γ°
        p-ext =
          p-⟨⟩ₘ γ° Mγ

        q-ext :
          qₘ [ extγ ]Tmₘ ≡ Mγ
        q-ext =
          q-⟨⟩ₘ γ° Mγ

        fun-ext-path :
          (F₀ [ pₘ ]Tmₘ) [ extγ ]Tmₘ ≡ F₀ [ γ° ]Tmₘ
        fun-ext-path =
          Tm-∘ₘ F₀ pₘ extγ
          ∙ cong (λ ρ → F₀ [ ρ ]Tmₘ) p-ext

        body-app-path :
          contractumTerm
          ≡ appₘ ((F₀ [ pₘ ]Tmₘ) [ extγ ]Tmₘ) (qₘ [ extγ ]Tmₘ)
        body-app-path =
          app[]ₘ (F₀ [ pₘ ]Tmₘ) qₘ extγ

        target-to-app-path :
          targetTerm
          ≡ appₘ ((F₀ [ pₘ ]Tmₘ) [ extγ ]Tmₘ) (qₘ [ extγ ]Tmₘ)
        target-to-app-path =
          cong₂ appₘ (sym fun-ext-path) (sym q-ext)

        target-path :
          targetTerm ≡ contractumTerm
        target-path =
          target-to-app-path
          ∙ sym body-app-path

        β-step :
          appₘ (lamₘ body₀ [ γ° ]Tmₘ) Mγ
          ≤ contractumTerm
        β-step =
          β⇒-substₘ body₀ γ° Mγ

        η-step :
          appₘ (lamₘ body₀ [ γ° ]Tmₘ) Mγ
          ≤ targetTerm
        η-step =
          hom-map (λ Fγ → appₘ Fγ Mγ) ηγ

        β-step-to-target :
          appₘ (lamₘ body₀ [ γ° ]Tmₘ) Mγ
          ≤ targetTerm
        β-step-to-target =
          subst
            (λ t → appₘ (lamₘ body₀ [ γ° ]Tmₘ) Mγ ≤ t)
            (sym target-path)
            β-step

        β-step≡η-step :
          β-step-to-target ≡ η-step
        β-step≡η-step =
          tm-thinₘ εₘ (GluTy.A° B)
            (appₘ (lamₘ body₀ [ γ° ]Tmₘ) Mγ)
            targetTerm
            β-step-to-target
            η-step

        target∙ :
          C targetTerm
        target∙ =
          GluTm.M∙ F γ° γ∙ Mγ Mγ∙

        contractum∙ :
          C contractumTerm
        contractum∙ =
          lam-contractum∙ {Γ = Γ} {A = A} body γ° γ∙ Mγ Mγ∙

        directγ =
          ⟨ idₘ ∘ₘ γ° , Mγ ⟩ₘ

        directγ≡extγ :
          directγ ≡ extγ
        directγ≡extγ i =
          ⟨ id-leftₘ γ° i , Mγ ⟩ₘ

        p-direct :
          pₘ ∘ₘ directγ ≡ idₘ ∘ₘ γ°
        p-direct =
          p-⟨⟩ₘ (idₘ ∘ₘ γ°) Mγ

        q-direct :
          qₘ [ directγ ]Tmₘ ≡ Mγ
        q-direct =
          q-⟨⟩ₘ (idₘ ∘ₘ γ°) Mγ

        directCtx∙ :
          GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) directγ
        directCtx∙ =
          subst (GluCtx.Γ∙ Γ) (sym p-direct)
            (subst (GluCtx.Γ∙ Γ) (sym (id-leftₘ γ°)) γ∙)
          ,
          subst (GluTy.A∙ A) (sym q-direct) Mγ∙

        extCtx∙ :
          GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) extγ
        extCtx∙ =
          extend-fiber {Γ = Γ} A γ° γ∙ Mγ Mγ∙

        extCtx∙-filler :
          PathP
            (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (directγ≡extγ i))
            directCtx∙
            extCtx∙
        extCtx∙-filler =
          transport-filler
            (λ i → GluCtx.Γ∙ (_▷ᵍ_ 𝓜 Γ A) (directγ≡extγ i))
            directCtx∙

        base₁ :
          γ° ≡ idₘ ∘ₘ γ°
        base₁ =
          sym (id-leftₘ γ°)

        base₂ :
          idₘ ∘ₘ γ° ≡ pₘ ∘ₘ directγ
        base₂ =
          sym p-direct

        base₃ :
          pₘ ∘ₘ directγ ≡ pₘ ∘ₘ extγ
        base₃ =
          cong (λ δ → pₘ ∘ₘ δ) directγ≡extγ

        base-path :
          γ° ≡ pₘ ∘ₘ extγ
        base-path =
          (base₁ ∙ base₂) ∙ base₃

        ctx₁ :
          PathP
            (λ i → GluCtx.Γ∙ Γ (base₁ i))
            γ∙
            (subst (GluCtx.Γ∙ Γ) base₁ γ∙)
        ctx₁ =
          subst-filler (GluCtx.Γ∙ Γ) base₁ γ∙

        ctx₂ :
          PathP
            (λ i → GluCtx.Γ∙ Γ (base₂ i))
            (subst (GluCtx.Γ∙ Γ) base₁ γ∙)
            (fst directCtx∙)
        ctx₂ =
          subst-filler
            (GluCtx.Γ∙ Γ)
            base₂
            (subst (GluCtx.Γ∙ Γ) base₁ γ∙)

        ctx₁₂ :
          PathP
            (λ i → GluCtx.Γ∙ Γ ((base₁ ∙ base₂) i))
            γ∙
            (fst directCtx∙)
        ctx₁₂ =
          compPathP' {B = GluCtx.Γ∙ Γ} ctx₁ ctx₂

        ctx₃ :
          PathP
            (λ i → GluCtx.Γ∙ Γ (base₃ i))
            (fst directCtx∙)
            (fst extCtx∙)
        ctx₃ i =
          fst (extCtx∙-filler i)

        ctx-path :
          PathP
            (λ i → GluCtx.Γ∙ Γ (base-path i))
            γ∙
            (fst extCtx∙)
        ctx-path =
          compPathP' {B = GluCtx.Γ∙ Γ} ctx₁₂ ctx₃

        arg₁ :
          Mγ ≡ qₘ [ directγ ]Tmₘ
        arg₁ =
          sym q-direct

        arg₂ :
          qₘ [ directγ ]Tmₘ ≡ qₘ [ extγ ]Tmₘ
        arg₂ =
          cong (λ δ → qₘ [ δ ]Tmₘ) directγ≡extγ

        arg-path :
          Mγ ≡ qₘ [ extγ ]Tmₘ
        arg-path =
          arg₁ ∙ arg₂

        arg₁∙ :
          PathP
            (λ i → GluTy.A∙ A (arg₁ i))
            Mγ∙
            (snd directCtx∙)
        arg₁∙ =
          subst-filler (GluTy.A∙ A) arg₁ Mγ∙

        arg₂∙ :
          PathP
            (λ i → GluTy.A∙ A (arg₂ i))
            (snd directCtx∙)
            (snd extCtx∙)
        arg₂∙ i =
          snd (extCtx∙-filler i)

        arg-path∙ :
          PathP
            (λ i → GluTy.A∙ A (arg-path i))
            Mγ∙
            (snd extCtx∙)
        arg-path∙ =
          compPathP' {B = GluTy.A∙ A} arg₁∙ arg₂∙

        F-arg-path :
          targetTerm ≡ appₘ (F₀ [ pₘ ∘ₘ extγ ]Tmₘ) (qₘ [ extγ ]Tmₘ)
        F-arg-path i =
          appₘ (F₀ [ base-path i ]Tmₘ) (arg-path i)

        F-display-pathP :
          PathP
            (λ i → C (F-arg-path i))
            target∙
            (GluTm.M∙ F (pₘ ∘ₘ extγ) (fst extCtx∙)
              (qₘ [ extγ ]Tmₘ) (snd extCtx∙))
        F-display-pathP i =
          GluTm.M∙ F
            (base-path i)
            (ctx-path i)
            (arg-path i)
            (arg-path∙ i)

        fun-subst-path :
          appₘ (F₀ [ pₘ ∘ₘ extγ ]Tmₘ) (qₘ [ extγ ]Tmₘ)
          ≡ appₘ ((F₀ [ pₘ ]Tmₘ) [ extγ ]Tmₘ) (qₘ [ extγ ]Tmₘ)
        fun-subst-path =
          cong (λ Fext → appₘ Fext (qₘ [ extγ ]Tmₘ))
            (sym (Tm-∘ₘ F₀ pₘ extγ))

        appDisplay∙ :
          C (appₘ ((F₀ [ pₘ ]Tmₘ) [ extγ ]Tmₘ) (qₘ [ extγ ]Tmₘ))
        appDisplay∙ =
          GluTm.M∙ (_[_]Tmᵍ 𝓜 F (pᵍ 𝓜 {Γ = Γ} {A = A}))
            extγ extCtx∙
            (qₘ [ extγ ]Tmₘ)
            (snd extCtx∙)

        fun-subst-pathP :
          PathP
            (λ i → C (fun-subst-path i))
            (GluTm.M∙ F (pₘ ∘ₘ extγ) (fst extCtx∙)
              (qₘ [ extγ ]Tmₘ) (snd extCtx∙))
            appDisplay∙
        fun-subst-pathP =
          toPathP
            (sym
              (FUN∙-subst A B
                (sym (Tm-∘ₘ F₀ pₘ extγ))
                (GluTm.M∙ F (pₘ ∘ₘ extγ) (fst extCtx∙))
                (qₘ [ extγ ]Tmₘ)
                (snd extCtx∙)))

        body-app-pathP :
          PathP
            (λ i → C (sym body-app-path i))
            appDisplay∙
            contractum∙
        body-app-pathP =
          toPathP refl

        actual-target-path :
          targetTerm ≡ contractumTerm
        actual-target-path =
          (F-arg-path ∙ fun-subst-path) ∙ sym body-app-path

        actual-target-pathP :
          PathP
            (λ i → C (actual-target-path i))
            target∙
            contractum∙
        actual-target-pathP =
          compPathP' {B = C}
            (compPathP' {B = C} F-display-pathP fun-subst-pathP)
            body-app-pathP

        target-path-square :
          actual-target-path ≡ target-path
        target-path-square =
          tm-setₘ εₘ (GluTy.A° B)
            targetTerm
            contractumTerm
            actual-target-path
            target-path

        target-pathP :
          PathP
            (λ i → C (target-path i))
            target∙
            contractum∙
        target-pathP =
          subst
            (λ p → PathP (λ i → C (p i)) target∙ contractum∙)
            target-path-square
            actual-target-pathP

        contractum-eq :
          contractum∙ ≡ subst C target-path target∙
        contractum-eq =
          sym (fromPathP target-pathP)

  FUN-preserves-η :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (F : GluTm 𝓜 Γ (FUN A B))
    → LAM {A = A} {B = B}
        (APP {A = A} {B = B}
          (_[_]Tmᵍ 𝓜 F (pᵍ 𝓜 {Γ = Γ} {A = A}))
          (qᵍ 𝓜 {Γ = Γ} {A = A}))
      ≤ F
  FUN-preserves-η {A = A} {B = B} F =
    ≤ᵍ→≤ 𝓜 (FUN-preserves-η-data {A = A} {B = B} F)
