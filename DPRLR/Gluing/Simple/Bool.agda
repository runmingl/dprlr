module DPRLR.Gluing.Simple.Bool where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import Cubical.Data.Bool.Base renaming (Bool to Bool₂ ; true to true₂ ; false to false₂)
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Contravariant
open import DPRLR.Simplicial.Discrete
open import DPRLR.Simplicial.Representable
open import DPRLR.Object.Simple.Model
open import DPRLR.Gluing.Simple.Judgment
open import DPRLR.Gluing.Simple.Substitution

module _ {ℓM : Level} (𝓜 : SimpleDirectedCwF ℓM) where

  open SimpleDirectedCwF 𝓜
    renaming
      ( Ctx to Ctxₘ
      ; Sub to Subₘ
      ; Tm to Tmₘ
      ; ε to εₘ
      ; Bool to Boolₘ
      ; true to trueₘ
      ; false to falseₘ
      ; if_then_else_ to ifₘ_then_else_
      ; true[] to true[]ₘ
      ; false[] to false[]ₘ
      ; if[] to if[]ₘ
      ; βif-true to βif-trueₘ
      ; βif-false to βif-falseₘ
      ; _∘_ to _∘ₘ_
      ; _[_]Tm to _[_]Tmₘ
      ; Tm-∘ to Tm-∘ₘ
      ; tm-set to tm-setₘ
      ; tm-segal to tm-segalₘ
      ; tm-thin to tm-thinₘ
      )

  ⌜_⌝ : Bool₂ → Tmₘ εₘ Boolₘ
  ⌜ true₂ ⌝ = trueₘ
  ⌜ false₂ ⌝ = falseₘ

  BOOL∙ : Tmₘ εₘ Boolₘ → Type ℓM
  BOOL∙ M =
    Σ Bool₂ (λ b → M ≤ ⌜ b ⌝)

  BOOL-contravariance :
    isContravariant BOOL∙
  BOOL-contravariance =
    contravariant-Σ-discrete Bool₂-isDiscrete λ b →
      representable-isContravariant (tm-segalₘ εₘ Boolₘ) ⌜ b ⌝

  BOOL : GluTy 𝓜
  GluTy.A° BOOL = Boolₘ
  GluTy.A∙ BOOL = BOOL∙
  GluTy.cA BOOL = BOOL-contravariance

  TRUE-fiber :
    {Γ : GluCtx 𝓜}
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    (γ∙ : GluCtx.Γ∙ Γ γ°)
    → BOOL∙ (trueₘ [ γ° ]Tmₘ)
  TRUE-fiber γ° _ =
    true₂ , path→hom (true[]ₘ γ°)

  FALSE-fiber :
    {Γ : GluCtx 𝓜}
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    (γ∙ : GluCtx.Γ∙ Γ γ°)
    → BOOL∙ (falseₘ [ γ° ]Tmₘ)
  FALSE-fiber γ° _ =
    false₂ , path→hom (false[]ₘ γ°)

  TRUE :
    {Γ : GluCtx 𝓜}
    → GluTm 𝓜 Γ BOOL
  GluTm.M° TRUE = trueₘ
  GluTm.M∙ TRUE = TRUE-fiber

  FALSE :
    {Γ : GluCtx 𝓜}
    → GluTm 𝓜 Γ BOOL
  GluTm.M° FALSE = falseₘ
  GluTm.M∙ FALSE = FALSE-fiber

  TRUE[] :
    {Γ Δ : GluCtx 𝓜}
    (σ : GluSub 𝓜 Γ Δ)
    → _[_]Tmᵍ 𝓜 (TRUE {Γ = Δ}) σ ≡ TRUE {Γ = Γ}
  GluTm.M° (TRUE[] σ i) =
    true[]ₘ (GluSub.σ° σ) i
  GluTm.M∙ (TRUE[] {Γ = Γ} {Δ = Δ} σ i) γ° γ∙ =
    path i
    where
    actual :
      BOOL∙ ((trueₘ [ GluSub.σ° σ ]Tmₘ) [ γ° ]Tmₘ)
    actual =
      subst BOOL∙
        (sym (Tm-∘ₘ trueₘ (GluSub.σ° σ) γ°))
        (TRUE-fiber {Γ = Δ} (GluSub.σ° σ ∘ₘ γ°)
          (GluSub.σ∙ σ γ° γ∙))

    middle :
      BOOL∙ (trueₘ [ GluSub.σ° σ ∘ₘ γ° ]Tmₘ)
    middle =
      TRUE-fiber {Γ = Δ} (GluSub.σ° σ ∘ₘ γ°)
        (GluSub.σ∙ σ γ° γ∙)

    target :
      BOOL∙ (trueₘ [ γ° ]Tmₘ)
    target =
      TRUE-fiber {Γ = Γ} γ° γ∙

    P :
      (trueₘ [ GluSub.σ° σ ]Tmₘ) [ γ° ]Tmₘ
      ≡ trueₘ [ γ° ]Tmₘ
    P i = true[]ₘ (GluSub.σ° σ) i [ γ° ]Tmₘ

    R :
      trueₘ [ GluSub.σ° σ ∘ₘ γ° ]Tmₘ
      ≡ trueₘ [ γ° ]Tmₘ
    R =
      true[]ₘ (GluSub.σ° σ ∘ₘ γ°)
      ∙ sym (true[]ₘ γ°)

    Q :
      (trueₘ [ GluSub.σ° σ ]Tmₘ) [ γ° ]Tmₘ
      ≡ trueₘ [ γ° ]Tmₘ
    Q =
      Tm-∘ₘ trueₘ (GluSub.σ° σ) γ° ∙ R

    Q≡P :
      Q ≡ P
    Q≡P =
      tm-setₘ εₘ Boolₘ
        ((trueₘ [ GluSub.σ° σ ]Tmₘ) [ γ° ]Tmₘ)
        (trueₘ [ γ° ]Tmₘ)
        Q
        P

    step₁ :
      PathP
        (λ i → BOOL∙ (Tm-∘ₘ trueₘ (GluSub.σ° σ) γ° i))
        actual
        middle
    step₁ i =
      subst-filler
        BOOL∙
        (sym (Tm-∘ₘ trueₘ (GluSub.σ° σ) γ°))
        middle
        (~ i)

    step₂ :
      PathP
        (λ i → BOOL∙ (R i))
        middle
        target
    step₂ =
      ΣPathP
        ( refl
        , isProp→PathP
            (λ i → tm-thinₘ εₘ Boolₘ (R i) trueₘ)
            (snd middle)
            (snd target)
        )

    path-Q :
      PathP
        (λ i → BOOL∙ (Q i))
        actual
        target
    path-Q =
      compPathP' {B = BOOL∙} step₁ step₂

    path :
      PathP
        (λ i → BOOL∙ (P i))
        actual
        target
    path =
      subst
        (λ q →
          PathP
            (λ i → BOOL∙ (q i))
            actual
            target)
        Q≡P
        path-Q

  FALSE[] :
    {Γ Δ : GluCtx 𝓜}
    (σ : GluSub 𝓜 Γ Δ)
    → _[_]Tmᵍ 𝓜 (FALSE {Γ = Δ}) σ ≡ FALSE {Γ = Γ}
  GluTm.M° (FALSE[] σ i) =
    false[]ₘ (GluSub.σ° σ) i
  GluTm.M∙ (FALSE[] {Γ = Γ} {Δ = Δ} σ i) γ° γ∙ =
    path i
    where
    actual :
      BOOL∙ ((falseₘ [ GluSub.σ° σ ]Tmₘ) [ γ° ]Tmₘ)
    actual =
      subst BOOL∙
        (sym (Tm-∘ₘ falseₘ (GluSub.σ° σ) γ°))
        (FALSE-fiber {Γ = Δ} (GluSub.σ° σ ∘ₘ γ°)
          (GluSub.σ∙ σ γ° γ∙))

    middle :
      BOOL∙ (falseₘ [ GluSub.σ° σ ∘ₘ γ° ]Tmₘ)
    middle =
      FALSE-fiber {Γ = Δ} (GluSub.σ° σ ∘ₘ γ°)
        (GluSub.σ∙ σ γ° γ∙)

    target :
      BOOL∙ (falseₘ [ γ° ]Tmₘ)
    target =
      FALSE-fiber {Γ = Γ} γ° γ∙

    P :
      (falseₘ [ GluSub.σ° σ ]Tmₘ) [ γ° ]Tmₘ
      ≡ falseₘ [ γ° ]Tmₘ
    P i = false[]ₘ (GluSub.σ° σ) i [ γ° ]Tmₘ

    R :
      falseₘ [ GluSub.σ° σ ∘ₘ γ° ]Tmₘ
      ≡ falseₘ [ γ° ]Tmₘ
    R =
      false[]ₘ (GluSub.σ° σ ∘ₘ γ°)
      ∙ sym (false[]ₘ γ°)

    Q :
      (falseₘ [ GluSub.σ° σ ]Tmₘ) [ γ° ]Tmₘ
      ≡ falseₘ [ γ° ]Tmₘ
    Q =
      Tm-∘ₘ falseₘ (GluSub.σ° σ) γ° ∙ R

    Q≡P :
      Q ≡ P
    Q≡P =
      tm-setₘ εₘ Boolₘ
        ((falseₘ [ GluSub.σ° σ ]Tmₘ) [ γ° ]Tmₘ)
        (falseₘ [ γ° ]Tmₘ)
        Q
        P

    step₁ :
      PathP
        (λ i → BOOL∙ (Tm-∘ₘ falseₘ (GluSub.σ° σ) γ° i))
        actual
        middle
    step₁ i =
      subst-filler
        BOOL∙
        (sym (Tm-∘ₘ falseₘ (GluSub.σ° σ) γ°))
        middle
        (~ i)

    step₂ :
      PathP
        (λ i → BOOL∙ (R i))
        middle
        target
    step₂ =
      ΣPathP
        ( refl
        , isProp→PathP
            (λ i → tm-thinₘ εₘ Boolₘ (R i) falseₘ)
            (snd middle)
            (snd target)
        )

    path-Q :
      PathP
        (λ i → BOOL∙ (Q i))
        actual
        target
    path-Q =
      compPathP' {B = BOOL∙} step₁ step₂

    path :
      PathP
        (λ i → BOOL∙ (P i))
        actual
        target
    path =
      subst
        (λ q →
          PathP
            (λ i → BOOL∙ (q i))
            actual
            target)
        Q≡P
        path-Q

  if-true-hom :
    {Γ : GluCtx 𝓜}
    {A : GluTy 𝓜}
    (B : GluTm 𝓜 Γ BOOL)
    (T F : GluTm 𝓜 Γ A)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    → GluTm.M° B [ γ° ]Tmₘ ≤ trueₘ
    → (ifₘ GluTm.M° B then GluTm.M° T else GluTm.M° F) [ γ° ]Tmₘ
      ≤ GluTm.M° T [ γ° ]Tmₘ
  if-true-hom B T F γ° B≤true =
    subst
      (λ s → s ≤ GluTm.M° T [ γ° ]Tmₘ)
      (sym (if[]ₘ (GluTm.M° B) (GluTm.M° T) (GluTm.M° F) γ°))
      (tm-∙ 𝓜
        (hom-map (λ Bγ → ifₘ Bγ then GluTm.M° T [ γ° ]Tmₘ else GluTm.M° F [ γ° ]Tmₘ) B≤true)
        (βif-trueₘ (GluTm.M° T [ γ° ]Tmₘ) (GluTm.M° F [ γ° ]Tmₘ)))

  if-false-hom :
    {Γ : GluCtx 𝓜}
    {A : GluTy 𝓜}
    (B : GluTm 𝓜 Γ BOOL)
    (T F : GluTm 𝓜 Γ A)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    → GluTm.M° B [ γ° ]Tmₘ ≤ falseₘ
    → (ifₘ GluTm.M° B then GluTm.M° T else GluTm.M° F) [ γ° ]Tmₘ
      ≤ GluTm.M° F [ γ° ]Tmₘ
  if-false-hom B T F γ° B≤false =
    subst
      (λ s → s ≤ GluTm.M° F [ γ° ]Tmₘ)
      (sym (if[]ₘ (GluTm.M° B) (GluTm.M° T) (GluTm.M° F) γ°))
      (tm-∙ 𝓜
        (hom-map (λ Bγ → ifₘ Bγ then GluTm.M° T [ γ° ]Tmₘ else GluTm.M° F [ γ° ]Tmₘ) B≤false)
        (βif-falseₘ (GluTm.M° T [ γ° ]Tmₘ) (GluTm.M° F [ γ° ]Tmₘ)))

  IF :
    {Γ : GluCtx 𝓜}
    {A : GluTy 𝓜}
    → GluTm 𝓜 Γ BOOL
    → GluTm 𝓜 Γ A
    → GluTm 𝓜 Γ A
    → GluTm 𝓜 Γ A
  GluTm.M° (IF B T F) =
    ifₘ GluTm.M° B then GluTm.M° T else GluTm.M° F
  GluTm.M∙ (IF {A = A} B T F) γ° γ∙ with GluTm.M∙ B γ° γ∙
  ... | true₂ , B≤true =
    contrav-transport
      (GluTy.cA A)
      (if-true-hom B T F γ° B≤true)
      (GluTm.M∙ T γ° γ∙)
  ... | false₂ , B≤false =
    contrav-transport
      (GluTy.cA A)
      (if-false-hom B T F γ° B≤false)
      (GluTm.M∙ F γ° γ∙)

  IF[] :
    {Γ Δ : GluCtx 𝓜}
    {A : GluTy 𝓜}
    (B : GluTm 𝓜 Δ BOOL)
    (T F : GluTm 𝓜 Δ A)
    (σ : GluSub 𝓜 Γ Δ)
    → _[_]Tmᵍ 𝓜 (IF {A = A} B T F) σ
      ≡ IF {A = A}
          (_[_]Tmᵍ 𝓜 B σ)
          (_[_]Tmᵍ 𝓜 T σ)
          (_[_]Tmᵍ 𝓜 F σ)
  GluTm.M° (IF[] B T F σ i) =
    if[]ₘ (GluTm.M° B) (GluTm.M° T) (GluTm.M° F) (GluSub.σ° σ) i
  GluTm.M∙ (IF[] {Γ = Γ} {Δ = Δ} {A = A} B T F σ i) γ° γ∙
    with GluTm.M∙ B (GluSub.σ° σ ∘ₘ γ°) (GluSub.σ∙ σ γ° γ∙)
  ... | true₂ , B≤true =
    path i
    where
    C = GluTy.A∙ A
    B₀ = GluTm.M° B
    T₀ = GluTm.M° T
    F₀ = GluTm.M° F
    σ₀ = GluSub.σ° σ

    σγ =
      σ₀ ∘ₘ γ°

    T∙σγ =
      GluTm.M∙ T σγ (GluSub.σ∙ σ γ° γ∙)

    compIf :
      ((ifₘ B₀ then T₀ else F₀) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ (ifₘ B₀ then T₀ else F₀) [ σγ ]Tmₘ
    compIf =
      Tm-∘ₘ (ifₘ B₀ then T₀ else F₀) σ₀ γ°

    ifσγ :
      (ifₘ B₀ then T₀ else F₀) [ σγ ]Tmₘ
      ≡ ifₘ B₀ [ σγ ]Tmₘ then T₀ [ σγ ]Tmₘ else F₀ [ σγ ]Tmₘ
    ifσγ =
      if[]ₘ B₀ T₀ F₀ σγ

    compB :
      (B₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ B₀ [ σγ ]Tmₘ
    compB =
      Tm-∘ₘ B₀ σ₀ γ°

    compT :
      (T₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ T₀ [ σγ ]Tmₘ
    compT =
      Tm-∘ₘ T₀ σ₀ γ°

    compF :
      (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ F₀ [ σγ ]Tmₘ
    compF =
      Tm-∘ₘ F₀ σ₀ γ°

    B-path :
      B₀ [ σγ ]Tmₘ ≡ (B₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    B-path =
      sym compB

    T-path :
      T₀ [ σγ ]Tmₘ ≡ (T₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    T-path =
      sym compT

    F-path :
      F₀ [ σγ ]Tmₘ ≡ (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    F-path =
      sym compF

    if-components :
      ifₘ B₀ [ σγ ]Tmₘ then T₀ [ σγ ]Tmₘ else F₀ [ σγ ]Tmₘ
      ≡ ifₘ (B₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
          then (T₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
          else (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    if-components i =
      ifₘ B-path i then T-path i else F-path i

    ifTarget :
      (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ ifₘ (B₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
          then (T₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
          else (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    ifTarget =
      if[]ₘ (B₀ [ σ₀ ]Tmₘ) (T₀ [ σ₀ ]Tmₘ) (F₀ [ σ₀ ]Tmₘ) γ°

    rest-path :
      (ifₘ B₀ then T₀ else F₀) [ σγ ]Tmₘ
      ≡ (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    rest-path =
      (ifσγ ∙ if-components) ∙ sym ifTarget

    T∙target :
      C ((T₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    T∙target =
      subst C T-path T∙σγ

    B≤true-target :
      (B₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≤ trueₘ
    B≤true-target =
      subst (λ b → b ≤ trueₘ) B-path B≤true

    source-hom :
      (ifₘ B₀ then T₀ else F₀) [ σγ ]Tmₘ
      ≤ T₀ [ σγ ]Tmₘ
    source-hom =
      if-true-hom B T F σγ B≤true

    target-hom :
      (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≤ (T₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    target-hom =
      if-true-hom
        (_[_]Tmᵍ 𝓜 B σ)
        (_[_]Tmᵍ 𝓜 T σ)
        (_[_]Tmᵍ 𝓜 F σ)
        γ°
        B≤true-target

    actual :
      C (((ifₘ B₀ then T₀ else F₀) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    actual =
      subst C (sym compIf)
        (contrav-transport (GluTy.cA A) source-hom T∙σγ)

    target :
      C ((ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    target =
      contrav-transport (GluTy.cA A) target-hom T∙target

    step₁ :
      PathP
        (λ i → C (compIf i))
        actual
        (contrav-transport (GluTy.cA A) source-hom T∙σγ)
    step₁ i =
      subst-filler
        C
        (sym compIf)
        (contrav-transport (GluTy.cA A) source-hom T∙σγ)
        (~ i)

    hom-eq :
      subst
        (λ t → (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≤ t)
        (sym T-path)
        target-hom
      ≡ subst
          (λ s → s ≤ T₀ [ σγ ]Tmₘ)
          rest-path
          source-hom
    hom-eq =
      tm-thinₘ εₘ (GluTy.A° A)
        ((ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        (T₀ [ σγ ]Tmₘ)
        (subst
          (λ t → (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≤ t)
          (sym T-path)
          target-hom)
        (subst
          (λ s → s ≤ T₀ [ σγ ]Tmₘ)
          rest-path
          source-hom)

    step₂ :
      PathP
        (λ i → C (rest-path i))
        (contrav-transport (GluTy.cA A) source-hom T∙σγ)
        target
    step₂ =
      contravariant-transport-pathP
        (GluTy.cA A)
        rest-path
        T-path
        source-hom
        target-hom
        T∙σγ
        hom-eq

    Q :
      ((ifₘ B₀ then T₀ else F₀) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    Q =
      compIf ∙ rest-path

    R :
      ((ifₘ B₀ then T₀ else F₀) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    R i =
      if[]ₘ B₀ T₀ F₀ σ₀ i [ γ° ]Tmₘ

    Q≡R :
      Q ≡ R
    Q≡R =
      tm-setₘ εₘ (GluTy.A° A)
        (((ifₘ B₀ then T₀ else F₀) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        ((ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
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
  ... | false₂ , B≤false =
    path i
    where
    C = GluTy.A∙ A
    B₀ = GluTm.M° B
    T₀ = GluTm.M° T
    F₀ = GluTm.M° F
    σ₀ = GluSub.σ° σ

    σγ =
      σ₀ ∘ₘ γ°

    F∙σγ =
      GluTm.M∙ F σγ (GluSub.σ∙ σ γ° γ∙)

    compIf :
      ((ifₘ B₀ then T₀ else F₀) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ (ifₘ B₀ then T₀ else F₀) [ σγ ]Tmₘ
    compIf =
      Tm-∘ₘ (ifₘ B₀ then T₀ else F₀) σ₀ γ°

    ifσγ :
      (ifₘ B₀ then T₀ else F₀) [ σγ ]Tmₘ
      ≡ ifₘ B₀ [ σγ ]Tmₘ then T₀ [ σγ ]Tmₘ else F₀ [ σγ ]Tmₘ
    ifσγ =
      if[]ₘ B₀ T₀ F₀ σγ

    compB :
      (B₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ B₀ [ σγ ]Tmₘ
    compB =
      Tm-∘ₘ B₀ σ₀ γ°

    compT :
      (T₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ T₀ [ σγ ]Tmₘ
    compT =
      Tm-∘ₘ T₀ σ₀ γ°

    compF :
      (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ F₀ [ σγ ]Tmₘ
    compF =
      Tm-∘ₘ F₀ σ₀ γ°

    B-path :
      B₀ [ σγ ]Tmₘ ≡ (B₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    B-path =
      sym compB

    T-path :
      T₀ [ σγ ]Tmₘ ≡ (T₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    T-path =
      sym compT

    F-path :
      F₀ [ σγ ]Tmₘ ≡ (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    F-path =
      sym compF

    if-components :
      ifₘ B₀ [ σγ ]Tmₘ then T₀ [ σγ ]Tmₘ else F₀ [ σγ ]Tmₘ
      ≡ ifₘ (B₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
          then (T₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
          else (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    if-components i =
      ifₘ B-path i then T-path i else F-path i

    ifTarget :
      (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ ifₘ (B₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
          then (T₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
          else (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    ifTarget =
      if[]ₘ (B₀ [ σ₀ ]Tmₘ) (T₀ [ σ₀ ]Tmₘ) (F₀ [ σ₀ ]Tmₘ) γ°

    rest-path :
      (ifₘ B₀ then T₀ else F₀) [ σγ ]Tmₘ
      ≡ (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    rest-path =
      (ifσγ ∙ if-components) ∙ sym ifTarget

    F∙target :
      C ((F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    F∙target =
      subst C F-path F∙σγ

    B≤false-target :
      (B₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≤ falseₘ
    B≤false-target =
      subst (λ b → b ≤ falseₘ) B-path B≤false

    source-hom :
      (ifₘ B₀ then T₀ else F₀) [ σγ ]Tmₘ
      ≤ F₀ [ σγ ]Tmₘ
    source-hom =
      if-false-hom B T F σγ B≤false

    target-hom :
      (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≤ (F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    target-hom =
      if-false-hom
        (_[_]Tmᵍ 𝓜 B σ)
        (_[_]Tmᵍ 𝓜 T σ)
        (_[_]Tmᵍ 𝓜 F σ)
        γ°
        B≤false-target

    actual :
      C (((ifₘ B₀ then T₀ else F₀) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    actual =
      subst C (sym compIf)
        (contrav-transport (GluTy.cA A) source-hom F∙σγ)

    target :
      C ((ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    target =
      contrav-transport (GluTy.cA A) target-hom F∙target

    step₁ :
      PathP
        (λ i → C (compIf i))
        actual
        (contrav-transport (GluTy.cA A) source-hom F∙σγ)
    step₁ i =
      subst-filler
        C
        (sym compIf)
        (contrav-transport (GluTy.cA A) source-hom F∙σγ)
        (~ i)

    hom-eq :
      subst
        (λ f → (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≤ f)
        (sym F-path)
        target-hom
      ≡ subst
          (λ s → s ≤ F₀ [ σγ ]Tmₘ)
          rest-path
          source-hom
    hom-eq =
      tm-thinₘ εₘ (GluTy.A° A)
        ((ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        (F₀ [ σγ ]Tmₘ)
        (subst
          (λ f → (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≤ f)
          (sym F-path)
          target-hom)
        (subst
          (λ s → s ≤ F₀ [ σγ ]Tmₘ)
          rest-path
          source-hom)

    step₂ :
      PathP
        (λ i → C (rest-path i))
        (contrav-transport (GluTy.cA A) source-hom F∙σγ)
        target
    step₂ =
      contravariant-transport-pathP
        (GluTy.cA A)
        rest-path
        F-path
        source-hom
        target-hom
        F∙σγ
        hom-eq

    Q :
      ((ifₘ B₀ then T₀ else F₀) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    Q =
      compIf ∙ rest-path

    R :
      ((ifₘ B₀ then T₀ else F₀) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ (ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    R i =
      if[]ₘ B₀ T₀ F₀ σ₀ i [ γ° ]Tmₘ

    Q≡R :
      Q ≡ R
    Q≡R =
      tm-setₘ εₘ (GluTy.A° A)
        (((ifₘ B₀ then T₀ else F₀) [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        ((ifₘ B₀ [ σ₀ ]Tmₘ then T₀ [ σ₀ ]Tmₘ else F₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
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
    IF-preserves-β-true-data :
      {Γ : GluCtx 𝓜}
      {A : GluTy 𝓜}
      (T F : GluTm 𝓜 Γ A)
      → _≤ᵍ_ 𝓜 {Γ = Γ} {A = A}
          (IF TRUE T F)
          T
    _≤ᵍ_.r° (IF-preserves-β-true-data T F) =
      βif-trueₘ (GluTm.M° T) (GluTm.M° F)
    _≤ᵍ_.r∙ (IF-preserves-β-true-data {A = A} T F) γ° γ∙ =
      contravariant-universal-from
        (GluTy.cA A)
        (cong
          (λ h → contrav-transport (GluTy.cA A) h (GluTm.M∙ T γ° γ∙))
          hom-eq)
      where
      βγ :
        (ifₘ trueₘ then GluTm.M° T else GluTm.M° F) [ γ° ]Tmₘ
        ≤ GluTm.M° T [ γ° ]Tmₘ
      βγ =
        hom-map (λ u → u [ γ° ]Tmₘ) (βif-trueₘ (GluTm.M° T) (GluTm.M° F))

      source-hom :
        (ifₘ trueₘ then GluTm.M° T else GluTm.M° F) [ γ° ]Tmₘ
        ≤ GluTm.M° T [ γ° ]Tmₘ
      source-hom =
        if-true-hom TRUE T F γ° (path→hom (true[]ₘ γ°))

      hom-eq :
        source-hom ≡ βγ
      hom-eq =
        tm-thinₘ εₘ (GluTy.A° A)
          ((ifₘ trueₘ then GluTm.M° T else GluTm.M° F) [ γ° ]Tmₘ)
          (GluTm.M° T [ γ° ]Tmₘ)
          source-hom
          βγ

    IF-preserves-β-false-data :
      {Γ : GluCtx 𝓜}
      {A : GluTy 𝓜}
      (T F : GluTm 𝓜 Γ A)
      → _≤ᵍ_ 𝓜 {Γ = Γ} {A = A}
          (IF FALSE T F)
          F
    _≤ᵍ_.r° (IF-preserves-β-false-data T F) =
      βif-falseₘ (GluTm.M° T) (GluTm.M° F)
    _≤ᵍ_.r∙ (IF-preserves-β-false-data {A = A} T F) γ° γ∙ =
      contravariant-universal-from
        (GluTy.cA A)
        (cong
          (λ h → contrav-transport (GluTy.cA A) h (GluTm.M∙ F γ° γ∙))
          hom-eq)
      where
      βγ :
        (ifₘ falseₘ then GluTm.M° T else GluTm.M° F) [ γ° ]Tmₘ
        ≤ GluTm.M° F [ γ° ]Tmₘ
      βγ =
        hom-map (λ u → u [ γ° ]Tmₘ) (βif-falseₘ (GluTm.M° T) (GluTm.M° F))

      source-hom :
        (ifₘ falseₘ then GluTm.M° T else GluTm.M° F) [ γ° ]Tmₘ
        ≤ GluTm.M° F [ γ° ]Tmₘ
      source-hom =
        if-false-hom FALSE T F γ° (path→hom (false[]ₘ γ°))

      hom-eq :
        source-hom ≡ βγ
      hom-eq =
        tm-thinₘ εₘ (GluTy.A° A)
          ((ifₘ falseₘ then GluTm.M° T else GluTm.M° F) [ γ° ]Tmₘ)
          (GluTm.M° F [ γ° ]Tmₘ)
          source-hom
          βγ

  IF-preserves-β-true :
    {Γ : GluCtx 𝓜}
    {A : GluTy 𝓜}
    (T F : GluTm 𝓜 Γ A)
    → IF TRUE T F ≤ T
  IF-preserves-β-true T F =
    ≤ᵍ→≤ 𝓜 (IF-preserves-β-true-data T F)

  IF-preserves-β-false :
    {Γ : GluCtx 𝓜}
    {A : GluTy 𝓜}
    (T F : GluTm 𝓜 Γ A)
    → IF FALSE T F ≤ F
  IF-preserves-β-false T F =
    ≤ᵍ→≤ 𝓜 (IF-preserves-β-false-data T F)
