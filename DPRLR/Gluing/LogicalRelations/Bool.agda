module DPRLR.Gluing.LogicalRelations.Bool where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base renaming (Bool to Bool₂ ; true to true₂ ; false to false₂)
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Contravariant
open import DPRLR.Simplicial.Discrete
open import DPRLR.Object.Model.Model using (SimpleDirectedCwF)

module _ {ℓS ℓM : Level} (𝓜 : SimpleDirectedCwF ℓS ℓM) where
  open import DPRLR.Gluing.LogicalRelations.Judgment 𝓜
  open import DPRLR.Gluing.LogicalRelations.Substitution 𝓜

  open SimpleDirectedCwF 𝓜
    renaming
      ( Sub to Subₘ
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
      ; _[_]Tm to _[_]Tmₘ
      ; tm-segal to tm-segalₘ
      ; tm-thin to tm-thinₘ
      )

  ⌜_⌝ : Bool₂ → Tmₘ εₘ Boolₘ
  ⌜ true₂ ⌝ = trueₘ
  ⌜ false₂ ⌝ = falseₘ

  BOOL∙ : Tmₘ εₘ Boolₘ → Type ℓM
  BOOL∙ M =
    Σ Bool₂ (λ b → M ≤ ⌜ b ⌝)

  BOOL-contravariant :
    isContravariant BOOL∙
  BOOL-contravariant =
    contravariant-Σ-discrete Bool₂-isDiscrete λ b →
      representable-isContravariant (tm-segalₘ εₘ Boolₘ) ⌜ b ⌝

  BOOL : GluTy
  GluTy.A° BOOL = Boolₘ
  GluTy.A∙ BOOL = BOOL∙
  GluTy.cA BOOL = BOOL-contravariant

  TRUE∙ :
    {Γ : GluCtx}
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    (γ∙ : GluCtx.Γ∙ Γ γ°)
    → BOOL∙ (trueₘ [ γ° ]Tmₘ)
  TRUE∙ γ° _ =
    true₂ , path→hom (true[]ₘ γ°)

  FALSE∙ :
    {Γ : GluCtx}
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    (γ∙ : GluCtx.Γ∙ Γ γ°)
    → BOOL∙ (falseₘ [ γ° ]Tmₘ)
  FALSE∙ γ° _ =
    false₂ , path→hom (false[]ₘ γ°)

  TRUE :
    {Γ : GluCtx}
    → GluTm Γ BOOL
  GluTm.M° TRUE = trueₘ
  GluTm.M∙ TRUE = TRUE∙

  FALSE :
    {Γ : GluCtx}
    → GluTm Γ BOOL
  GluTm.M° FALSE = falseₘ
  GluTm.M∙ FALSE = FALSE∙

  TRUE₀ FALSE₀ : GluTm₀ BOOL
  TRUE₀ = trueₘ , true₂ , hom-refl trueₘ
  FALSE₀ = falseₘ , false₂ , hom-refl falseₘ

  TRUE[]₀ : {Γ : GluCtx} (γ : GluSub₀ Γ) → TRUE [ γ ]Tm₀ ≡ TRUE₀
  TRUE[]₀ (γ , γ∙) = ΣPathP (true[]ₘ γ , λ i → true₂ , arrow i)
    where
    arrow : PathP (λ i → true[]ₘ γ i ≤ trueₘ)
      (path→hom (true[]ₘ γ)) (hom-refl trueₘ)
    arrow = isProp→PathP (λ i → tm-thinₘ εₘ Boolₘ (true[]ₘ γ i) trueₘ)
      (path→hom (true[]ₘ γ)) (hom-refl trueₘ)

  FALSE[]₀ : {Γ : GluCtx} (γ : GluSub₀ Γ) → FALSE [ γ ]Tm₀ ≡ FALSE₀
  FALSE[]₀ (γ , γ∙) = ΣPathP (false[]ₘ γ , λ i → false₂ , arrow i)
    where
    arrow : PathP (λ i → false[]ₘ γ i ≤ falseₘ)
      (path→hom (false[]ₘ γ)) (hom-refl falseₘ)
    arrow = isProp→PathP (λ i → tm-thinₘ εₘ Boolₘ (false[]ₘ γ i) falseₘ)
      (path→hom (false[]ₘ γ)) (hom-refl falseₘ)

  TRUE[] : {Γ Δ : GluCtx} (σ : GluSub Γ Δ)
    → (TRUE {Γ = Δ}) [ σ ]Tmᵍ ≡ TRUE {Γ = Γ}
  TRUE[] σ = GluTm-ext (true[]ₘ (GluSub.σ° σ)) λ γ →
      (TRUE [ σ ]Tmᵍ) [ γ ]Tm₀
    ≡⟨ Tm-∘₀ TRUE σ γ ⟩
      TRUE [ σ ∘₀ γ ]Tm₀
    ≡⟨ TRUE[]₀ (σ ∘₀ γ) ⟩
      TRUE₀
    ≡⟨ sym (TRUE[]₀ γ) ⟩
      TRUE [ γ ]Tm₀
    ∎

  FALSE[] : {Γ Δ : GluCtx} (σ : GluSub Γ Δ)
    → (FALSE {Γ = Δ}) [ σ ]Tmᵍ ≡ FALSE {Γ = Γ}
  FALSE[] σ = GluTm-ext (false[]ₘ (GluSub.σ° σ)) λ γ →
      (FALSE [ σ ]Tmᵍ) [ γ ]Tm₀
    ≡⟨ Tm-∘₀ FALSE σ γ ⟩
      FALSE [ σ ∘₀ γ ]Tm₀
    ≡⟨ FALSE[]₀ (σ ∘₀ γ) ⟩
      FALSE₀
    ≡⟨ sym (FALSE[]₀ γ) ⟩
      FALSE [ γ ]Tm₀
    ∎

  βIF-TRUE[] :
    {Γ : GluCtx}
    {A : GluTy}
    (B : GluTm Γ BOOL)
    (T F : GluTm Γ A)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    → GluTm.M° B [ γ° ]Tmₘ ≤ trueₘ
    → (ifₘ GluTm.M° B then GluTm.M° T else GluTm.M° F) [ γ° ]Tmₘ
      ≤ GluTm.M° T [ γ° ]Tmₘ
  βIF-TRUE[] B T F γ° B≤true =
    subst
      (λ s → s ≤ GluTm.M° T [ γ° ]Tmₘ)
      (sym (if[]ₘ (GluTm.M° B) (GluTm.M° T) (GluTm.M° F) γ°))
      (
          ifₘ GluTm.M° B [ γ° ]Tmₘ then GluTm.M° T [ γ° ]Tmₘ else GluTm.M° F [ γ° ]Tmₘ
        ≤⟨ hom-map (λ Bγ → ifₘ Bγ then GluTm.M° T [ γ° ]Tmₘ else GluTm.M° F [ γ° ]Tmₘ) B≤true ⟩
          ifₘ trueₘ then GluTm.M° T [ γ° ]Tmₘ else GluTm.M° F [ γ° ]Tmₘ
        ≤⟨ βif-trueₘ (GluTm.M° T [ γ° ]Tmₘ) (GluTm.M° F [ γ° ]Tmₘ) ⟩
          GluTm.M° T [ γ° ]Tmₘ
        ∎≤)

  βIF-FALSE[] :
    {Γ : GluCtx}
    {A : GluTy}
    (B : GluTm Γ BOOL)
    (T F : GluTm Γ A)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    → GluTm.M° B [ γ° ]Tmₘ ≤ falseₘ
    → (ifₘ GluTm.M° B then GluTm.M° T else GluTm.M° F) [ γ° ]Tmₘ
      ≤ GluTm.M° F [ γ° ]Tmₘ
  βIF-FALSE[] B T F γ° B≤false =
    subst
      (λ s → s ≤ GluTm.M° F [ γ° ]Tmₘ)
      (sym (if[]ₘ (GluTm.M° B) (GluTm.M° T) (GluTm.M° F) γ°))
      (
          ifₘ GluTm.M° B [ γ° ]Tmₘ then GluTm.M° T [ γ° ]Tmₘ else GluTm.M° F [ γ° ]Tmₘ
        ≤⟨ hom-map (λ Bγ → ifₘ Bγ then GluTm.M° T [ γ° ]Tmₘ else GluTm.M° F [ γ° ]Tmₘ) B≤false ⟩
          ifₘ falseₘ then GluTm.M° T [ γ° ]Tmₘ else GluTm.M° F [ γ° ]Tmₘ
        ≤⟨ βif-falseₘ (GluTm.M° T [ γ° ]Tmₘ) (GluTm.M° F [ γ° ]Tmₘ) ⟩
          GluTm.M° F [ γ° ]Tmₘ
        ∎≤)

  IF :
    {Γ : GluCtx}
    {A : GluTy}
    → GluTm Γ BOOL
    → GluTm Γ A
    → GluTm Γ A
    → GluTm Γ A
  GluTm.M° (IF B T F) =
    ifₘ GluTm.M° B then GluTm.M° T else GluTm.M° F
  GluTm.M∙ (IF {A = A} B T F) γ° γ∙ with GluTm.M∙ B γ° γ∙
  ... | true₂ , B≤true =
    contrav-transport
      (GluTy.cA A)
      (βIF-TRUE[] B T F γ° B≤true)
      (GluTm.M∙ T γ° γ∙)
  ... | false₂ , B≤false =
    contrav-transport
      (GluTy.cA A)
      (βIF-FALSE[] B T F γ° B≤false)
      (GluTm.M∙ F γ° γ∙)

  IF₀ : (A : GluTy)
    → GluTm₀ BOOL → GluTm₀ A → GluTm₀ A → GluTm₀ A
  IF₀ A (b , true₂ , h) (t , t∙) (f , f∙) = (ifₘ b then t else f)
    , contrav-transport (GluTy.cA A)
        (
            ifₘ b then t else f
          ≤⟨ hom-map (λ b → ifₘ b then t else f) h ⟩
            ifₘ trueₘ then t else f
          ≤⟨ βif-trueₘ t f ⟩
            t
          ∎≤) t∙
  IF₀ A (b , false₂ , h) (t , t∙) (f , f∙) = (ifₘ b then t else f)
    , contrav-transport (GluTy.cA A)
        (
            ifₘ b then t else f
          ≤⟨ hom-map (λ b → ifₘ b then t else f) h ⟩
            ifₘ falseₘ then t else f
          ≤⟨ βif-falseₘ t f ⟩
            f
          ∎≤) f∙

  IF[]₀ : {Γ : GluCtx} {A : GluTy}
    (B : GluTm Γ BOOL) (T F : GluTm Γ A) (γ : GluSub₀ Γ)
    → (IF B T F) [ γ ]Tm₀
      ≡ IF₀ A (B [ γ ]Tm₀) (T [ γ ]Tm₀) (F [ γ ]Tm₀)
  IF[]₀ {A = A} B T F (γ , γ∙) with GluTm.M∙ B γ γ∙
  ... | true₂ , h = ΣPathP (base ,
    contravariant-transport-cong (GluTy.cA A) (tm-thinₘ εₘ (GluTy.A° A))
      base refl (βIF-TRUE[] B T F γ h)
      (
          ifₘ GluTm.M° B [ γ ]Tmₘ then t else f
        ≤⟨ hom-map (λ b → ifₘ b then t else f) h ⟩
          ifₘ trueₘ then t else f
        ≤⟨ βif-trueₘ t f ⟩
          t
        ∎≤) refl)
    where
    t f : Tmₘ εₘ (GluTy.A° A)
    t = GluTm.M° T [ γ ]Tmₘ
    f = GluTm.M° F [ γ ]Tmₘ
    base : (ifₘ GluTm.M° B then GluTm.M° T else GluTm.M° F) [ γ ]Tmₘ
      ≡ (ifₘ GluTm.M° B [ γ ]Tmₘ then t else f)
    base = if[]ₘ (GluTm.M° B) (GluTm.M° T) (GluTm.M° F) γ
  ... | false₂ , h = ΣPathP (base ,
    contravariant-transport-cong (GluTy.cA A) (tm-thinₘ εₘ (GluTy.A° A))
      base refl (βIF-FALSE[] B T F γ h)
      (
          ifₘ GluTm.M° B [ γ ]Tmₘ then t else f
        ≤⟨ hom-map (λ b → ifₘ b then t else f) h ⟩
          ifₘ falseₘ then t else f
        ≤⟨ βif-falseₘ t f ⟩
          f
        ∎≤) refl)
    where
    t f : Tmₘ εₘ (GluTy.A° A)
    t = GluTm.M° T [ γ ]Tmₘ
    f = GluTm.M° F [ γ ]Tmₘ
    base : (ifₘ GluTm.M° B then GluTm.M° T else GluTm.M° F) [ γ ]Tmₘ
      ≡ (ifₘ GluTm.M° B [ γ ]Tmₘ then t else f)
    base = if[]ₘ (GluTm.M° B) (GluTm.M° T) (GluTm.M° F) γ

  IF[] : {Γ Δ : GluCtx} {A : GluTy}
    (B : GluTm Δ BOOL) (T F : GluTm Δ A) (σ : GluSub Γ Δ)
    → (IF B T F) [ σ ]Tmᵍ
      ≡ IF (B [ σ ]Tmᵍ) (T [ σ ]Tmᵍ) (F [ σ ]Tmᵍ)
  IF[] {A = A} B T F σ =
    GluTm-ext (if[]ₘ (GluTm.M° B) (GluTm.M° T) (GluTm.M° F) (GluSub.σ° σ)) λ γ →
        ((IF B T F) [ σ ]Tmᵍ) [ γ ]Tm₀
      ≡⟨ Tm-∘₀ (IF B T F) σ γ ⟩
        (IF B T F) [ σ ∘₀ γ ]Tm₀
      ≡⟨ IF[]₀ B T F (σ ∘₀ γ) ⟩
        IF₀ A (B [ σ ∘₀ γ ]Tm₀) (T [ σ ∘₀ γ ]Tm₀) (F [ σ ∘₀ γ ]Tm₀)
      ≡⟨ (λ i → IF₀ A (Tm-∘₀ B σ γ (~ i))
           (Tm-∘₀ T σ γ (~ i)) (Tm-∘₀ F σ γ (~ i))) ⟩
        IF₀ A ((B [ σ ]Tmᵍ) [ γ ]Tm₀) ((T [ σ ]Tmᵍ) [ γ ]Tm₀) ((F [ σ ]Tmᵍ) [ γ ]Tm₀)
      ≡⟨ sym (IF[]₀ (B [ σ ]Tmᵍ) (T [ σ ]Tmᵍ) (F [ σ ]Tmᵍ) γ) ⟩
        (IF (B [ σ ]Tmᵍ) (T [ σ ]Tmᵍ) (F [ σ ]Tmᵍ)) [ γ ]Tm₀
      ∎

  IF-preserves-β-true : {Γ : GluCtx} {A : GluTy}
    (T F : GluTm Γ A) → IF TRUE T F ≤ T
  IF-preserves-β-true {A = A} T F = ≤ᵍ→≤ record
    { r° = βif-trueₘ (GluTm.M° T) (GluTm.M° F)
    ; r∙ = λ γ γ∙ → contravariant-universal-from (GluTy.cA A)
        (contravariant-transport-cong (GluTy.cA A) (tm-thinₘ εₘ (GluTy.A° A))
          refl refl (βIF-TRUE[] TRUE T F γ (path→hom (true[]ₘ γ)))
          (hom-map (_[ γ ]Tmₘ) (βif-trueₘ (GluTm.M° T) (GluTm.M° F))) refl)
    }

  IF-preserves-β-false : {Γ : GluCtx} {A : GluTy}
    (T F : GluTm Γ A) → IF FALSE T F ≤ F
  IF-preserves-β-false {A = A} T F = ≤ᵍ→≤ record
    { r° = βif-falseₘ (GluTm.M° T) (GluTm.M° F)
    ; r∙ = λ γ γ∙ → contravariant-universal-from (GluTy.cA A)
        (contravariant-transport-cong (GluTy.cA A) (tm-thinₘ εₘ (GluTy.A° A))
          refl refl (βIF-FALSE[] FALSE T F γ (path→hom (false[]ₘ γ)))
          (hom-map (_[ γ ]Tmₘ) (βif-falseₘ (GluTm.M° T) (GluTm.M° F))) refl)
    }
