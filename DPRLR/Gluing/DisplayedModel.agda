module DPRLR.Gluing.DisplayedModel where

open import Cubical.Foundations.Prelude
  using (Level ; Type ; ℓ-suc ; isSet ; isProp→isSet)
open import Cubical.Foundations.HLevels
  using (isSetΣ ; isSetΠ2 ; isSet×)
open import Cubical.Data.Bool.Properties using (isSetBool)
open import Cubical.Data.Sigma hiding (Sub)
open import Cubical.Data.Unit using (isSetUnit*)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Contravariant
  using
    ( isContravariant
    ; contravariant-reindex
    ; contravariant-Π
    )
open import DPRLR.Object.Simple.Model
open import DPRLR.Object.Simple.Displayed
open import DPRLR.Gluing.GluingModel
open import DPRLR.Gluing.Simple.Judgment using (_≤ᵍ_ ; r° ; r∙ ; ≤→≤ᵍ)
open import DPRLR.Gluing.Simple.Bool using (BOOL∙ ; ⌜_⌝)

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
      ; _∘_ to _∘ₘ_
      ; _[_]Tm to _[_]Tmₘ
      ; Bool to Boolₘ
      ; _×ᵗʸ_ to _×ᵗʸₘ_
      ; fst to fstₘ
      ; snd to sndₘ
      ; _⇒ᵗʸ_ to _⇒ᵗʸₘ_
      ; app to appₘ
      ; tm-thin to tm-thinₘ
      )

  record CtxPred (Γ° : Ctxₘ) : Type (ℓ-suc ℓM) where
    field
      Γ∙ : Subₘ εₘ Γ° → Type ℓM
      Γ∙-isSet : (γ° : Subₘ εₘ Γ°) → isSet (Γ∙ γ°)

  record TyPred (A° : Tyₘ) : Type (ℓ-suc ℓM) where
    field
      A∙ : Tmₘ εₘ A° → Type ℓM
      cA : isContravariant A∙
      A∙-isSet : (M° : Tmₘ εₘ A°) → isSet (A∙ M°)

  CTX :
    (Γ° : Ctxₘ)
    → CtxPred Γ°
    → GluCtx 𝓜
  GluCtx.Γ° (CTX Γ° Γ∙) = Γ°
  GluCtx.Γ∙ (CTX Γ° Γ∙) = CtxPred.Γ∙ Γ∙

  TY :
    (A° : Tyₘ)
    → TyPred A°
    → GluTy 𝓜
  GluTy.A° (TY A° A∙) = A°
  GluTy.A∙ (TY A° A∙) = TyPred.A∙ A∙
  GluTy.cA (TY A° A∙) = TyPred.cA A∙

  SUB :
    {Γ° Δ° : Ctxₘ}
    {Γ∙ : CtxPred Γ°}
    {Δ∙ : CtxPred Δ°}
    (σ° : Subₘ Γ° Δ°)
    → ((γ° : Subₘ εₘ Γ°) → CtxPred.Γ∙ Γ∙ γ° → CtxPred.Γ∙ Δ∙ (σ° ∘ₘ γ°))
    → GluSub 𝓜 (CTX Γ° Γ∙) (CTX Δ° Δ∙)
  GluSub.σ° (SUB σ° σ∙) = σ°
  GluSub.σ∙ (SUB σ° σ∙) = σ∙

  TM :
    {Γ° : Ctxₘ} {A° : Tyₘ}
    {Γ∙ : CtxPred Γ°}
    {A∙ : TyPred A°}
    (M° : Tmₘ Γ° A°)
    → ((γ° : Subₘ εₘ Γ°) (γ∙ : CtxPred.Γ∙ Γ∙ γ°)
        → TyPred.A∙ A∙ (M° [ γ° ]Tmₘ))
    → GluTm 𝓜 (CTX Γ° Γ∙) (TY A° A∙)
  GluTm.M° (TM M° M∙) = M°
  GluTm.M∙ (TM M° M∙) = M∙

  TMPredᴰ :
    {Γ° : Ctxₘ} {A° : Tyₘ}
    → CtxPred Γ°
    → TyPred A°
    → Tmₘ Γ° A°
    → Type ℓM
  TMPredᴰ {Γ° = Γ°} Γ∙ A∙ M° =
    (γ° : Subₘ εₘ Γ°) (γ∙ : CtxPred.Γ∙ Γ∙ γ°)
    → TyPred.A∙ A∙ (M° [ γ° ]Tmₘ)

  TMPredᴰ-isSet :
    {Γ° : Ctxₘ} {A° : Tyₘ}
    (Γ∙ : CtxPred Γ°)
    (A∙ : TyPred A°)
    (M° : Tmₘ Γ° A°)
    → isSet (TMPredᴰ Γ∙ A∙ M°)
  TMPredᴰ-isSet Γ∙ A∙ M° =
    isSetΠ2 λ γ° _ →
      TyPred.A∙-isSet A∙ (M° [ γ° ]Tmₘ)

  TMPredᴰ-contravariant :
    {Γ° : Ctxₘ} {A° : Tyₘ}
    (Γ∙ : CtxPred Γ°)
    (A∙ : TyPred A°)
    → isContravariant (TMPredᴰ Γ∙ A∙)
  TMPredᴰ-contravariant Γ∙ A∙ =
    contravariant-Π λ γ° →
      contravariant-Π λ _ →
        contravariant-reindex
          (λ M° → M° [ γ° ]Tmₘ)
          (TyPred.cA A∙)

  BOOLᴰ : TyPred Boolₘ
  TyPred.A∙ BOOLᴰ =
    GluTy.A∙ (BOOL 𝓜)
  TyPred.cA BOOLᴰ =
    GluTy.cA (BOOL 𝓜)
  TyPred.A∙-isSet BOOLᴰ = λ M° →
    isSetΣ isSetBool λ b →
      isProp→isSet (tm-thinₘ εₘ Boolₘ M° (⌜_⌝ 𝓜 b))

  PRODᴰ : {A° B° : Tyₘ} → TyPred A° → TyPred B° → TyPred (A° ×ᵗʸₘ B°)
  TyPred.A∙ (PRODᴰ {A° = A°} {B° = B°} A∙ B∙) =
    GluTy.A∙ (PROD 𝓜 (TY A° A∙) (TY B° B∙))
  TyPred.cA (PRODᴰ {A° = A°} {B° = B°} A∙ B∙) =
    GluTy.cA (PROD 𝓜 (TY A° A∙) (TY B° B∙))
  TyPred.A∙-isSet (PRODᴰ A∙ B∙) P° =
    isSet×
      (TyPred.A∙-isSet A∙ (fstₘ P°))
      (TyPred.A∙-isSet B∙ (sndₘ P°))

  FUNᴰ : {A° B° : Tyₘ} → TyPred A° → TyPred B° → TyPred (A° ⇒ᵗʸₘ B°)
  TyPred.A∙ (FUNᴰ {A° = A°} {B° = B°} A∙ B∙) =
    GluTy.A∙ (FUN 𝓜 (TY A° A∙) (TY B° B∙))
  TyPred.cA (FUNᴰ {A° = A°} {B° = B°} A∙ B∙) =
    GluTy.cA (FUN 𝓜 (TY A° A∙) (TY B° B∙))
  TyPred.A∙-isSet (FUNᴰ {A° = A°} {B° = B°} A∙ B∙) F° =
    isSetΠ2 λ M° M∙ →
      TyPred.A∙-isSet B∙ (appₘ F° M°)

  εᴰ : CtxPred εₘ
  CtxPred.Γ∙ εᴰ =
    GluCtx.Γ∙ (εᵍ 𝓜)
  CtxPred.Γ∙-isSet εᴰ _ =
    isSetUnit*

  _▷ᴰ_ :
    {Γ° : Ctxₘ} {A° : Tyₘ}
    → CtxPred Γ°
    → TyPred A°
    → CtxPred (Γ° ▷ₘ A°)
  CtxPred.Γ∙ (_▷ᴰ_ {Γ° = Γ°} {A° = A°} Γ∙ A∙) =
    GluCtx.Γ∙ (_▷ᵍ_ 𝓜 (CTX Γ° Γ∙) (TY A° A∙))
  CtxPred.Γ∙-isSet (Γ∙ ▷ᴰ A∙) δ° =
    isSetΣ
      (CtxPred.Γ∙-isSet Γ∙ (pₘ ∘ₘ δ°))
      (λ _ → TyPred.A∙-isSet A∙ (qₘ [ δ° ]Tmₘ))

  prodTmᴰ :
    {Γ° : Ctxₘ} {A° B° : Tyₘ}
    → (Γ∙ : CtxPred Γ°)
    → (A∙ : TyPred A°)
    → (B∙ : TyPred B°)
    → (P° : Tmₘ Γ° (A° ×ᵗʸₘ B°))
    → ((γ° : Subₘ εₘ Γ°) (γ∙ : CtxPred.Γ∙ Γ∙ γ°)
        → TyPred.A∙ (PRODᴰ A∙ B∙) (P° [ γ° ]Tmₘ))
    → GluTm 𝓜 (CTX Γ° Γ∙) (PROD 𝓜 (TY A° A∙) (TY B° B∙))
  prodTmᴰ Γ∙ A∙ B∙ P° P∙ =
    record
      { M° = P°
      ; M∙ = P∙
      }

  funTmᴰ :
    {Γ° : Ctxₘ} {A° B° : Tyₘ}
    → (Γ∙ : CtxPred Γ°)
    → (A∙ : TyPred A°)
    → (B∙ : TyPred B°)
    → (F° : Tmₘ Γ° (A° ⇒ᵗʸₘ B°))
    → ((γ° : Subₘ εₘ Γ°) (γ∙ : CtxPred.Γ∙ Γ∙ γ°)
        → TyPred.A∙ (FUNᴰ A∙ B∙) (F° [ γ° ]Tmₘ))
    → GluTm 𝓜 (CTX Γ° Γ∙) (FUN 𝓜 (TY A° A∙) (TY B° B∙))
  funTmᴰ Γ∙ A∙ B∙ F° F∙ =
    record
      { M° = F°
      ; M∙ = F∙
      }

  gluing-homP :
    {Γ : GluCtx 𝓜} {A : GluTy 𝓜}
    {M N : GluTm 𝓜 Γ A}
    (r : _≤ᵍ_ 𝓜 {Γ = Γ} {A = A} M N)
    → (λ M° →
        (γ° : Subₘ εₘ (GluCtx.Γ° Γ)) (γ∙ : GluCtx.Γ∙ Γ γ°)
        → GluTy.A∙ A (M° [ γ° ]Tmₘ))
      ⊢ GluTm.M∙ M ≤[ _≤ᵍ_.r° r ] GluTm.M∙ N
  gluing-homP r =
    (λ i γ° γ∙ → fst (_≤ᵍ_.r∙ r γ° γ∙) i)
    , (λ i γ° γ∙ → fst (snd (_≤ᵍ_.r∙ r γ° γ∙)) i)
    , (λ i γ° γ∙ → snd (snd (_≤ᵍ_.r∙ r γ° γ∙)) i)

  gluing-homP≤ :
    {Γ : GluCtx 𝓜} {A : GluTy 𝓜}
    {M N : GluTm 𝓜 Γ A}
    (h : M ≤ N)
    → (λ M° →
        (γ° : Subₘ εₘ (GluCtx.Γ° Γ)) (γ∙ : GluCtx.Γ∙ Γ γ°)
        → GluTy.A∙ A (M° [ γ° ]Tmₘ))
      ⊢ GluTm.M∙ M ≤[ hom-map GluTm.M° h ] GluTm.M∙ N
  gluing-homP≤ h =
    gluing-homP (≤→≤ᵍ 𝓜 h)

  GluingDisplayed :
    DisplayedSimpleCwF (ℓ-suc ℓM) ℓM (SimpleDirectedCwF.cwf 𝓜)
  GluingDisplayed =
    record
      { Ctx∙ = CtxPred
      ; Ty∙ = TyPred
      ; Sub∙ = λ {Γ = Γ°} Γ∙ Δ∙ σ° →
          (γ° : Subₘ εₘ Γ°)
          → CtxPred.Γ∙ Γ∙ γ°
          → CtxPred.Γ∙ Δ∙ (σ° ∘ₘ γ°)
      ; Tm∙ = λ {Γ = Γ°} Γ∙ A∙ M° →
          (γ° : Subₘ εₘ Γ°) (γ∙ : CtxPred.Γ∙ Γ∙ γ°)
          → TyPred.A∙ A∙ (M° [ γ° ]Tmₘ)
      ; id∙ = λ {Γ = Γ°} {Γ∙ = Γ∙} →
          GluSub.σ∙ (idᵍ 𝓜 (CTX Γ° Γ∙))
      ; _∘∙_ = λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {Θ∙ = Θ∙} {σ = σ°} {τ = τ°} τ∙ σ∙ →
          GluSub.σ∙
            (_∘ᵍ_ 𝓜
              (SUB {Γ∙ = Θ∙} {Δ∙ = Δ∙} τ° τ∙)
              (SUB {Γ∙ = Γ∙} {Δ∙ = Θ∙} σ° σ∙))
      ; id-left∙ = λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {σ = σ°} σ∙ i →
          GluSub.σ∙ (id-leftᵍ 𝓜 (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙) i)
      ; id-right∙ = λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {σ = σ°} σ∙ i →
          GluSub.σ∙ (id-rightᵍ 𝓜 (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙) i)
      ; ∘-assoc∙ =
          λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {Θ∙ = Θ∙} {Ξ∙ = Ξ∙}
            {σ = σ°} {τ = τ°} {ρ = ρ°} ρ∙ τ∙ σ∙ i →
          GluSub.σ∙
            (∘-assocᵍ 𝓜
              (SUB {Γ∙ = Θ∙} {Δ∙ = Ξ∙} ρ° ρ∙)
              (SUB {Γ∙ = Δ∙} {Δ∙ = Θ∙} τ° τ∙)
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              i)
      ; _[_]Tm∙ = λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {A∙ = A∙} {M = M°} {σ = σ°} M∙ σ∙ →
          GluTm.M∙
            (_[_]Tmᵍ 𝓜
              (TM {Γ∙ = Δ∙} {A∙ = A∙} M° M∙)
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙))
      ; Tm-id∙ = λ {Γ∙ = Γ∙} {A∙ = A∙} {M = M°} M∙ i →
          GluTm.M∙ (Tm-idᵍ 𝓜 (TM {Γ∙ = Γ∙} {A∙ = A∙} M° M∙) i)
      ; Tm-∘∙ =
          λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {Θ∙ = Θ∙} {A∙ = A∙}
            {M = M°} {τ = τ°} {σ = σ°} M∙ τ∙ σ∙ i →
          GluTm.M∙
            (Tm-∘ᵍ 𝓜
              (TM {Γ∙ = Θ∙} {A∙ = A∙} M° M∙)
              (SUB {Γ∙ = Δ∙} {Δ∙ = Θ∙} τ° τ∙)
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              i)
      ; ε∙ = εᴰ
      ; ε-sub∙ = λ {Γ = Γ°} {Γ∙ = Γ∙} →
          GluSub.σ∙ (ε-subᵍ 𝓜 {Γ = CTX Γ° Γ∙})
      ; εη∙ = λ {Γ∙ = Γ∙} {σ = σ°} σ∙ i →
          GluSub.σ∙ (εηᵍ 𝓜 (SUB {Γ∙ = Γ∙} {Δ∙ = εᴰ} σ° σ∙) i)
      ; _▷∙_ = λ {Γ = Γ°} {A = A°} Γ∙ A∙ →
          Γ∙ ▷ᴰ A∙
      ; p∙ = λ {Γ = Γ°} {A = A°} {Γ∙ = Γ∙} {A∙ = A∙} →
          GluSub.σ∙ (pᵍ 𝓜 {Γ = CTX Γ° Γ∙} {A = TY A° A∙})
      ; q∙ = λ {Γ = Γ°} {A = A°} {Γ∙ = Γ∙} {A∙ = A∙} →
          GluTm.M∙ (qᵍ 𝓜 {Γ = CTX Γ° Γ∙} {A = TY A° A∙})
      ; ⟨_,_⟩∙ = λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {A∙ = A∙} {σ = σ°} {M = M°} σ∙ M∙ →
          GluSub.σ∙
            (⟨_,_⟩ᵍ 𝓜
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              (TM {Γ∙ = Γ∙} {A∙ = A∙} M° M∙))
      ; p-⟨⟩∙ = λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {A∙ = A∙} {σ = σ°} {M = M°} σ∙ M∙ i →
          GluSub.σ∙
            (p-⟨⟩ᵍ 𝓜
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              (TM {Γ∙ = Γ∙} {A∙ = A∙} M° M∙)
              i)
      ; q-⟨⟩∙ = λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {A∙ = A∙} {σ = σ°} {M = M°} σ∙ M∙ i →
          GluTm.M∙
            (q-⟨⟩ᵍ 𝓜
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              (TM {Γ∙ = Γ∙} {A∙ = A∙} M° M∙)
              i)
      ; ▷η∙ = λ {Γ = Γ°} {A = A°} {Γ∙ = Γ∙} {A∙ = A∙} i →
          GluSub.σ∙ (▷ηᵍ 𝓜 {Γ = CTX Γ° Γ∙} {A = TY A° A∙} i)
      ; ⟨⟩-∘∙ =
          λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {Θ∙ = Θ∙} {A∙ = A∙}
            {σ = σ°} {M = M°} {ρ = ρ°} σ∙ M∙ ρ∙ i →
          GluSub.σ∙
            (⟨⟩-∘ᵍ 𝓜
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              (TM {Γ∙ = Γ∙} {A∙ = A∙} M° M∙)
              (SUB {Γ∙ = Θ∙} {Δ∙ = Γ∙} ρ° ρ∙)
              i)
      ; Bool∙ = BOOLᴰ
      ; true∙ = λ {Γ = Γ°} {Γ∙ = Γ∙} →
          GluTm.M∙ (TRUE 𝓜 {Γ = CTX Γ° Γ∙})
      ; false∙ = λ {Γ = Γ°} {Γ∙ = Γ∙} →
          GluTm.M∙ (FALSE 𝓜 {Γ = CTX Γ° Γ∙})
      ; if∙ = λ {Γ∙ = Γ∙} {A∙ = A∙} {B = B°} {T = T°} {F = F°} B∙ T∙ F∙ →
          GluTm.M∙
            (IF 𝓜
              (TM {Γ∙ = Γ∙} {A∙ = BOOLᴰ} B° B∙)
              (TM {Γ∙ = Γ∙} {A∙ = A∙} T° T∙)
              (TM {Γ∙ = Γ∙} {A∙ = A∙} F° F∙))
      ; true[]∙ = λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {σ = σ°} σ∙ i →
          GluTm.M∙ (TRUE[] 𝓜 (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙) i)
      ; false[]∙ = λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {σ = σ°} σ∙ i →
          GluTm.M∙ (FALSE[] 𝓜 (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙) i)
      ; if[]∙ =
          λ {Γ∙ = Γ∙} {Δ∙ = Δ∙} {A∙ = A∙} {B = B°} {T = T°} {F = F°} {σ = σ°}
            B∙ T∙ F∙ σ∙ i →
          GluTm.M∙
            (IF[] 𝓜
              (TM {Γ∙ = Δ∙} {A∙ = BOOLᴰ} B° B∙)
              (TM {Γ∙ = Δ∙} {A∙ = A∙} T° T∙)
              (TM {Γ∙ = Δ∙} {A∙ = A∙} F° F∙)
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              i)
      ; βif-true∙ = λ {Γ∙ = Γ∙} {A∙ = A∙} {T = T°} {F = F°} T∙ F∙ →
          gluing-homP≤
            (IF-preserves-β-true 𝓜
              (TM {Γ∙ = Γ∙} {A∙ = A∙} T° T∙)
              (TM {Γ∙ = Γ∙} {A∙ = A∙} F° F∙))
      ; βif-false∙ = λ {Γ∙ = Γ∙} {A∙ = A∙} {T = T°} {F = F°} T∙ F∙ →
          gluing-homP≤
            (IF-preserves-β-false 𝓜
              (TM {Γ∙ = Γ∙} {A∙ = A∙} T° T∙)
              (TM {Γ∙ = Γ∙} {A∙ = A∙} F° F∙))
      ; _×ᵗʸ∙_ = λ A∙ B∙ → PRODᴰ A∙ B∙
      ; pair∙ = λ {A = A°} {B = B°} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙}
          {M = M°} {N = N°} M∙ N∙ →
          GluTm.M∙
            (PAIR 𝓜 {A = TY A° A∙} {B = TY B° B∙}
              (TM {Γ∙ = Γ∙} {A∙ = A∙} M° M∙)
              (TM {Γ∙ = Γ∙} {A∙ = B∙} N° N∙))
      ; fst∙ = λ {A = A°} {B = B°} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙} {P = P°} P∙ →
          GluTm.M∙
            (FST 𝓜 {A = TY A° A∙} {B = TY B° B∙}
              (prodTmᴰ Γ∙ A∙ B∙ P° P∙))
      ; snd∙ = λ {A = A°} {B = B°} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙} {P = P°} P∙ →
          GluTm.M∙
            (SND 𝓜 {A = TY A° A∙} {B = TY B° B∙}
              (prodTmᴰ Γ∙ A∙ B∙ P° P∙))
      ; pair[]∙ =
          λ {A = A°} {B = B°} {Γ∙ = Γ∙} {Δ∙ = Δ∙} {A∙ = A∙} {B∙ = B∙}
            {M = M°} {N = N°} {σ = σ°} M∙ N∙ σ∙ i →
          GluTm.M∙
            (PAIR[] 𝓜
              {A = TY A° A∙}
              {B = TY B° B∙}
              (TM {Γ∙ = Δ∙} {A∙ = A∙} M° M∙)
              (TM {Γ∙ = Δ∙} {A∙ = B∙} N° N∙)
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              i)
      ; fst[]∙ = λ {A = A°} {B = B°} {Γ∙ = Γ∙} {Δ∙ = Δ∙} {A∙ = A∙}
          {B∙ = B∙} {P = P°} {σ = σ°} P∙ σ∙ i →
          GluTm.M∙
            (FST[] 𝓜
              {A = TY A° A∙}
              {B = TY B° B∙}
              (prodTmᴰ Δ∙ A∙ B∙ P° P∙)
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              i)
      ; snd[]∙ = λ {A = A°} {B = B°} {Γ∙ = Γ∙} {Δ∙ = Δ∙} {A∙ = A∙}
          {B∙ = B∙} {P = P°} {σ = σ°} P∙ σ∙ i →
          GluTm.M∙
            (SND[] 𝓜
              {A = TY A° A∙}
              {B = TY B° B∙}
              (prodTmᴰ Δ∙ A∙ B∙ P° P∙)
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              i)
      ; β×₁∙ = λ {A = A°} {B = B°} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙}
          {M = M°} {N = N°} M∙ N∙ →
          gluing-homP≤
            (PROD-preserves-β₁ 𝓜
              {A = TY A° A∙}
              {B = TY B° B∙}
              (TM {Γ∙ = Γ∙} {A∙ = A∙} M° M∙)
              (TM {Γ∙ = Γ∙} {A∙ = B∙} N° N∙))
      ; β×₂∙ = λ {A = A°} {B = B°} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙}
          {M = M°} {N = N°} M∙ N∙ →
          gluing-homP≤
            (PROD-preserves-β₂ 𝓜
              {A = TY A° A∙}
              {B = TY B° B∙}
              (TM {Γ∙ = Γ∙} {A∙ = A∙} M° M∙)
              (TM {Γ∙ = Γ∙} {A∙ = B∙} N° N∙))
      ; η×∙ = λ {A = A°} {B = B°} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙} {P = P°} P∙ →
          gluing-homP≤
            (PROD-preserves-η 𝓜
              {A = TY A° A∙}
              {B = TY B° B∙}
              (prodTmᴰ Γ∙ A∙ B∙ P° P∙))
      ; _⇒ᵗʸ∙_ = λ A∙ B∙ → FUNᴰ A∙ B∙
      ; lam∙ = λ {Γ = Γ°} {A = A°} {B = B°} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙}
          {N = N°} N∙ →
          GluTm.M∙
            (LAM 𝓜 {Γ = CTX Γ° Γ∙} {A = TY A° A∙} {B = TY B° B∙}
              (TM {Γ∙ = Γ∙ ▷ᴰ A∙} {A∙ = B∙} N° N∙))
      ; app∙ = λ {A = A°} {B = B°} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙}
          {F = F°} {M = M°} F∙ M∙ →
          GluTm.M∙
            (APP 𝓜 {A = TY A° A∙} {B = TY B° B∙}
              (funTmᴰ Γ∙ A∙ B∙ F° F∙)
              (TM {Γ∙ = Γ∙} {A∙ = A∙} M° M∙))
      ; lam[]∙ =
          λ {Γ = Γ°} {Δ = Δ°} {A = A°} {B = B°}
            {Γ∙ = Γ∙} {Δ∙ = Δ∙} {A∙ = A∙} {B∙ = B∙}
            {N = N°} {σ = σ°} N∙ σ∙ i →
          GluTm.M∙
            (LAM[] 𝓜 {Γ = CTX Γ° Γ∙} {Δ = CTX Δ° Δ∙} {A = TY A° A∙} {B = TY B° B∙}
              (TM {Γ∙ = Δ∙ ▷ᴰ A∙} {A∙ = B∙} N° N∙)
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              i)
      ; app[]∙ =
          λ {A = A°} {B = B°} {Γ∙ = Γ∙} {Δ∙ = Δ∙} {A∙ = A∙} {B∙ = B∙}
            {F = F°} {M = M°} {σ = σ°} F∙ M∙ σ∙ i →
          GluTm.M∙
            (APP[] 𝓜
              {A = TY A° A∙}
              {B = TY B° B∙}
              (funTmᴰ Δ∙ A∙ B∙ F° F∙)
              (TM {Γ∙ = Δ∙} {A∙ = A∙} M° M∙)
              (SUB {Γ∙ = Γ∙} {Δ∙ = Δ∙} σ° σ∙)
              i)
      ; β⇒∙ =
          λ {Γ = Γ°} {A = A°} {B = B°} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙}
            {N = N°} {M = M°} N∙ M∙ →
          gluing-homP≤
            (FUN-preserves-β 𝓜
              {A = TY A° A∙}
              {B = TY B° B∙}
              (TM {Γ∙ = Γ∙ ▷ᴰ A∙} {A∙ = B∙} N° N∙)
              (TM {Γ∙ = Γ∙} {A∙ = A∙} M° M∙))
      ; η⇒∙ = λ {A = A°} {B = B°} {Γ∙ = Γ∙} {A∙ = A∙} {B∙ = B∙} {F = F°} F∙ →
          gluing-homP≤
            (FUN-preserves-η 𝓜
              {A = TY A° A∙}
              {B = TY B° B∙}
              (funTmᴰ Γ∙ A∙ B∙ F° F∙))
      }
