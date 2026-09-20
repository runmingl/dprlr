module DPRLR.Gluing.LogicalRelations.Function where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import DPRLR.Cubical.Path using (ΣPathP-subst)
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Contravariant
open import DPRLR.Simplicial.Product using (Σ≤)
open import DPRLR.Simplicial.Function
open import DPRLR.Object.Model.Model using (SimpleDirectedCwF)

module _ {ℓS ℓM : Level} (𝓜 : SimpleDirectedCwF ℓS ℓM) where
  open import DPRLR.Gluing.LogicalRelations.Judgment 𝓜
  open import DPRLR.Gluing.LogicalRelations.Substitution 𝓜

  open SimpleDirectedCwF 𝓜
    renaming
      ( Sub to Subₘ
      ; Tm to Tmₘ
      ; ε to εₘ
      ; _∘_ to _∘ₘ_
      ; _[_]Tm to _[_]Tmₘ
      ; Tm-∘ to Tm-∘ₘ
      ; _⇒ᵗʸ_ to _⇒ₘ_
      ; lam to lamₘ
      ; app to appₘ
      ; lam[] to lam[]ₘ
      ; app[] to app[]ₘ
      ; β⇒ to β⇒ₘ
      ; β⇒-subst to β⇒-substₘ
      ; η⇒ to η⇒ₘ
      ; tm-thin to tm-thinₘ
      )

  FUN∙ :
    (A B : GluTy)
    → Tmₘ εₘ (GluTy.A° A ⇒ₘ GluTy.A° B)
    → Type ℓM
  FUN∙ A B F =
    (M° : Tmₘ εₘ (GluTy.A° A))
    → GluTy.A∙ A M°
    → GluTy.A∙ B (appₘ F M°)

  FUN-contravariant :
    (A B : GluTy)
    → isContravariant (FUN∙ A B)
  FUN-contravariant A B =
    contravariant-Π λ M° →
      contravariant-Π λ _ →
        contravariant-reindex
          (λ F → appₘ F M°)
          (GluTy.cA B)

  FUN :
    (A B : GluTy)
    → GluTy
  GluTy.A° (FUN A B) = GluTy.A° A ⇒ₘ GluTy.A° B
  GluTy.A∙ (FUN A B) = FUN∙ A B
  GluTy.cA (FUN A B) = FUN-contravariant A B

  APP₀ : (A B : GluTy)
    → GluTm₀ (FUN A B) → GluTm₀ A → GluTm₀ B
  APP₀ A B (f , f∙) (m , m∙) = appₘ f m , f∙ m m∙

  APP : {Γ : GluCtx} {A B : GluTy}
    → GluTm Γ (FUN A B) → GluTm Γ A → GluTm Γ B
  GluTm.M° (APP F M) = appₘ (GluTm.M° F) (GluTm.M° M)
  GluTm.M∙ (APP {B = B} F M) γ γ∙ =
    subst (GluTy.A∙ B) (sym (app[]ₘ (GluTm.M° F) (GluTm.M° M) γ))
      (GluTm.M∙ F γ γ∙ (GluTm.M° M [ γ ]Tmₘ) (GluTm.M∙ M γ γ∙))

  APP[]₀ : {Γ : GluCtx} {A B : GluTy}
    (F : GluTm Γ (FUN A B)) (M : GluTm Γ A) (γ : GluSub₀ Γ)
    → (APP {A = A} {B = B} F M) [ γ ]Tm₀ ≡ APP₀ A B (F [ γ ]Tm₀) (M [ γ ]Tm₀)
  APP[]₀ {A = A} {B = B} F M (γ , γ∙) = sym
    (ΣPathP-subst (GluTy.A∙ B) (sym (app[]ₘ (GluTm.M° F) (GluTm.M° M) γ))
      (GluTm.M∙ F γ γ∙ (GluTm.M° M [ γ ]Tmₘ) (GluTm.M∙ M γ γ∙)))

  APP[] : {Γ Δ : GluCtx} {A B : GluTy}
    (F : GluTm Δ (FUN A B)) (M : GluTm Δ A) (σ : GluSub Γ Δ)
    → (APP {A = A} {B = B} F M) [ σ ]Tmᵍ ≡ APP {A = A} {B = B} (F [ σ ]Tmᵍ) (M [ σ ]Tmᵍ)
  APP[] {A = A} {B = B} F M σ =
    GluTm-ext (app[]ₘ (GluTm.M° F) (GluTm.M° M) (GluSub.σ° σ)) λ γ →
        ((APP {A = A} {B = B} F M) [ σ ]Tmᵍ) [ γ ]Tm₀
      ≡⟨ Tm-∘₀ (APP {A = A} {B = B} F M) σ γ ⟩
        (APP {A = A} {B = B} F M) [ σ ∘₀ γ ]Tm₀
      ≡⟨ APP[]₀ {A = A} {B = B} F M (σ ∘₀ γ) ⟩
        APP₀ A B (F [ σ ∘₀ γ ]Tm₀) (M [ σ ∘₀ γ ]Tm₀)
      ≡⟨ cong₂ (APP₀ A B) (sym (Tm-∘₀ F σ γ)) (sym (Tm-∘₀ M σ γ)) ⟩
        APP₀ A B ((F [ σ ]Tmᵍ) [ γ ]Tm₀) ((M [ σ ]Tmᵍ) [ γ ]Tm₀)
      ≡⟨ sym (APP[]₀ {A = A} {B = B} (F [ σ ]Tmᵍ) (M [ σ ]Tmᵍ) γ) ⟩
        (APP {A = A} {B = B} (F [ σ ]Tmᵍ) (M [ σ ]Tmᵍ)) [ γ ]Tm₀
      ∎

  LAM : {Γ : GluCtx} {A B : GluTy}
    → GluTm (Γ ▷ᵍ A) B → GluTm Γ (FUN A B)
  GluTm.M° (LAM N) = lamₘ (GluTm.M° N)
  GluTm.M∙ (LAM {A = A} {B = B} N) γ γ∙ m m∙ =
    contrav-transport (GluTy.cA B) (β⇒-substₘ (GluTm.M° N) γ m)
      (snd (N [ ⟨_,_⟩₀ {A = A} (γ , γ∙) (m , m∙) ]Tm₀))

  LAM[] : {Γ Δ : GluCtx} {A B : GluTy}
    (N : GluTm (Δ ▷ᵍ A) B) (σ : GluSub Γ Δ)
    → (LAM {A = A} {B = B} N) [ σ ]Tmᵍ
      ≡ LAM {A = A} {B = B} (N [ liftᵍ {A = A} σ ]Tmᵍ)
  LAM[] {Γ = Γ} {A = A} {B = B} N σ =
    GluTm-ext (lam[]ₘ (GluTm.M° N) (GluSub.σ° σ)) λ γ →
        ((LAM {A = A} {B = B} N) [ σ ]Tmᵍ) [ γ ]Tm₀
      ≡⟨ Tm-∘₀ (LAM {A = A} {B = B} N) σ γ ⟩
        (LAM {A = A} {B = B} N) [ σ ∘₀ γ ]Tm₀
      ≡⟨ naturality γ ⟩
        (LAM {A = A} {B = B} Nσ) [ γ ]Tm₀
      ∎
    where
    Nσ : GluTm (Γ ▷ᵍ A) B
    Nσ = N [ liftᵍ {A = A} σ ]Tmᵍ

    body-path : (γ : GluSub₀ Γ) (m : GluTm₀ A)
      → Nσ [ ⟨_,_⟩₀ {A = A} γ m ]Tm₀
        ≡ N [ ⟨_,_⟩₀ {A = A} (σ ∘₀ γ) m ]Tm₀
    body-path γ m =
        Nσ [ ⟨_,_⟩₀ {A = A} γ m ]Tm₀
      ≡⟨ Tm-∘₀ N (liftᵍ {A = A} σ) (⟨_,_⟩₀ {A = A} γ m) ⟩
        N [ liftᵍ {A = A} σ ∘₀ ⟨_,_⟩₀ {A = A} γ m ]Tm₀
      ≡⟨ cong (N [_]Tm₀) (lift-⟨⟩₀ {A = A} σ γ m) ⟩
        N [ ⟨_,_⟩₀ {A = A} (σ ∘₀ γ) m ]Tm₀
      ∎

    naturality : (γ : GluSub₀ Γ)
      → (LAM {A = A} {B = B} N) [ σ ∘₀ γ ]Tm₀ ≡ (LAM {A = A} {B = B} Nσ) [ γ ]Tm₀
    naturality (γ , γ∙) = ΣPathP (base , λ i m m∙ →
      contravariant-transport-cong (GluTy.cA B) (tm-thinₘ εₘ (GluTy.A° B))
        (cong (λ f → appₘ f m) base) (cong fst (sym (body-path (γ , γ∙) (m , m∙))))
        (β⇒-substₘ (GluTm.M° N) (GluSub.σ° σ ∘ₘ γ) m)
        (β⇒-substₘ (GluTm.M° Nσ) γ m)
        (λ j → snd (body-path (γ , γ∙) (m , m∙) (~ j))) i)
      where
      base : lamₘ (GluTm.M° N) [ GluSub.σ° σ ∘ₘ γ ]Tmₘ
        ≡ lamₘ (GluTm.M° Nσ) [ γ ]Tmₘ
      base =
          lamₘ (GluTm.M° N) [ GluSub.σ° σ ∘ₘ γ ]Tmₘ
        ≡⟨ sym (Tm-∘ₘ (lamₘ (GluTm.M° N)) (GluSub.σ° σ) γ) ⟩
          (lamₘ (GluTm.M° N) [ GluSub.σ° σ ]Tmₘ) [ γ ]Tmₘ
        ≡⟨ cong (_[ γ ]Tmₘ) (lam[]ₘ (GluTm.M° N) (GluSub.σ° σ)) ⟩
          lamₘ (GluTm.M° Nσ) [ γ ]Tmₘ
        ∎

  FUN-preserves-β : {Γ : GluCtx} {A B : GluTy}
    (N : GluTm (Γ ▷ᵍ A) B) (M : GluTm Γ A)
    → APP {A = A} {B = B} (LAM {A = A} {B = B} N) M ≤ N [ ⟨ idᵍ Γ , M ⟩ᵍ ]Tmᵍ
  FUN-preserves-β {Γ} {A} {B} N M =
    GluTm-hom (β⇒ₘ (GluTm.M° N) (GluTm.M° M)) λ γ →
      subst2 _≤_ (sym (APP[]₀ {A = A} {B = B} (LAM {A = A} {B = B} N) M γ)) (sym (contractum γ))
        (Σ≤ (β⇒-substₘ (GluTm.M° N) (fst γ) (fst (M [ γ ]Tm₀)))
          (contravariant-universal-from (GluTy.cA B) refl))
    where
    contractum : (γ : GluSub₀ Γ)
      → (N [ ⟨ idᵍ Γ , M ⟩ᵍ ]Tmᵍ) [ γ ]Tm₀
        ≡ N [ ⟨_,_⟩₀ {A = A} γ (M [ γ ]Tm₀) ]Tm₀
    contractum γ =
        (N [ ⟨ idᵍ Γ , M ⟩ᵍ ]Tmᵍ) [ γ ]Tm₀
      ≡⟨ Tm-∘₀ N (⟨ idᵍ Γ , M ⟩ᵍ) γ ⟩
        N [ ⟨ idᵍ Γ , M ⟩ᵍ ∘₀ γ ]Tm₀
      ≡⟨ cong (N [_]Tm₀) (⟨id⟩-∘₀ M γ) ⟩
        N [ ⟨_,_⟩₀ {A = A} γ (M [ γ ]Tm₀) ]Tm₀
      ∎

  FUNη-body : {Γ : GluCtx} {A B : GluTy}
    → GluTm Γ (FUN A B) → GluTm (Γ ▷ᵍ A) B
  FUNη-body {Γ} {A} {B} F = APP {A = A} {B = B} (F [ pᵍ {Γ} {A} ]Tmᵍ) (qᵍ {Γ} {A})

  FUNη-body[]₀ : {Γ : GluCtx} {A B : GluTy}
    (F : GluTm Γ (FUN A B)) (γ : GluSub₀ Γ) (m : GluTm₀ A)
    → (FUNη-body {A = A} {B = B} F) [ ⟨_,_⟩₀ {A = A} γ m ]Tm₀
      ≡ APP₀ A B (F [ γ ]Tm₀) m
  FUNη-body[]₀ {Γ} {A} {B} F γ m =
      (FUNη-body {A = A} {B = B} F) [ δ ]Tm₀
    ≡⟨ APP[]₀ {A = A} {B = B} (F [ pᵍ {Γ} {A} ]Tmᵍ) (qᵍ {Γ} {A}) δ ⟩
      APP₀ A B ((F [ pᵍ {Γ} {A} ]Tmᵍ) [ δ ]Tm₀) (qᵍ {Γ} {A} [ δ ]Tm₀)
    ≡⟨ cong (λ f → APP₀ A B f (qᵍ {Γ} {A} [ δ ]Tm₀)) (Tm-∘₀ F (pᵍ {Γ} {A}) δ) ⟩
      APP₀ A B (F [ pᵍ {Γ} {A} ∘₀ δ ]Tm₀) (qᵍ {Γ} {A} [ δ ]Tm₀)
    ≡⟨ cong₂ (APP₀ A B)
         (cong (F [_]Tm₀) (p-⟨⟩₀ {A = A} γ m)) (q-⟨⟩₀ {A = A} γ m) ⟩
      APP₀ A B (F [ γ ]Tm₀) m
    ∎
    where
    δ : GluSub₀ (Γ ▷ᵍ A)
    δ = ⟨_,_⟩₀ {A = A} γ m

  FUN-preserves-η : {Γ : GluCtx} {A B : GluTy}
    (F : GluTm Γ (FUN A B)) → LAM {A = A} {B = B} (FUNη-body {A = A} {B = B} F) ≤ F
  FUN-preserves-η {Γ = Γ} {A = A} {B = B} F = ≤ᵍ→≤ record
    { r° = η⇒ₘ (GluTm.M° F)
    ; r∙ = λ γ γ∙ →
        HomPΠ {P = λ f m → GluTy.A∙ A m → GluTy.A∙ B (appₘ f m)} λ m →
          HomPΠ {P = λ f _ → GluTy.A∙ B (appₘ f m)} λ m∙ →
            contravariant-universal-from (contravariant-reindex (λ f → appₘ f m) (GluTy.cA B))
              (pointwise γ γ∙ m m∙)
    }
    where
    pointwise : (γ : Subₘ εₘ (GluCtx.Γ° Γ)) (γ∙ : GluCtx.Γ∙ Γ γ)
      (m : Tmₘ εₘ (GluTy.A° A)) (m∙ : GluTy.A∙ A m)
      → GluTm.M∙ (LAM {A = A} {B = B} (FUNη-body {A = A} {B = B} F)) γ γ∙ m m∙
        ≡ contrav-transport (GluTy.cA B)
            (hom-map (λ f → appₘ (f [ γ ]Tmₘ) m) (η⇒ₘ (GluTm.M° F)))
            (GluTm.M∙ F γ γ∙ m m∙)
    pointwise γ γ∙ m m∙ =
      contravariant-transport-cong (GluTy.cA B) (tm-thinₘ εₘ (GluTy.A° B))
        refl (cong fst (FUNη-body[]₀ {A = A} {B = B} F (γ , γ∙) (m , m∙)))
        (β⇒-substₘ (GluTm.M° (FUNη-body {A = A} {B = B} F)) γ m)
        (hom-map (λ f → appₘ (f [ γ ]Tmₘ) m) (η⇒ₘ (GluTm.M° F)))
        (λ i → snd (FUNη-body[]₀ {A = A} {B = B} F (γ , γ∙) (m , m∙) i))
