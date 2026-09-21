module DPRLR.Gluing.LogicalRelations.Product where

open import Cubical.Foundations.Prelude
open import DPRLR.Cubical.Path using (ΣPathP-subst)
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Contravariant
open import DPRLR.Simplicial.Product
open import DPRLR.Object.Model.Model using (SimpleDirectedCwF)

module _ {ℓS ℓM : Level} (𝓜 : SimpleDirectedCwF ℓS ℓM) where
  open import DPRLR.Gluing.LogicalRelations.Judgment 𝓜
  open import DPRLR.Gluing.LogicalRelations.Substitution 𝓜

  open SimpleDirectedCwF 𝓜
    renaming
      ( Sub to Subₘ
      ; Tm to Tmₘ
      ; ε to εₘ
      ; _[_]Tm to _[_]Tmₘ
      ; _×ᵗʸ_ to _×ₘ_
      ; pair to pairₘ
      ; fst to fstₘ
      ; snd to sndₘ
      ; pair[] to pair[]ₘ
      ; fst[] to fst[]ₘ
      ; snd[] to snd[]ₘ
      ; β×₁ to β×₁ₘ
      ; β×₂ to β×₂ₘ
      ; η× to η×ₘ
      ; tm-thin to tm-thinₘ
      )

  PROD∙ :
    (A B : GluTy)
    → Tmₘ εₘ (GluTy.A° A ×ₘ GluTy.A° B)
    → Type ℓM
  PROD∙ A B P =
    GluTy.A∙ A (fstₘ P)
    ×
    GluTy.A∙ B (sndₘ P)

  PROD-contravariant :
    (A B : GluTy)
    → isContravariant (PROD∙ A B)
  PROD-contravariant A B =
    contravariant-×
      (contravariant-reindex fstₘ (GluTy.cA A))
      (contravariant-reindex sndₘ (GluTy.cA B))

  PROD :
    (A B : GluTy)
    → GluTy
  GluTy.A° (PROD A B) = GluTy.A° A ×ₘ GluTy.A° B
  GluTy.A∙ (PROD A B) = PROD∙ A B
  GluTy.cA (PROD A B) = PROD-contravariant A B

  β×₁[] :
    {Γ : GluCtx}
    (A B : GluTy)
    (M : GluTm Γ A)
    (N : GluTm Γ B)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    → fstₘ (pairₘ (GluTm.M° M) (GluTm.M° N) [ γ° ]Tmₘ)
      ≤ (GluTm.M° M [ γ° ]Tmₘ)
  β×₁[] A B M N γ° =
    subst
      (λ t → t ≤ (GluTm.M° M [ γ° ]Tmₘ))
      (fst[]ₘ (pairₘ (GluTm.M° M) (GluTm.M° N)) γ°)
      (hom-map (λ t → t [ γ° ]Tmₘ)
        (β×₁ₘ (GluTm.M° M) (GluTm.M° N)))

  β×₂[] :
    {Γ : GluCtx}
    (A B : GluTy)
    (M : GluTm Γ A)
    (N : GluTm Γ B)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    → sndₘ (pairₘ (GluTm.M° M) (GluTm.M° N) [ γ° ]Tmₘ)
      ≤ (GluTm.M° N [ γ° ]Tmₘ)
  β×₂[] A B M N γ° =
    subst
      (λ t → t ≤ (GluTm.M° N [ γ° ]Tmₘ))
      (snd[]ₘ (pairₘ (GluTm.M° M) (GluTm.M° N)) γ°)
      (hom-map (λ t → t [ γ° ]Tmₘ)
        (β×₂ₘ (GluTm.M° M) (GluTm.M° N)))

  PAIR :
    {Γ : GluCtx}
    {A B : GluTy}
    → GluTm Γ A
    → GluTm Γ B
    → GluTm Γ (PROD A B)
  GluTm.M° (PAIR M N) = pairₘ (GluTm.M° M) (GluTm.M° N)
  GluTm.M∙ (PAIR {A = A} {B = B} M N) γ° γ∙ =
    contrav-transport
      (GluTy.cA A)
      (β×₁[] A B M N γ°)
      (GluTm.M∙ M γ° γ∙)
    ,
    contrav-transport
      (GluTy.cA B)
      (β×₂[] A B M N γ°)
      (GluTm.M∙ N γ° γ∙)

  FST :
    {Γ : GluCtx}
    {A B : GluTy}
    → GluTm Γ (PROD A B)
    → GluTm Γ A
  GluTm.M° (FST M) = fstₘ (GluTm.M° M)
  GluTm.M∙ (FST {A = A} M) γ° γ∙ =
    subst
      (GluTy.A∙ A)
      (sym (fst[]ₘ (GluTm.M° M) γ°))
      (fst (GluTm.M∙ M γ° γ∙))

  SND :
    {Γ : GluCtx}
    {A B : GluTy}
    → GluTm Γ (PROD A B)
    → GluTm Γ B
  GluTm.M° (SND M) = sndₘ (GluTm.M° M)
  GluTm.M∙ (SND {B = B} M) γ° γ∙ =
    subst
      (GluTy.A∙ B)
      (sym (snd[]ₘ (GluTm.M° M) γ°))
      (snd (GluTm.M∙ M γ° γ∙))

  FST₀ : (A B : GluTy) → GluTm₀ (PROD A B) → GluTm₀ A
  FST₀ A B (p , a , b) = fstₘ p , a

  SND₀ : (A B : GluTy) → GluTm₀ (PROD A B) → GluTm₀ B
  SND₀ A B (p , a , b) = sndₘ p , b

  PAIR₀ : (A B : GluTy) → GluTm₀ A → GluTm₀ B → GluTm₀ (PROD A B)
  PAIR₀ A B (m , m∙) (n , n∙) = pairₘ m n
    , contrav-transport (GluTy.cA A) (β×₁ₘ m n) m∙
    , contrav-transport (GluTy.cA B) (β×₂ₘ m n) n∙

  FST[]₀ : {Γ : GluCtx} {A B : GluTy}
    (P : GluTm Γ (PROD A B)) (γ : GluSub₀ Γ)
    → (FST {A = A} {B = B} P) [ γ ]Tm₀ ≡ FST₀ A B (P [ γ ]Tm₀)
  FST[]₀ {A = A} P (γ , γ∙) = sym
    (ΣPathP-subst (GluTy.A∙ A) (sym (fst[]ₘ (GluTm.M° P) γ)) (fst (GluTm.M∙ P γ γ∙)))

  SND[]₀ : {Γ : GluCtx} {A B : GluTy}
    (P : GluTm Γ (PROD A B)) (γ : GluSub₀ Γ)
    → (SND {A = A} {B = B} P) [ γ ]Tm₀ ≡ SND₀ A B (P [ γ ]Tm₀)
  SND[]₀ {B = B} P (γ , γ∙) = sym
    (ΣPathP-subst (GluTy.A∙ B) (sym (snd[]ₘ (GluTm.M° P) γ)) (snd (GluTm.M∙ P γ γ∙)))

  PAIR[]₀ : {Γ : GluCtx} {A B : GluTy}
    (M : GluTm Γ A) (N : GluTm Γ B) (γ : GluSub₀ Γ)
    → (PAIR M N) [ γ ]Tm₀ ≡ PAIR₀ A B (M [ γ ]Tm₀) (N [ γ ]Tm₀)
  PAIR[]₀ {A = A} {B = B} M N (γ , γ∙) = ΣPathP (base , λ i → first i , second i)
    where
    base = pair[]ₘ (GluTm.M° M) (GluTm.M° N) γ
    first = contravariant-transport-cong (GluTy.cA A) (tm-thinₘ εₘ (GluTy.A° A))
      (cong fstₘ base) refl (β×₁[] A B M N γ)
      (β×₁ₘ (GluTm.M° M [ γ ]Tmₘ) (GluTm.M° N [ γ ]Tmₘ)) refl
    second = contravariant-transport-cong (GluTy.cA B) (tm-thinₘ εₘ (GluTy.A° B))
      (cong sndₘ base) refl (β×₂[] A B M N γ)
      (β×₂ₘ (GluTm.M° M [ γ ]Tmₘ) (GluTm.M° N [ γ ]Tmₘ)) refl

  PAIR[] : {Γ Δ : GluCtx} {A B : GluTy}
    (M : GluTm Δ A) (N : GluTm Δ B) (σ : GluSub Γ Δ)
    → (PAIR M N) [ σ ]Tmᵍ ≡ PAIR (M [ σ ]Tmᵍ) (N [ σ ]Tmᵍ)
  PAIR[] {A = A} {B = B} M N σ =
    GluTm-ext (pair[]ₘ (GluTm.M° M) (GluTm.M° N) (GluSub.σ° σ)) λ γ →
        ((PAIR M N) [ σ ]Tmᵍ) [ γ ]Tm₀
      ≡⟨ Tm-∘₀ (PAIR M N) σ γ ⟩
        (PAIR M N) [ σ ∘₀ γ ]Tm₀
      ≡⟨ PAIR[]₀ M N (σ ∘₀ γ) ⟩
        PAIR₀ A B (M [ σ ∘₀ γ ]Tm₀) (N [ σ ∘₀ γ ]Tm₀)
      ≡⟨ cong₂ (PAIR₀ A B)
           (sym (Tm-∘₀ M σ γ)) (sym (Tm-∘₀ N σ γ)) ⟩
        PAIR₀ A B ((M [ σ ]Tmᵍ) [ γ ]Tm₀) ((N [ σ ]Tmᵍ) [ γ ]Tm₀)
      ≡⟨ sym (PAIR[]₀ (M [ σ ]Tmᵍ) (N [ σ ]Tmᵍ) γ) ⟩
        (PAIR (M [ σ ]Tmᵍ) (N [ σ ]Tmᵍ)) [ γ ]Tm₀
      ∎

  FST[] : {Γ Δ : GluCtx} {A B : GluTy}
    (P : GluTm Δ (PROD A B)) (σ : GluSub Γ Δ)
    → (FST {A = A} {B = B} P) [ σ ]Tmᵍ ≡ FST {A = A} {B = B} (P [ σ ]Tmᵍ)
  FST[] {A = A} {B = B} P σ = GluTm-ext (fst[]ₘ (GluTm.M° P) (GluSub.σ° σ)) λ γ →
      ((FST {A = A} {B = B} P) [ σ ]Tmᵍ) [ γ ]Tm₀
    ≡⟨ Tm-∘₀ (FST {A = A} {B = B} P) σ γ ⟩
      (FST {A = A} {B = B} P) [ σ ∘₀ γ ]Tm₀
    ≡⟨ FST[]₀ {A = A} {B = B} P (σ ∘₀ γ) ⟩
      FST₀ A B (P [ σ ∘₀ γ ]Tm₀)
    ≡⟨ cong (FST₀ A B) (sym (Tm-∘₀ P σ γ)) ⟩
      FST₀ A B ((P [ σ ]Tmᵍ) [ γ ]Tm₀)
    ≡⟨ sym (FST[]₀ {A = A} {B = B} (P [ σ ]Tmᵍ) γ) ⟩
      (FST {A = A} {B = B} (P [ σ ]Tmᵍ)) [ γ ]Tm₀
    ∎

  SND[] : {Γ Δ : GluCtx} {A B : GluTy}
    (P : GluTm Δ (PROD A B)) (σ : GluSub Γ Δ)
    → (SND {A = A} {B = B} P) [ σ ]Tmᵍ ≡ SND {A = A} {B = B} (P [ σ ]Tmᵍ)
  SND[] {A = A} {B = B} P σ = GluTm-ext (snd[]ₘ (GluTm.M° P) (GluSub.σ° σ)) λ γ →
      ((SND {A = A} {B = B} P) [ σ ]Tmᵍ) [ γ ]Tm₀
    ≡⟨ Tm-∘₀ (SND {A = A} {B = B} P) σ γ ⟩
      (SND {A = A} {B = B} P) [ σ ∘₀ γ ]Tm₀
    ≡⟨ SND[]₀ {A = A} {B = B} P (σ ∘₀ γ) ⟩
      SND₀ A B (P [ σ ∘₀ γ ]Tm₀)
    ≡⟨ cong (SND₀ A B) (sym (Tm-∘₀ P σ γ)) ⟩
      SND₀ A B ((P [ σ ]Tmᵍ) [ γ ]Tm₀)
    ≡⟨ sym (SND[]₀ {A = A} {B = B} (P [ σ ]Tmᵍ) γ) ⟩
      (SND {A = A} {B = B} (P [ σ ]Tmᵍ)) [ γ ]Tm₀
    ∎

  PAIR₀-β₁ : (A B : GluTy) (m : GluTm₀ A) (n : GluTm₀ B)
    → FST₀ A B (PAIR₀ A B m n) ≤ m
  PAIR₀-β₁ A B (m , m∙) (n , n∙) =
    Σ≤ (β×₁ₘ m n) (contravariant-lift-hom (GluTy.cA A) (β×₁ₘ m n) m∙)

  PAIR₀-β₂ : (A B : GluTy) (m : GluTm₀ A) (n : GluTm₀ B)
    → SND₀ A B (PAIR₀ A B m n) ≤ n
  PAIR₀-β₂ A B (m , m∙) (n , n∙) =
    Σ≤ (β×₂ₘ m n) (contravariant-lift-hom (GluTy.cA B) (β×₂ₘ m n) n∙)

  PAIR₀-η : (A B : GluTy) (p : GluTm₀ (PROD A B))
    → PAIR₀ A B (FST₀ A B p) (SND₀ A B p) ≤ p
  PAIR₀-η A B (p , a , b) = Σ≤ (η×ₘ p)
    (HomP× {C = λ p → GluTy.A∙ A (fstₘ p)} {D = λ p → GluTy.A∙ B (sndₘ p)}
      (contravariant-universal-from (contravariant-reindex fstₘ (GluTy.cA A))
        (cong (λ h → contrav-transport (GluTy.cA A) h a)
          (tm-thinₘ εₘ (GluTy.A° A) _ _ (β×₁ₘ (fstₘ p) (sndₘ p)) (hom-map fstₘ (η×ₘ p)))))
      (contravariant-universal-from (contravariant-reindex sndₘ (GluTy.cA B))
        (cong (λ h → contrav-transport (GluTy.cA B) h b)
          (tm-thinₘ εₘ (GluTy.A° B) _ _ (β×₂ₘ (fstₘ p) (sndₘ p)) (hom-map sndₘ (η×ₘ p))))))

  PROD-preserves-β₁ : {Γ : GluCtx} {A B : GluTy}
    (M : GluTm Γ A) (N : GluTm Γ B)
    → FST {A = A} {B = B} (PAIR M N) ≤ M
  PROD-preserves-β₁ {A = A} {B = B} M N =
    GluTm-hom (β×₁ₘ (GluTm.M° M) (GluTm.M° N)) λ γ →
      subst (_≤ (M [ γ ]Tm₀))
        (sym (
            (FST {A = A} {B = B} (PAIR M N)) [ γ ]Tm₀
          ≡⟨ FST[]₀ {A = A} {B = B} (PAIR M N) γ ⟩
            FST₀ A B ((PAIR M N) [ γ ]Tm₀)
          ≡⟨ cong (FST₀ A B) (PAIR[]₀ M N γ) ⟩
            FST₀ A B (PAIR₀ A B (M [ γ ]Tm₀) (N [ γ ]Tm₀))
          ∎))
        (PAIR₀-β₁ A B (M [ γ ]Tm₀) (N [ γ ]Tm₀))

  PROD-preserves-β₂ : {Γ : GluCtx} {A B : GluTy}
    (M : GluTm Γ A) (N : GluTm Γ B)
    → SND {A = A} {B = B} (PAIR M N) ≤ N
  PROD-preserves-β₂ {A = A} {B = B} M N =
    GluTm-hom (β×₂ₘ (GluTm.M° M) (GluTm.M° N)) λ γ →
      subst (_≤ (N [ γ ]Tm₀))
        (sym (
            (SND {A = A} {B = B} (PAIR M N)) [ γ ]Tm₀
          ≡⟨ SND[]₀ {A = A} {B = B} (PAIR M N) γ ⟩
            SND₀ A B ((PAIR M N) [ γ ]Tm₀)
          ≡⟨ cong (SND₀ A B) (PAIR[]₀ M N γ) ⟩
            SND₀ A B (PAIR₀ A B (M [ γ ]Tm₀) (N [ γ ]Tm₀))
          ∎))
        (PAIR₀-β₂ A B (M [ γ ]Tm₀) (N [ γ ]Tm₀))

  PROD-preserves-η : {Γ : GluCtx} {A B : GluTy}
    (P : GluTm Γ (PROD A B))
    → PAIR (FST {A = A} {B = B} P) (SND {A = A} {B = B} P) ≤ P
  PROD-preserves-η {A = A} {B = B} P = GluTm-hom (η×ₘ (GluTm.M° P)) λ γ →
    subst (_≤ (P [ γ ]Tm₀))
      (sym (
          (PAIR (FST {A = A} {B = B} P) (SND {A = A} {B = B} P)) [ γ ]Tm₀
        ≡⟨ PAIR[]₀ (FST {A = A} {B = B} P) (SND {A = A} {B = B} P) γ ⟩
          PAIR₀ A B ((FST {A = A} {B = B} P) [ γ ]Tm₀) ((SND {A = A} {B = B} P) [ γ ]Tm₀)
        ≡⟨ cong₂ (PAIR₀ A B) (FST[]₀ {A = A} {B = B} P γ) (SND[]₀ {A = A} {B = B} P γ) ⟩
          PAIR₀ A B (FST₀ A B (P [ γ ]Tm₀)) (SND₀ A B (P [ γ ]Tm₀))
        ∎))
      (PAIR₀-η A B (P [ γ ]Tm₀))
