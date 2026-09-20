module DPRLR.Object.Model.DisplayedModel where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd ; lift)
open import Cubical.Data.Sigma hiding (Sub)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Product
open import DPRLR.Object.Model.Model using (SimpleCwF)

record DisplayedSimpleCwF
  {ℓS ℓM : Level} (ℓD₀ ℓD₁ : Level) (𝓒 : SimpleCwF ℓS ℓM)
  : Type (ℓ-suc (ℓ-max (ℓ-max ℓS ℓM) (ℓ-max ℓD₀ ℓD₁))) where
  open SimpleCwF 𝓒

  infixl 30 _∘∙_
  infixl 40 _[_]Tm∙
  infixr 35 _▷∙_
  infixr 25 _×ᵗʸ∙_ _⇒ᵗʸ∙_
  infix  5 ⟨_,_⟩∙

  field
    Ctx∙ : Ctx → Type ℓD₀
    Ty∙  : Ty → Type ℓD₀
    Sub∙ : {Γ Δ : Ctx} → Ctx∙ Γ → Ctx∙ Δ → Sub Γ Δ → Type ℓD₁
    Tm∙  : {Γ : Ctx} {A : Ty} → Ctx∙ Γ → Ty∙ A → Tm Γ A → Type ℓD₁

    id∙ :
      {Γ : Ctx} {Γ∙ : Ctx∙ Γ}
      → Sub∙ Γ∙ Γ∙ id
    _∘∙_ :
      {Γ Δ Θ : Ctx}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {Θ∙ : Ctx∙ Θ}
      {σ : Sub Γ Θ} {τ : Sub Θ Δ}
      → Sub∙ Θ∙ Δ∙ τ
      → Sub∙ Γ∙ Θ∙ σ
      → Sub∙ Γ∙ Δ∙ (τ ∘ σ)
    id-left∙ :
      {Γ Δ : Ctx}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ}
      {σ : Sub Γ Δ}
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Sub∙ Γ∙ Δ∙ (id-left σ i))
          (id∙ ∘∙ σ∙)
          σ∙
    id-right∙ :
      {Γ Δ : Ctx}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ}
      {σ : Sub Γ Δ}
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Sub∙ Γ∙ Δ∙ (id-right σ i))
          (σ∙ ∘∙ id∙)
          σ∙
    ∘-assoc∙ :
      {Γ Δ Θ Ξ : Ctx}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {Θ∙ : Ctx∙ Θ} {Ξ∙ : Ctx∙ Ξ}
      {σ : Sub Γ Δ} {τ : Sub Δ Θ} {ρ : Sub Θ Ξ}
      (ρ∙ : Sub∙ Θ∙ Ξ∙ ρ)
      (τ∙ : Sub∙ Δ∙ Θ∙ τ)
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Sub∙ Γ∙ Ξ∙ (∘-assoc ρ τ σ i))
          ((ρ∙ ∘∙ τ∙) ∘∙ σ∙)
          (ρ∙ ∘∙ (τ∙ ∘∙ σ∙))

    _[_]Tm∙ :
      {Γ Δ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A}
      {M : Tm Δ A} {σ : Sub Γ Δ}
      → Tm∙ Δ∙ A∙ M
      → Sub∙ Γ∙ Δ∙ σ
      → Tm∙ Γ∙ A∙ (M [ σ ]Tm)
    Tm-id∙ :
      {Γ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A}
      {M : Tm Γ A}
      (M∙ : Tm∙ Γ∙ A∙ M)
      → PathP (λ i → Tm∙ Γ∙ A∙ (Tm-id M i))
          (M∙ [ id∙ ]Tm∙)
          M∙
    Tm-∘∙ :
      {Γ Δ Θ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {Θ∙ : Ctx∙ Θ} {A∙ : Ty∙ A}
      {M : Tm Θ A} {τ : Sub Δ Θ} {σ : Sub Γ Δ}
      (M∙ : Tm∙ Θ∙ A∙ M)
      (τ∙ : Sub∙ Δ∙ Θ∙ τ)
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Tm∙ Γ∙ A∙ (Tm-∘ M τ σ i))
          ((M∙ [ τ∙ ]Tm∙) [ σ∙ ]Tm∙)
          (M∙ [ τ∙ ∘∙ σ∙ ]Tm∙)

    ε∙ : Ctx∙ ε
    ε-sub∙ :
      {Γ : Ctx} {Γ∙ : Ctx∙ Γ}
      → Sub∙ Γ∙ ε∙ ε-sub
    εη∙ :
      {Γ : Ctx} {Γ∙ : Ctx∙ Γ}
      {σ : Sub Γ ε}
      (σ∙ : Sub∙ Γ∙ ε∙ σ)
      → PathP (λ i → Sub∙ Γ∙ ε∙ (εη σ i))
          σ∙
          ε-sub∙

    _▷∙_ :
      {Γ : Ctx} {A : Ty}
      → Ctx∙ Γ → Ty∙ A → Ctx∙ (Γ ▷ A)
    p∙ :
      {Γ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A}
      → Sub∙ (Γ∙ ▷∙ A∙) Γ∙ p
    q∙ :
      {Γ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A}
      → Tm∙ (Γ∙ ▷∙ A∙) A∙ q
    ⟨_,_⟩∙ :
      {Γ Δ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A}
      {σ : Sub Γ Δ} {M : Tm Γ A}
      → Sub∙ Γ∙ Δ∙ σ
      → Tm∙ Γ∙ A∙ M
      → Sub∙ Γ∙ (Δ∙ ▷∙ A∙) ⟨ σ , M ⟩
    p-⟨⟩∙ :
      {Γ Δ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A}
      {σ : Sub Γ Δ} {M : Tm Γ A}
      (σ∙ : Sub∙ Γ∙ Δ∙ σ) (M∙ : Tm∙ Γ∙ A∙ M)
      → PathP (λ i → Sub∙ Γ∙ Δ∙ (p-⟨⟩ σ M i))
          (p∙ ∘∙ ⟨ σ∙ , M∙ ⟩∙)
          σ∙
    q-⟨⟩∙ :
      {Γ Δ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A}
      {σ : Sub Γ Δ} {M : Tm Γ A}
      (σ∙ : Sub∙ Γ∙ Δ∙ σ) (M∙ : Tm∙ Γ∙ A∙ M)
      → PathP (λ i → Tm∙ Γ∙ A∙ (q-⟨⟩ σ M i))
          (q∙ [ ⟨ σ∙ , M∙ ⟩∙ ]Tm∙)
          M∙
    ▷η∙ :
      {Γ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A}
      → PathP (λ i → Sub∙ (Γ∙ ▷∙ A∙) (Γ∙ ▷∙ A∙) (▷η {Γ = Γ} {A = A} i))
          (⟨ p∙ , q∙ ⟩∙)
          id∙
    ⟨⟩-∘∙ :
      {Γ Δ Θ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {Θ∙ : Ctx∙ Θ} {A∙ : Ty∙ A}
      {σ : Sub Γ Δ} {M : Tm Γ A} {ρ : Sub Θ Γ}
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      (M∙ : Tm∙ Γ∙ A∙ M)
      (ρ∙ : Sub∙ Θ∙ Γ∙ ρ)
      → PathP (λ i → Sub∙ Θ∙ (Δ∙ ▷∙ A∙) (⟨⟩-∘ σ M ρ i))
          (⟨ σ∙ , M∙ ⟩∙ ∘∙ ρ∙)
          (⟨ σ∙ ∘∙ ρ∙ , M∙ [ ρ∙ ]Tm∙ ⟩∙)

  lift∙ :
    {Γ Δ : Ctx} {A : Ty}
    {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A}
    {σ : Sub Γ Δ}
    → Sub∙ Γ∙ Δ∙ σ
    → Sub∙ (Γ∙ ▷∙ A∙) (Δ∙ ▷∙ A∙) (lift σ)
  lift∙ σ∙ = ⟨ σ∙ ∘∙ p∙ , q∙ ⟩∙

  field
    Bool∙ : Ty∙ Bool
    true∙ :
      {Γ : Ctx} {Γ∙ : Ctx∙ Γ}
      → Tm∙ Γ∙ Bool∙ true
    false∙ :
      {Γ : Ctx} {Γ∙ : Ctx∙ Γ}
      → Tm∙ Γ∙ Bool∙ false
    if∙ :
      {Γ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A}
      {B : Tm Γ Bool} {T F : Tm Γ A}
      → Tm∙ Γ∙ Bool∙ B
      → Tm∙ Γ∙ A∙ T
      → Tm∙ Γ∙ A∙ F
      → Tm∙ Γ∙ A∙ (if B then T else F)
    true[]∙ :
      {Γ Δ : Ctx}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ}
      {σ : Sub Γ Δ}
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Tm∙ Γ∙ Bool∙ (true[] σ i))
          (true∙ [ σ∙ ]Tm∙)
          true∙
    false[]∙ :
      {Γ Δ : Ctx}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ}
      {σ : Sub Γ Δ}
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Tm∙ Γ∙ Bool∙ (false[] σ i))
          (false∙ [ σ∙ ]Tm∙)
          false∙
    if[]∙ :
      {Γ Δ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A}
      {B : Tm Δ Bool} {T F : Tm Δ A} {σ : Sub Γ Δ}
      (B∙ : Tm∙ Δ∙ Bool∙ B)
      (T∙ : Tm∙ Δ∙ A∙ T)
      (F∙ : Tm∙ Δ∙ A∙ F)
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Tm∙ Γ∙ A∙ (if[] B T F σ i))
          (if∙ B∙ T∙ F∙ [ σ∙ ]Tm∙)
          (if∙ (B∙ [ σ∙ ]Tm∙) (T∙ [ σ∙ ]Tm∙) (F∙ [ σ∙ ]Tm∙))
    βif-true∙ :
      {Γ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A}
      {T F : Tm Γ A}
      (T∙ : Tm∙ Γ∙ A∙ T)
      (F∙ : Tm∙ Γ∙ A∙ F)
      → Tm∙ Γ∙ A∙ ⊢ if∙ true∙ T∙ F∙ ≤[ βif-true T F ] T∙
    βif-false∙ :
      {Γ : Ctx} {A : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A}
      {T F : Tm Γ A}
      (T∙ : Tm∙ Γ∙ A∙ T)
      (F∙ : Tm∙ Γ∙ A∙ F)
      → Tm∙ Γ∙ A∙ ⊢ if∙ false∙ T∙ F∙ ≤[ βif-false T F ] F∙

    _×ᵗʸ∙_ :
      {A B : Ty}
      → Ty∙ A → Ty∙ B → Ty∙ (A ×ᵗʸ B)
    pair∙ :
      {Γ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {M : Tm Γ A} {N : Tm Γ B}
      → Tm∙ Γ∙ A∙ M
      → Tm∙ Γ∙ B∙ N
      → Tm∙ Γ∙ (A∙ ×ᵗʸ∙ B∙) (pair M N)
    fst∙ :
      {Γ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {P : Tm Γ (A ×ᵗʸ B)}
      → Tm∙ Γ∙ (A∙ ×ᵗʸ∙ B∙) P
      → Tm∙ Γ∙ A∙ (SimpleCwF.fst 𝓒 P)
    snd∙ :
      {Γ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {P : Tm Γ (A ×ᵗʸ B)}
      → Tm∙ Γ∙ (A∙ ×ᵗʸ∙ B∙) P
      → Tm∙ Γ∙ B∙ (SimpleCwF.snd 𝓒 P)
    pair[]∙ :
      {Γ Δ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {M : Tm Δ A} {N : Tm Δ B} {σ : Sub Γ Δ}
      (M∙ : Tm∙ Δ∙ A∙ M)
      (N∙ : Tm∙ Δ∙ B∙ N)
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Tm∙ Γ∙ (A∙ ×ᵗʸ∙ B∙) (pair[] M N σ i))
          (pair∙ M∙ N∙ [ σ∙ ]Tm∙)
          (pair∙ (M∙ [ σ∙ ]Tm∙) (N∙ [ σ∙ ]Tm∙))
    fst[]∙ :
      {Γ Δ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {P : Tm Δ (A ×ᵗʸ B)} {σ : Sub Γ Δ}
      (P∙ : Tm∙ Δ∙ (A∙ ×ᵗʸ∙ B∙) P)
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Tm∙ Γ∙ A∙ (fst[] P σ i))
          (fst∙ P∙ [ σ∙ ]Tm∙)
          (fst∙ (P∙ [ σ∙ ]Tm∙))
    snd[]∙ :
      {Γ Δ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {P : Tm Δ (A ×ᵗʸ B)} {σ : Sub Γ Δ}
      (P∙ : Tm∙ Δ∙ (A∙ ×ᵗʸ∙ B∙) P)
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Tm∙ Γ∙ B∙ (snd[] P σ i))
          (snd∙ P∙ [ σ∙ ]Tm∙)
          (snd∙ (P∙ [ σ∙ ]Tm∙))
    β×₁∙ :
      {Γ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {M : Tm Γ A} {N : Tm Γ B}
      (M∙ : Tm∙ Γ∙ A∙ M)
      (N∙ : Tm∙ Γ∙ B∙ N)
      → Tm∙ Γ∙ A∙ ⊢ fst∙ (pair∙ M∙ N∙) ≤[ β×₁ M N ] M∙
    β×₂∙ :
      {Γ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {M : Tm Γ A} {N : Tm Γ B}
      (M∙ : Tm∙ Γ∙ A∙ M)
      (N∙ : Tm∙ Γ∙ B∙ N)
      → Tm∙ Γ∙ B∙ ⊢ snd∙ (pair∙ M∙ N∙) ≤[ β×₂ M N ] N∙
    η×∙ :
      {Γ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {P : Tm Γ (A ×ᵗʸ B)}
      (P∙ : Tm∙ Γ∙ (A∙ ×ᵗʸ∙ B∙) P)
      → Tm∙ Γ∙ (A∙ ×ᵗʸ∙ B∙)
          ⊢ pair∙ (fst∙ P∙) (snd∙ P∙) ≤[ η× P ] P∙

    _⇒ᵗʸ∙_ :
      {A B : Ty}
      → Ty∙ A → Ty∙ B → Ty∙ (A ⇒ᵗʸ B)
    lam∙ :
      {Γ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {N : Tm (Γ ▷ A) B}
      → Tm∙ (Γ∙ ▷∙ A∙) B∙ N
      → Tm∙ Γ∙ (A∙ ⇒ᵗʸ∙ B∙) (lam N)
    app∙ :
      {Γ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {F : Tm Γ (A ⇒ᵗʸ B)} {M : Tm Γ A}
      → Tm∙ Γ∙ (A∙ ⇒ᵗʸ∙ B∙) F
      → Tm∙ Γ∙ A∙ M
      → Tm∙ Γ∙ B∙ (app F M)
    lam[]∙ :
      {Γ Δ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {N : Tm (Δ ▷ A) B} {σ : Sub Γ Δ}
      (N∙ : Tm∙ (Δ∙ ▷∙ A∙) B∙ N)
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Tm∙ Γ∙ (A∙ ⇒ᵗʸ∙ B∙) (lam[] N σ i))
          (lam∙ N∙ [ σ∙ ]Tm∙)
          (lam∙ (N∙ [ lift∙ σ∙ ]Tm∙))
    app[]∙ :
      {Γ Δ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {Δ∙ : Ctx∙ Δ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {F : Tm Δ (A ⇒ᵗʸ B)} {M : Tm Δ A} {σ : Sub Γ Δ}
      (F∙ : Tm∙ Δ∙ (A∙ ⇒ᵗʸ∙ B∙) F)
      (M∙ : Tm∙ Δ∙ A∙ M)
      (σ∙ : Sub∙ Γ∙ Δ∙ σ)
      → PathP (λ i → Tm∙ Γ∙ B∙ (app[] F M σ i))
          (app∙ F∙ M∙ [ σ∙ ]Tm∙)
          (app∙ (F∙ [ σ∙ ]Tm∙) (M∙ [ σ∙ ]Tm∙))
    β⇒∙ :
      {Γ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {N : Tm (Γ ▷ A) B} {M : Tm Γ A}
      (N∙ : Tm∙ (Γ∙ ▷∙ A∙) B∙ N)
      (M∙ : Tm∙ Γ∙ A∙ M)
      → Tm∙ Γ∙ B∙ ⊢ app∙ (lam∙ N∙) M∙ ≤[ β⇒ N M ]
          (N∙ [ ⟨ id∙ , M∙ ⟩∙ ]Tm∙)
    η⇒∙ :
      {Γ : Ctx} {A B : Ty}
      {Γ∙ : Ctx∙ Γ} {A∙ : Ty∙ A} {B∙ : Ty∙ B}
      {F : Tm Γ (A ⇒ᵗʸ B)}
      (F∙ : Tm∙ Γ∙ (A∙ ⇒ᵗʸ∙ B∙) F)
      → Tm∙ Γ∙ (A∙ ⇒ᵗʸ∙ B∙)
          ⊢ lam∙ (app∙ (F∙ [ p∙ ]Tm∙) q∙) ≤[ η⇒ F ] F∙

constantDisplayed : {ℓCS ℓC ℓS ℓM : Level} {𝓒 : SimpleCwF ℓCS ℓC}
  → SimpleCwF ℓS ℓM → DisplayedSimpleCwF ℓS ℓM 𝓒
DisplayedSimpleCwF.Ctx∙ (constantDisplayed 𝓜) _ = SimpleCwF.Ctx 𝓜
DisplayedSimpleCwF.Ty∙ (constantDisplayed 𝓜) _ = SimpleCwF.Ty 𝓜
DisplayedSimpleCwF.Sub∙ (constantDisplayed 𝓜) Γ Δ _ = SimpleCwF.Sub 𝓜 Γ Δ
DisplayedSimpleCwF.Tm∙ (constantDisplayed 𝓜) Γ A _ = SimpleCwF.Tm 𝓜 Γ A
DisplayedSimpleCwF.id∙ (constantDisplayed 𝓜) = SimpleCwF.id 𝓜
DisplayedSimpleCwF._∘∙_ (constantDisplayed 𝓜) = SimpleCwF._∘_ 𝓜
DisplayedSimpleCwF.id-left∙ (constantDisplayed 𝓜) = SimpleCwF.id-left 𝓜
DisplayedSimpleCwF.id-right∙ (constantDisplayed 𝓜) = SimpleCwF.id-right 𝓜
DisplayedSimpleCwF.∘-assoc∙ (constantDisplayed 𝓜) = SimpleCwF.∘-assoc 𝓜
DisplayedSimpleCwF._[_]Tm∙ (constantDisplayed 𝓜) = SimpleCwF._[_]Tm 𝓜
DisplayedSimpleCwF.Tm-id∙ (constantDisplayed 𝓜) = SimpleCwF.Tm-id 𝓜
DisplayedSimpleCwF.Tm-∘∙ (constantDisplayed 𝓜) = SimpleCwF.Tm-∘ 𝓜
DisplayedSimpleCwF.ε∙ (constantDisplayed 𝓜) = SimpleCwF.ε 𝓜
DisplayedSimpleCwF.ε-sub∙ (constantDisplayed 𝓜) = SimpleCwF.ε-sub 𝓜
DisplayedSimpleCwF.εη∙ (constantDisplayed 𝓜) = SimpleCwF.εη 𝓜
DisplayedSimpleCwF._▷∙_ (constantDisplayed 𝓜) = SimpleCwF._▷_ 𝓜
DisplayedSimpleCwF.p∙ (constantDisplayed 𝓜) = SimpleCwF.p 𝓜
DisplayedSimpleCwF.q∙ (constantDisplayed 𝓜) = SimpleCwF.q 𝓜
DisplayedSimpleCwF.⟨_,_⟩∙ (constantDisplayed 𝓜) = SimpleCwF.⟨_,_⟩ 𝓜
DisplayedSimpleCwF.p-⟨⟩∙ (constantDisplayed 𝓜) = SimpleCwF.p-⟨⟩ 𝓜
DisplayedSimpleCwF.q-⟨⟩∙ (constantDisplayed 𝓜) = SimpleCwF.q-⟨⟩ 𝓜
DisplayedSimpleCwF.▷η∙ (constantDisplayed 𝓜) = SimpleCwF.▷η 𝓜
DisplayedSimpleCwF.⟨⟩-∘∙ (constantDisplayed 𝓜) = SimpleCwF.⟨⟩-∘ 𝓜
DisplayedSimpleCwF.Bool∙ (constantDisplayed 𝓜) = SimpleCwF.Bool 𝓜
DisplayedSimpleCwF.true∙ (constantDisplayed 𝓜) = SimpleCwF.true 𝓜
DisplayedSimpleCwF.false∙ (constantDisplayed 𝓜) = SimpleCwF.false 𝓜
DisplayedSimpleCwF.if∙ (constantDisplayed 𝓜) = SimpleCwF.if_then_else_ 𝓜
DisplayedSimpleCwF.true[]∙ (constantDisplayed 𝓜) = SimpleCwF.true[] 𝓜
DisplayedSimpleCwF.false[]∙ (constantDisplayed 𝓜) = SimpleCwF.false[] 𝓜
DisplayedSimpleCwF.if[]∙ (constantDisplayed 𝓜) = SimpleCwF.if[] 𝓜
DisplayedSimpleCwF.βif-true∙ (constantDisplayed 𝓜) = SimpleCwF.βif-true 𝓜
DisplayedSimpleCwF.βif-false∙ (constantDisplayed 𝓜) = SimpleCwF.βif-false 𝓜
DisplayedSimpleCwF._×ᵗʸ∙_ (constantDisplayed 𝓜) = SimpleCwF._×ᵗʸ_ 𝓜
DisplayedSimpleCwF.pair∙ (constantDisplayed 𝓜) = SimpleCwF.pair 𝓜
DisplayedSimpleCwF.fst∙ (constantDisplayed 𝓜) = SimpleCwF.fst 𝓜
DisplayedSimpleCwF.snd∙ (constantDisplayed 𝓜) = SimpleCwF.snd 𝓜
DisplayedSimpleCwF.pair[]∙ (constantDisplayed 𝓜) = SimpleCwF.pair[] 𝓜
DisplayedSimpleCwF.fst[]∙ (constantDisplayed 𝓜) = SimpleCwF.fst[] 𝓜
DisplayedSimpleCwF.snd[]∙ (constantDisplayed 𝓜) = SimpleCwF.snd[] 𝓜
DisplayedSimpleCwF._⇒ᵗʸ∙_ (constantDisplayed 𝓜) = SimpleCwF._⇒ᵗʸ_ 𝓜
DisplayedSimpleCwF.lam∙ (constantDisplayed 𝓜) = SimpleCwF.lam 𝓜
DisplayedSimpleCwF.app∙ (constantDisplayed 𝓜) = SimpleCwF.app 𝓜
DisplayedSimpleCwF.lam[]∙ (constantDisplayed 𝓜) = SimpleCwF.lam[] 𝓜
DisplayedSimpleCwF.app[]∙ (constantDisplayed 𝓜) = SimpleCwF.app[] 𝓜
DisplayedSimpleCwF.β⇒∙ (constantDisplayed 𝓜) = SimpleCwF.β⇒ 𝓜
DisplayedSimpleCwF.η⇒∙ (constantDisplayed 𝓜) = SimpleCwF.η⇒ 𝓜
DisplayedSimpleCwF.β×₁∙ (constantDisplayed 𝓜) = SimpleCwF.β×₁ 𝓜
DisplayedSimpleCwF.β×₂∙ (constantDisplayed 𝓜) = SimpleCwF.β×₂ 𝓜
DisplayedSimpleCwF.η×∙ (constantDisplayed 𝓜) = SimpleCwF.η× 𝓜

record DisplayedSection
  {ℓS ℓM ℓD₀ ℓD₁ : Level}
  {𝓒 : SimpleCwF ℓS ℓM}
  (𝓓 : DisplayedSimpleCwF ℓD₀ ℓD₁ 𝓒)
  : Type (ℓ-max (ℓ-max ℓS ℓM) (ℓ-max ℓD₀ ℓD₁)) where
  module C = SimpleCwF 𝓒
  module D = DisplayedSimpleCwF 𝓓

  field
    Ctxˢ : (Γ : C.Ctx) → D.Ctx∙ Γ
    Tyˢ  : (A : C.Ty) → D.Ty∙ A
    Subˢ :
      {Γ Δ : C.Ctx}
      (σ : C.Sub Γ Δ)
      → D.Sub∙ (Ctxˢ Γ) (Ctxˢ Δ) σ
    Tmˢ :
      {Γ : C.Ctx} {A : C.Ty}
      (M : C.Tm Γ A)
      → D.Tm∙ (Ctxˢ Γ) (Tyˢ A) M

module _ {ℓS ℓM ℓD₀ ℓD₁ : Level}
  {𝓒 : SimpleCwF ℓS ℓM}
  (𝓓 : DisplayedSimpleCwF ℓD₀ ℓD₁ 𝓒) where

  module C = SimpleCwF 𝓒
  module D = DisplayedSimpleCwF 𝓓

  TotalSimpleCwF : SimpleCwF (ℓ-max ℓS ℓD₀) (ℓ-max ℓM ℓD₁)
  SimpleCwF.Ctx TotalSimpleCwF =
    Σ C.Ctx D.Ctx∙
  SimpleCwF.Ty TotalSimpleCwF =
    Σ C.Ty D.Ty∙
  SimpleCwF.Sub TotalSimpleCwF Γ Δ =
    Σ (C.Sub (fst Γ) (fst Δ))
      (λ σ → D.Sub∙ (snd Γ) (snd Δ) σ)
  SimpleCwF.Tm TotalSimpleCwF Γ A =
    Σ (C.Tm (fst Γ) (fst A))
      (λ M → D.Tm∙ (snd Γ) (snd A) M)
  SimpleCwF.id TotalSimpleCwF {Γ = Γ} =
    C.id , D.id∙
  SimpleCwF._∘_ TotalSimpleCwF τ σ =
    C._∘_ (fst τ) (fst σ) , D._∘∙_ (snd τ) (snd σ)
  SimpleCwF.id-left TotalSimpleCwF σ =
    ΣPathP (C.id-left (fst σ) , D.id-left∙ (snd σ))
  SimpleCwF.id-right TotalSimpleCwF σ =
    ΣPathP (C.id-right (fst σ) , D.id-right∙ (snd σ))
  SimpleCwF.∘-assoc TotalSimpleCwF ρ τ σ =
    ΣPathP (C.∘-assoc (fst ρ) (fst τ) (fst σ)
      , D.∘-assoc∙ (snd ρ) (snd τ) (snd σ))
  SimpleCwF._[_]Tm TotalSimpleCwF M σ =
    C._[_]Tm (fst M) (fst σ) , D._[_]Tm∙ (snd M) (snd σ)
  SimpleCwF.Tm-id TotalSimpleCwF M =
    ΣPathP (C.Tm-id (fst M) , D.Tm-id∙ (snd M))
  SimpleCwF.Tm-∘ TotalSimpleCwF M τ σ =
    ΣPathP (C.Tm-∘ (fst M) (fst τ) (fst σ)
      , D.Tm-∘∙ (snd M) (snd τ) (snd σ))
  SimpleCwF.ε TotalSimpleCwF =
    C.ε , D.ε∙
  SimpleCwF.ε-sub TotalSimpleCwF =
    C.ε-sub , D.ε-sub∙
  SimpleCwF.εη TotalSimpleCwF σ =
    ΣPathP (C.εη (fst σ) , D.εη∙ (snd σ))
  SimpleCwF._▷_ TotalSimpleCwF Γ A =
    C._▷_ (fst Γ) (fst A) , D._▷∙_ (snd Γ) (snd A)
  SimpleCwF.p TotalSimpleCwF =
    C.p , D.p∙
  SimpleCwF.q TotalSimpleCwF =
    C.q , D.q∙
  SimpleCwF.⟨_,_⟩ TotalSimpleCwF σ M =
    C.⟨_,_⟩ (fst σ) (fst M) , D.⟨_,_⟩∙ (snd σ) (snd M)
  SimpleCwF.p-⟨⟩ TotalSimpleCwF σ M =
    ΣPathP (C.p-⟨⟩ (fst σ) (fst M)
      , D.p-⟨⟩∙ (snd σ) (snd M))
  SimpleCwF.q-⟨⟩ TotalSimpleCwF σ M =
    ΣPathP (C.q-⟨⟩ (fst σ) (fst M)
      , D.q-⟨⟩∙ (snd σ) (snd M))
  SimpleCwF.▷η TotalSimpleCwF =
    ΣPathP (C.▷η , D.▷η∙)
  SimpleCwF.⟨⟩-∘ TotalSimpleCwF σ M ρ =
    ΣPathP (C.⟨⟩-∘ (fst σ) (fst M) (fst ρ)
      , D.⟨⟩-∘∙ (snd σ) (snd M) (snd ρ))
  SimpleCwF.Bool TotalSimpleCwF =
    C.Bool , D.Bool∙
  SimpleCwF.true TotalSimpleCwF =
    C.true , D.true∙
  SimpleCwF.false TotalSimpleCwF =
    C.false , D.false∙
  SimpleCwF.if_then_else_ TotalSimpleCwF B T F =
    C.if_then_else_ (fst B) (fst T) (fst F)
    , D.if∙ (snd B) (snd T) (snd F)
  SimpleCwF.true[] TotalSimpleCwF σ =
    ΣPathP (C.true[] (fst σ) , D.true[]∙ (snd σ))
  SimpleCwF.false[] TotalSimpleCwF σ =
    ΣPathP (C.false[] (fst σ) , D.false[]∙ (snd σ))
  SimpleCwF.if[] TotalSimpleCwF B T F σ =
    ΣPathP (C.if[] (fst B) (fst T) (fst F) (fst σ)
      , D.if[]∙ (snd B) (snd T) (snd F) (snd σ))
  SimpleCwF.βif-true TotalSimpleCwF T F =
    Σ≤ (C.βif-true (fst T) (fst F))
      (D.βif-true∙ (snd T) (snd F))
  SimpleCwF.βif-false TotalSimpleCwF T F =
    Σ≤ (C.βif-false (fst T) (fst F))
      (D.βif-false∙ (snd T) (snd F))
  SimpleCwF._×ᵗʸ_ TotalSimpleCwF A B =
    C._×ᵗʸ_ (fst A) (fst B) , D._×ᵗʸ∙_ (snd A) (snd B)
  SimpleCwF.pair TotalSimpleCwF M N =
    C.pair (fst M) (fst N) , D.pair∙ (snd M) (snd N)
  SimpleCwF.fst TotalSimpleCwF P =
    C.fst (fst P) , D.fst∙ (snd P)
  SimpleCwF.snd TotalSimpleCwF P =
    C.snd (fst P) , D.snd∙ (snd P)
  SimpleCwF.pair[] TotalSimpleCwF M N σ =
    ΣPathP (C.pair[] (fst M) (fst N) (fst σ)
      , D.pair[]∙ (snd M) (snd N) (snd σ))
  SimpleCwF.fst[] TotalSimpleCwF P σ =
    ΣPathP (C.fst[] (fst P) (fst σ)
      , D.fst[]∙ (snd P) (snd σ))
  SimpleCwF.snd[] TotalSimpleCwF P σ =
    ΣPathP (C.snd[] (fst P) (fst σ)
      , D.snd[]∙ (snd P) (snd σ))
  SimpleCwF._⇒ᵗʸ_ TotalSimpleCwF A B =
    C._⇒ᵗʸ_ (fst A) (fst B) , D._⇒ᵗʸ∙_ (snd A) (snd B)
  SimpleCwF.lam TotalSimpleCwF N =
    C.lam (fst N) , D.lam∙ (snd N)
  SimpleCwF.app TotalSimpleCwF F M =
    C.app (fst F) (fst M) , D.app∙ (snd F) (snd M)
  SimpleCwF.lam[] TotalSimpleCwF N σ =
    ΣPathP (C.lam[] (fst N) (fst σ)
      , D.lam[]∙ (snd N) (snd σ))
  SimpleCwF.app[] TotalSimpleCwF F M σ =
    ΣPathP (C.app[] (fst F) (fst M) (fst σ)
      , D.app[]∙ (snd F) (snd M) (snd σ))
  SimpleCwF.β⇒ TotalSimpleCwF N M =
    Σ≤ (C.β⇒ (fst N) (fst M))
      (D.β⇒∙ (snd N) (snd M))
  SimpleCwF.η⇒ TotalSimpleCwF F =
    Σ≤ (C.η⇒ (fst F))
      (D.η⇒∙ (snd F))
  SimpleCwF.β×₁ TotalSimpleCwF M N =
    Σ≤ (C.β×₁ (fst M) (fst N))
      (D.β×₁∙ (snd M) (snd N))
  SimpleCwF.β×₂ TotalSimpleCwF M N =
    Σ≤ (C.β×₂ (fst M) (fst N))
      (D.β×₂∙ (snd M) (snd N))
  SimpleCwF.η× TotalSimpleCwF P =
    Σ≤ (C.η× (fst P))
      (D.η×∙ (snd P))
