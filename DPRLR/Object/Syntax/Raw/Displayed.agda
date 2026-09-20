module DPRLR.Object.Syntax.Raw.Displayed where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import Cubical.Data.Sigma using () renaming (fst to proj₁ ; snd to proj₂)

open import DPRLR.Object.Model.DisplayedModel
open import DPRLR.Object.Syntax.Raw.Model
open import DPRLR.Object.Syntax.Raw.Base

module _ {ℓD₀ ℓD₁ : Level}
  (𝓓 : DisplayedSimpleCwF ℓD₀ ℓD₁ RawSyntaxCwF) where

  open DisplayedSimpleCwF 𝓓

  mutual
    Ctxˢ : (Γ : Ctx) → Ctx∙ Γ
    Ctxˢ ε = ε∙
    Ctxˢ (Γ ▷ A) = Ctxˢ Γ ▷∙ Tyˢ A

    Tyˢ : (A : Ty) → Ty∙ A
    Tyˢ Bool = Bool∙
    Tyˢ (A ×ᵗʸ B) = Tyˢ A ×ᵗʸ∙ Tyˢ B
    Tyˢ (A ⇒ᵗʸ B) = Tyˢ A ⇒ᵗʸ∙ Tyˢ B

    Subˢ :
      {Γ Δ : Ctx}
      (σ : Sub Γ Δ)
      → Sub∙ (Ctxˢ Γ) (Ctxˢ Δ) σ
    Subˢ id = id∙
    Subˢ (τ ∘ σ) = Subˢ τ ∘∙ Subˢ σ
    Subˢ ε-sub = ε-sub∙
    Subˢ (εη σ i) = εη∙ (Subˢ σ) i
    Subˢ p = p∙
    Subˢ ⟨ σ , M ⟩ = ⟨ Subˢ σ , Tmˢ M ⟩∙
    Subˢ (id-left σ i) = id-left∙ (Subˢ σ) i
    Subˢ (id-right σ i) = id-right∙ (Subˢ σ) i
    Subˢ (∘-assoc ρ τ σ i) = ∘-assoc∙ (Subˢ ρ) (Subˢ τ) (Subˢ σ) i
    Subˢ (p-⟨⟩ σ M i) = p-⟨⟩∙ (Subˢ σ) (Tmˢ M) i
    Subˢ (▷η i) = ▷η∙ i
    Subˢ (⟨⟩-∘ σ M ρ i) = ⟨⟩-∘∙ (Subˢ σ) (Tmˢ M) (Subˢ ρ) i

    Tmˢ :
      {Γ : Ctx} {A : Ty}
      (M : Tm Γ A)
      → Tm∙ (Ctxˢ Γ) (Tyˢ A) M
    Tmˢ qᶜ = q∙
    Tmˢ (substTmᶜ M σ) = Tmˢ M [ Subˢ σ ]Tm∙
    Tmˢ (Tm-id M i) = Tm-id∙ (Tmˢ M) i
    Tmˢ (Tm-∘ M τ σ i) = Tm-∘∙ (Tmˢ M) (Subˢ τ) (Subˢ σ) i
    Tmˢ (q-⟨⟩ σ M i) = q-⟨⟩∙ (Subˢ σ) (Tmˢ M) i
    Tmˢ true = true∙
    Tmˢ false = false∙
    Tmˢ (if B then T else F) = if∙ (Tmˢ B) (Tmˢ T) (Tmˢ F)
    Tmˢ (true[] σ i) = true[]∙ (Subˢ σ) i
    Tmˢ (false[] σ i) = false[]∙ (Subˢ σ) i
    Tmˢ (if[] B T F σ i) =
      if[]∙ (Tmˢ B) (Tmˢ T) (Tmˢ F) (Subˢ σ) i
    Tmˢ (pair M N) = pair∙ (Tmˢ M) (Tmˢ N)
    Tmˢ (fst P) = fst∙ (Tmˢ P)
    Tmˢ (snd P) = snd∙ (Tmˢ P)
    Tmˢ (pair[] M N σ i) = pair[]∙ (Tmˢ M) (Tmˢ N) (Subˢ σ) i
    Tmˢ (fst[] P σ i) = fst[]∙ (Tmˢ P) (Subˢ σ) i
    Tmˢ (snd[] P σ i) = snd[]∙ (Tmˢ P) (Subˢ σ) i
    Tmˢ (lam N) = lam∙ (Tmˢ N)
    Tmˢ (app F M) = app∙ (Tmˢ F) (Tmˢ M)
    Tmˢ (lam[] N σ i) = lam[]∙ (Tmˢ N) (Subˢ σ) i
    Tmˢ (app[] F M σ i) = app[]∙ (Tmˢ F) (Tmˢ M) (Subˢ σ) i
    Tmˢ (βif-true-rel T F i) = proj₁ (βif-true∙ (Tmˢ T) (Tmˢ F)) i
    Tmˢ (βif-true-left T F i) = proj₁ (proj₂ (βif-true∙ (Tmˢ T) (Tmˢ F))) i
    Tmˢ (βif-true-right T F i) = proj₂ (proj₂ (βif-true∙ (Tmˢ T) (Tmˢ F))) i
    Tmˢ (βif-false-rel T F i) = proj₁ (βif-false∙ (Tmˢ T) (Tmˢ F)) i
    Tmˢ (βif-false-left T F i) = proj₁ (proj₂ (βif-false∙ (Tmˢ T) (Tmˢ F))) i
    Tmˢ (βif-false-right T F i) = proj₂ (proj₂ (βif-false∙ (Tmˢ T) (Tmˢ F))) i
    Tmˢ (β×₁-rel M N i) = proj₁ (β×₁∙ (Tmˢ M) (Tmˢ N)) i
    Tmˢ (β×₁-left M N i) = proj₁ (proj₂ (β×₁∙ (Tmˢ M) (Tmˢ N))) i
    Tmˢ (β×₁-right M N i) = proj₂ (proj₂ (β×₁∙ (Tmˢ M) (Tmˢ N))) i
    Tmˢ (β×₂-rel M N i) = proj₁ (β×₂∙ (Tmˢ M) (Tmˢ N)) i
    Tmˢ (β×₂-left M N i) = proj₁ (proj₂ (β×₂∙ (Tmˢ M) (Tmˢ N))) i
    Tmˢ (β×₂-right M N i) = proj₂ (proj₂ (β×₂∙ (Tmˢ M) (Tmˢ N))) i
    Tmˢ (η×-rel P i) = proj₁ (η×∙ (Tmˢ P)) i
    Tmˢ (η×-left P i) = proj₁ (proj₂ (η×∙ (Tmˢ P))) i
    Tmˢ (η×-right P i) = proj₂ (proj₂ (η×∙ (Tmˢ P))) i
    Tmˢ (β⇒-rel N M i) = proj₁ (β⇒∙ (Tmˢ N) (Tmˢ M)) i
    Tmˢ (β⇒-left N M i) = proj₁ (proj₂ (β⇒∙ (Tmˢ N) (Tmˢ M))) i
    Tmˢ (β⇒-right N M i) = proj₂ (proj₂ (β⇒∙ (Tmˢ N) (Tmˢ M))) i
    Tmˢ (η⇒-rel F i) = proj₁ (η⇒∙ (Tmˢ F)) i
    Tmˢ (η⇒-left F i) = proj₁ (proj₂ (η⇒∙ (Tmˢ F))) i
    Tmˢ (η⇒-right F i) = proj₂ (proj₂ (η⇒∙ (Tmˢ F))) i

  syntax-elim-displayed : DisplayedSection 𝓓
  DisplayedSection.Ctxˢ syntax-elim-displayed = Ctxˢ
  DisplayedSection.Tyˢ syntax-elim-displayed = Tyˢ
  DisplayedSection.Subˢ syntax-elim-displayed = Subˢ
  DisplayedSection.Tmˢ syntax-elim-displayed = Tmˢ
