module DPRLR.Object.Syntax.Localized.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (fst ; snd)

open import DPRLR.Object.Model.Model using (SimpleCwF)
open import DPRLR.Object.Model.DisplayedModel
  using (DisplayedSimpleCwF ; DisplayedSimpleDirectedCwF ; DisplayedSection
        ; TotalSimpleCwF ; projectMorphism)
open import DPRLR.Object.Model.Morphism.Base using (SimpleMorphism ; identityMorphism)
open import DPRLR.Object.Syntax.Localized.Base
open import DPRLR.Object.Syntax.Localized.Model
open import DPRLR.Object.Syntax.Initiality.Localized using (localized-syntax-isInitial)
import DPRLR.Object.Syntax.Raw.Base as Raw

private
  module SectionConstruction {ℓS ℓM ℓD₀ ℓD₁ : Level} {𝓒 : SimpleCwF ℓS ℓM}
    (𝓓 : DisplayedSimpleCwF ℓD₀ ℓD₁ 𝓒) where
    module C = SimpleCwF 𝓒
    module D = DisplayedSimpleCwF 𝓓

    module _ (f : SimpleMorphism 𝓒 (TotalSimpleCwF 𝓓))
      (projection : projectMorphism 𝓓 f ≡ identityMorphism 𝓒) where
      private
        module F = SimpleMorphism f
        module P (i : I) = SimpleMorphism (projection i)

        ctx-path : (Γ : C.Ctx) → PathP (λ i → D.Ctx∙ (P.Ctxᶠ i Γ))
          (snd (F.Ctxᶠ Γ)) (subst D.Ctx∙ (λ i → P.Ctxᶠ i Γ) (snd (F.Ctxᶠ Γ)))
        ctx-path Γ = subst-filler D.Ctx∙ (λ i → P.Ctxᶠ i Γ) (snd (F.Ctxᶠ Γ))

        ty-path : (A : C.Ty) → PathP (λ i → D.Ty∙ (P.Tyᶠ i A))
          (snd (F.Tyᶠ A)) (subst D.Ty∙ (λ i → P.Tyᶠ i A) (snd (F.Tyᶠ A)))
        ty-path A = subst-filler D.Ty∙ (λ i → P.Tyᶠ i A) (snd (F.Tyᶠ A))

      sectionOfMorphism : DisplayedSection 𝓓
      DisplayedSection.Ctxˢ sectionOfMorphism Γ = ctx-path Γ i1
      DisplayedSection.Tyˢ sectionOfMorphism A = ty-path A i1
      DisplayedSection.Subˢ sectionOfMorphism {Γ} {Δ} σ = transport
        (λ i → D.Sub∙ (ctx-path Γ i) (ctx-path Δ i) (P.Subᶠ i σ)) (snd (F.Subᶠ σ))
      DisplayedSection.Tmˢ sectionOfMorphism {Γ} {A} t = transport
        (λ i → D.Tm∙ (ctx-path Γ i) (ty-path A i) (P.Tmᶠ i t)) (snd (F.Tmᶠ t))

      sectionOfMorphism-ε : DisplayedSection.Ctxˢ sectionOfMorphism C.ε ≡ D.ε∙
      sectionOfMorphism-ε =
          ctx-path C.ε i1
        ≡⟨ sym (substRefl {B = D.Ctx∙} _) ⟩
          subst D.Ctx∙ refl (ctx-path C.ε i1)
        ≡⟨ sym (λ i → subst D.Ctx∙ (P.εᶠ i) (ctx-path C.ε i)) ⟩
          subst D.Ctx∙ (cong fst F.εᶠ) (snd (F.Ctxᶠ C.ε))
        ≡⟨ fromPathP (λ i → snd (F.εᶠ i)) ⟩
          D.ε∙
        ∎

      sectionOfMorphism-Bool : DisplayedSection.Tyˢ sectionOfMorphism C.Bool ≡ D.Bool∙
      sectionOfMorphism-Bool =
          ty-path C.Bool i1
        ≡⟨ sym (substRefl {B = D.Ty∙} _) ⟩
          subst D.Ty∙ refl (ty-path C.Bool i1)
        ≡⟨ sym (λ i → subst D.Ty∙ (P.Boolᶠ i) (ty-path C.Bool i)) ⟩
          subst D.Ty∙ (cong fst F.Boolᶠ) (snd (F.Tyᶠ C.Bool))
        ≡⟨ fromPathP (λ i → snd (F.Boolᶠ i)) ⟩
          D.Bool∙
        ∎

      sectionOfMorphism-closedBool : (t : C.Tm C.ε C.Bool) → D.Tm∙ D.ε∙ D.Bool∙ t
      sectionOfMorphism-closedBool t = transport
        (λ i → D.Tm∙ (sectionOfMorphism-ε i) (sectionOfMorphism-Bool i) t)
        (DisplayedSection.Tmˢ sectionOfMorphism t)


module _ {ℓD₀ ℓD₁ : Level}
  (𝓓 : DisplayedSimpleDirectedCwF ℓD₀ ℓD₁ LocalizedSyntaxModel) where
  private
    module D = DisplayedSimpleDirectedCwF 𝓓

    f : SimpleMorphism LocalizedSyntaxCwF (TotalSimpleCwF D.displayed)
    f = (localized-syntax-isInitial ℓD₀ ℓD₁ D.total) .fst

    projection : projectMorphism D.displayed f ≡ identityMorphism LocalizedSyntaxCwF
    projection = isContr→isProp (localized-syntax-isInitial ℓ-zero ℓ-zero LocalizedSyntaxModel)
      (projectMorphism D.displayed f) (identityMorphism LocalizedSyntaxCwF)

  syntax-elim-displayed : DisplayedSection D.displayed
  syntax-elim-displayed = SectionConstruction.sectionOfMorphism D.displayed f projection

  syntax-elim-closedBool : (t : Tmᴾ Raw.ε Raw.Bool) → D.Tm∙ D.ε∙ D.Bool∙ t
  syntax-elim-closedBool = SectionConstruction.sectionOfMorphism-closedBool D.displayed f projection
