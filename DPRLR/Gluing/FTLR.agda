module DPRLR.Gluing.FTLR where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base renaming (Bool to Bool₂)
open import Cubical.Data.Unit

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.PreorderLocalization using (⌞_⌟)
open import DPRLR.Object.Model.Model
open import DPRLR.Object.Model.Morphism.Base
open import DPRLR.Object.Syntax.Localized
open import DPRLR.Object.Syntax.Model
open import DPRLR.Object.Syntax.Initiality
open import DPRLR.Object.Syntax.Raw using (ε ; Bool)
open import DPRLR.Gluing.LogicalRelations.Bool SyntaxModel using (⌜_⌝)

module _ {ℓS ℓM : Level} (𝓜 : SimpleCwF ℓS ℓM) where
  open import DPRLR.Gluing.GluingModel 𝓜
  private
    module M = SimpleCwF 𝓜

  record FTLRSection {ℓAS ℓA : Level} {𝓐 : SimpleCwF ℓAS ℓA}
    (f : SimpleMorphism 𝓐 𝓜)
    : Type (ℓ-max (ℓ-max ℓAS ℓA) (ℓ-max ℓS (ℓ-suc ℓM))) where
    private
      module A = SimpleCwF 𝓐
      module F = SimpleMorphism f
    field
      Ctxˢ : (Γ : A.Ctx) → Σ[ Γᵍ ∈ GluCtx ] (GluCtx.Γ° Γᵍ ≡ F.Ctxᶠ Γ)
      Tyˢ : (B : A.Ty) → Σ[ Bᵍ ∈ GluTy ] (GluTy.A° Bᵍ ≡ F.Tyᶠ B)
      Subˢ : {Γ Δ : A.Ctx} (σ : ⌞ A.Sub Γ Δ ⌟)
        → Σ[ σᵍ ∈ GluSub (fst (Ctxˢ Γ)) (fst (Ctxˢ Δ)) ]
          PathP (λ i → ⌞ M.Sub (snd (Ctxˢ Γ) i) (snd (Ctxˢ Δ) i) ⌟)
            (GluSub.σ° σᵍ) (F.Subᶠ σ)
      Tmˢ : {Γ : A.Ctx} {B : A.Ty} (t : ⌞ A.Tm Γ B ⌟)
        → Σ[ tᵍ ∈ GluTm (fst (Ctxˢ Γ)) (fst (Tyˢ B)) ]
          PathP (λ i → ⌞ M.Tm (snd (Ctxˢ Γ) i) (snd (Tyˢ B) i) ⌟)
            (GluTm.M° tᵍ) (F.Tmᶠ t)

  sectionFromGluing : {ℓAS ℓA : Level} {𝓐 : SimpleCwF ℓAS ℓA}
    → (f : SimpleMorphism 𝓐 GluingCwF)
    → FTLRSection (projectGluingMorphism f)
  sectionFromGluing f = record
    { Ctxˢ = λ Γ → F.Ctxᶠ Γ , refl
    ; Tyˢ = λ A → F.Tyᶠ A , refl
    ; Subˢ = λ σ → F.Subᶠ σ , refl
    ; Tmˢ = λ t → F.Tmᶠ t , refl
    }
    where module F = SimpleMorphism f

open import DPRLR.Gluing.GluingModel SyntaxModel

ftlr-morphism : SimpleMorphism SyntaxModel GluingCwF
ftlr-morphism = fst (syntax-isInitial _ _ GluingCwF)

ftlr-over-id : projectGluingMorphism ftlr-morphism ≡ identityMorphism SyntaxModel
ftlr-over-id =
    projectGluingMorphism ftlr-morphism
  ≡⟨ sym (snd initial (projectGluingMorphism ftlr-morphism)) ⟩
    fst initial
  ≡⟨ snd initial (identityMorphism SyntaxModel) ⟩
    identityMorphism SyntaxModel 
  ∎
  where
  initial = syntax-isInitial _ _ SyntaxModel

ftlr-section : FTLRSection SyntaxModel (identityMorphism SyntaxModel)
ftlr-section = subst (FTLRSection SyntaxModel) ftlr-over-id
  (sectionFromGluing SyntaxModel ftlr-morphism)

private
  module G = SimpleMorphism ftlr-morphism

  closedBool : SimpleMorphism SyntaxModel SyntaxModel → Tmᴾ ε Bool → Tmᴾ ε Bool
  closedBool f t = transport (λ i → Tmᴾ (F.εᶠ i) (F.Boolᶠ i)) (F.Tmᶠ t)
    where module F = SimpleMorphism f

bool-canonicityᴾ : (M : Tmᴾ ε Bool) → Σ Bool₂ (λ b → M ≤ ⌜ b ⌝)
bool-canonicityᴾ M = subst (λ u → Σ Bool₂ (λ b → u ≤ ⌜ b ⌝))
  ( GluTm.M° glued [ idᴾ ]Tmᴾ
  ≡⟨ Tmᴾ-id (GluTm.M° glued) ⟩
    GluTm.M° glued
  ≡⟨ cong (λ f → closedBool f M) ftlr-over-id ⟩
    closedBool (identityMorphism SyntaxModel) M
  ≡⟨ transportRefl M ⟩
    M 
  ∎) 
  (GluTm.M∙ glued idᴾ tt*)
  where
  glued : GluTm εᵍ BOOL
  glued = transport (λ i → GluTm (G.εᶠ i) (G.Boolᶠ i)) (G.Tmᶠ M)
