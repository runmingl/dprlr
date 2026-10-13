module DPRLR.Gluing.FTLR where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base renaming (Bool to Bool₂)
open import Cubical.Data.Unit

open import DPRLR.Simplicial.Hom
open import DPRLR.Object.Model.Morphism.Base
open import DPRLR.Object.Syntax.Localized
open import DPRLR.Object.Syntax.Model
open import DPRLR.Object.Syntax.Initiality
open import DPRLR.Object.Syntax.Raw using (ε ; Bool)
open import DPRLR.Gluing.LogicalRelations.Bool SyntaxModel using (⌜_⌝ ; BOOL∙)

open import DPRLR.Gluing.GluingModel SyntaxModel

ftlr-section :
  Σ[ ι ∈ SimpleMorphism SyntaxModel GluingCwF ]
    (projectGluingMorphism ι ≡ identityMorphism SyntaxModel)
ftlr-section =
  fst (syntax-isInitial _ _ GluingCwF) , isContr→isProp (syntax-isInitial _ _ SyntaxModel) _ _

private
  closedBool : SimpleMorphism SyntaxModel SyntaxModel → Tmᴾ ε Bool → Tmᴾ ε Bool
  closedBool f t = transport (λ i → Tmᴾ (F.εᶠ i) (F.Boolᶠ i)) (F.Tmᶠ t)
    where module F = SimpleMorphism f

bool-canonicityᴾ : (M : Tmᴾ ε Bool) → Σ Bool₂ (λ b → M ≤ ⌜ b ⌝)
bool-canonicityᴾ M = subst BOOL∙
  ( GluTm.M° glued [ idᴾ ]Tmᴾ
  ≡⟨ Tmᴾ-id (GluTm.M° glued) ⟩
    GluTm.M° glued
  ≡⟨ cong (λ f → closedBool f M) (snd ftlr-section) ⟩
    closedBool (identityMorphism SyntaxModel) M
  ≡⟨ transportRefl M ⟩
    M
  ∎)
  (GluTm.M∙ glued idᴾ tt*)
  where
  module I = SimpleMorphism (fst ftlr-section)
    
  glued : GluTm εᵍ BOOL
  glued = transport (λ i → GluTm (I.εᶠ i) (I.Boolᶠ i)) (I.Tmᶠ M)
