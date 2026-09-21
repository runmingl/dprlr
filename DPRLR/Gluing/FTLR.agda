module DPRLR.Gluing.FTLR where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool.Base renaming (Bool to Bool₂)
open import Cubical.Data.Unit

open import DPRLR.Simplicial.Hom
open import DPRLR.Object.Model.DisplayedModel
open import DPRLR.Object.Syntax.Localized.Base
open import DPRLR.Object.Syntax.Localized.Model
open import DPRLR.Object.Syntax.Localized.Displayed
open import DPRLR.Object.Syntax.Raw.Base
open import DPRLR.Gluing.LogicalRelations.Bool
open import DPRLR.Gluing.DisplayedModel

ftlr-section : DisplayedSection (GluingDisplayed LocalizedSyntaxModel)
ftlr-section = syntax-elim-displayed (GluingDisplayedDirected LocalizedSyntaxModel)

bool-canonicityᴾ :
  (M : Tmᴾ ε Bool)
  → Σ Bool₂ (λ b → M ≤ ⌜_⌝ LocalizedSyntaxModel b)
bool-canonicityᴾ M =
  subst (λ N → Σ Bool₂ (λ b → N ≤ ⌜_⌝ LocalizedSyntaxModel b)) (Tmᴾ-id M)
    (syntax-elim-closedBool (GluingDisplayedDirected LocalizedSyntaxModel) M idᴾ tt*)
