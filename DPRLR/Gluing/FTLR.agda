module DPRLR.Gluing.FTLR where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import Cubical.Data.Bool.Base using () renaming (Bool to Bool₂)
open import Cubical.Data.Sigma hiding (Sub ; fst ; snd)
open import Cubical.Data.Unit

open import DPRLR.Simplicial.Hom
open import DPRLR.Object.Simple.Displayed
open import DPRLR.Object.Simple.Syntax.LocalizedSyntax
open import DPRLR.Object.Simple.Syntax.LocalizedModel
open import DPRLR.Object.Simple.Syntax.LocalizedDisplayedBridge
import DPRLR.Object.Simple.Syntax.Base as Raw
open import DPRLR.Object.Simple.Syntax.Displayed
open import DPRLR.Gluing.Simple.Bool
open import DPRLR.Gluing.DisplayedModel

ftlr-section :
  DisplayedSection
    (ηDisplayedSimpleCwF (GluingDisplayed LocalizedSyntaxModel))
ftlr-section =
  syntax-elim-displayed
    (ηDisplayedSimpleCwF (GluingDisplayed LocalizedSyntaxModel))

bool-canonicity :
  (M : Raw.Tm Raw.ε Raw.Bool)
  → Σ Bool₂ (λ b → ηTmᴾ M ≤ ⌜_⌝ LocalizedSyntaxModel b)
bool-canonicity M =
  subst
      (λ N → Σ Bool₂ (λ b → N ≤ ⌜_⌝ LocalizedSyntaxModel b))
      (Tmᴾ-id (ηTmᴾ M))
      (DisplayedSection.Tmˢ ftlr-section M idᴾ tt*)
