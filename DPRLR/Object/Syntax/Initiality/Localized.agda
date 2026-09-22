module DPRLR.Object.Syntax.Initiality.Localized where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; invEquiv)
open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv)
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv)

open import DPRLR.Simplicial.PreorderLocalization
open import DPRLR.Object.Model.Model using (SimpleCwF ; SimpleDirectedCwF)
open import DPRLR.Object.Model.Morphism.Base
  using (SortMorphism ; MorphismOver ; SimpleMorphism ; simple-morphism ; isInitialDirected)
open import DPRLR.Object.Model.Morphism.Properties
open import DPRLR.Object.Syntax.Raw.Model
open import DPRLR.Object.Syntax.Localized.Base
open import DPRLR.Object.Syntax.Localized.Model
open import DPRLR.Object.Syntax.Initiality.Raw using (raw-syntax-isInitial)
import DPRLR.Object.Syntax.Raw.Base as R

--    
--                           η
--                 Raw ─────────→ Localized
--                    ╲              │
--                      ╲            │
--     restrictMorphism f ╲          │ f
--                          ╲        │
--                            ╲      │
--                              ╲    │
--                                ↘  ↓
--                                   𝓜
--    
restrictMorphism : {ℓS ℓM : Level} {𝓜 : SimpleCwF ℓS ℓM}
  → SimpleMorphism LocalizedSyntaxCwF 𝓜 → SimpleMorphism RawSyntaxCwF 𝓜
restrictMorphism f =
  record
    { sorts = record
      { Tyᶠ = F.Tyᶠ ; Ctxᶠ = F.Ctxᶠ ; Boolᶠ = F.Boolᶠ
      ; ×ᶠ = F.×ᶠ ; ⇒ᶠ = F.⇒ᶠ ; εᶠ = F.εᶠ ; ▷ᶠ = F.▷ᶠ }
    ; over = record
      { Subᶠ = λ σ → F.Subᶠ (ηSubᴾ σ) ; Tmᶠ = λ t → F.Tmᶠ (ηTmᴾ t)
      ; idᶠ = F.idᶠ ; ∘ᶠ = λ τ σ → F.∘ᶠ (ηSubᴾ τ) (ηSubᴾ σ)
      ; ε-subᶠ = F.ε-subᶠ ; pᶠ = F.pᶠ ; qᶠ = F.qᶠ
      ; ⟨⟩ᶠ = λ σ t → F.⟨⟩ᶠ (ηSubᴾ σ) (ηTmᴾ t)
      ; []ᶠ = λ t σ → F.[]ᶠ (ηTmᴾ t) (ηSubᴾ σ)
      ; trueᶠ = F.trueᶠ ; falseᶠ = F.falseᶠ
      ; ifᶠ = λ b t u → F.ifᶠ (ηTmᴾ b) (ηTmᴾ t) (ηTmᴾ u)
      ; pairᶠ = λ t u → F.pairᶠ (ηTmᴾ t) (ηTmᴾ u)
      ; fstᶠ = λ t → F.fstᶠ (ηTmᴾ t)
      ; sndᶠ = λ t → F.sndᶠ (ηTmᴾ t)
      ; lamᶠ = λ t → F.lamᶠ (ηTmᴾ t)
      ; appᶠ = λ t u → F.appᶠ (ηTmᴾ t) (ηTmᴾ u)
      }
    }
  where
  module F = SimpleMorphism f

module _ {ℓS ℓM : Level} (𝓜 : SimpleDirectedCwF ℓS ℓM) where
  private
    module M = SimpleDirectedCwF 𝓜

  extendMorphism : SimpleMorphism RawSyntaxCwF M.cwf
    → SimpleMorphism LocalizedSyntaxCwF M.cwf
  extendMorphism f = simple-morphism sorts over
    where
    module F = SimpleMorphism f

    Subᶠ : {Γ Δ : R.Ctx} → Subᴾ Γ Δ → M.Sub (F.Ctxᶠ Γ) (F.Ctxᶠ Δ)
    Subᶠ = rec (M.sub-local _ _) F.Subᶠ

    Tmᶠ : {Γ : R.Ctx} {A : R.Ty} → Tmᴾ Γ A → M.Tm (F.Ctxᶠ Γ) (F.Tyᶠ A)
    Tmᶠ = rec (M.tm-local _ _) F.Tmᶠ

    sorts : SortMorphism LocalizedSyntaxCwF M.cwf
    sorts = record
      { Tyᶠ = F.Tyᶠ ; Ctxᶠ = F.Ctxᶠ ; Boolᶠ = F.Boolᶠ
      ; ×ᶠ = F.×ᶠ ; ⇒ᶠ = F.⇒ᶠ ; εᶠ = F.εᶠ ; ▷ᶠ = F.▷ᶠ }

    over : MorphismOver LocalizedSyntaxCwF M.cwf sorts
    MorphismOver.Subᶠ over = Subᶠ
    MorphismOver.Tmᶠ over = Tmᶠ
    MorphismOver.idᶠ over = F.idᶠ
    MorphismOver.∘ᶠ over = rec-unique₂ (M.sub-local _ _)
      (λ τ σ → Subᶠ (τ ∘ᴾ σ)) (λ τ σ → Subᶠ τ M.∘ Subᶠ σ) F.∘ᶠ
    MorphismOver.ε-subᶠ over = F.ε-subᶠ
    MorphismOver.pᶠ over = F.pᶠ
    MorphismOver.qᶠ over = F.qᶠ
    MorphismOver.⟨⟩ᶠ over =
      rec-uniqueP₂ (M.sub-local _ _)
        (λ σ t → Subᶠ ⟨ σ , t ⟩ᴾ) (λ σ t → M.⟨ Subᶠ σ , Tmᶠ t ⟩) F.⟨⟩ᶠ
    MorphismOver.[]ᶠ over = rec-unique₂ (M.tm-local _ _) (λ t σ → Tmᶠ (t [ σ ]Tmᴾ)) (λ t σ → Tmᶠ t M.[ Subᶠ σ ]Tm) F.[]ᶠ
    MorphismOver.trueᶠ over = F.trueᶠ
    MorphismOver.falseᶠ over = F.falseᶠ
    MorphismOver.ifᶠ over = rec-unique₃ (M.tm-local _ _)
      (λ b t u → Tmᶠ (ifᴾ b t u))
      (λ b t u → M.if subst (M.Tm _) F.Boolᶠ (Tmᶠ b) then Tmᶠ t else Tmᶠ u) F.ifᶠ
    MorphismOver.pairᶠ over = rec-uniqueP₂ (M.tm-local _ _)
      (λ t u → Tmᶠ (pairᴾ t u)) (λ t u → M.pair (Tmᶠ t) (Tmᶠ u)) F.pairᶠ
    MorphismOver.fstᶠ over = rec-unique (M.tm-local _ _)
      (λ t → Tmᶠ (fstᴾ t)) (λ t → M.fst (subst (M.Tm _) (F.×ᶠ _ _) (Tmᶠ t))) F.fstᶠ
    MorphismOver.sndᶠ over = rec-unique (M.tm-local _ _)
      (λ t → Tmᶠ (sndᴾ t)) (λ t → M.snd (subst (M.Tm _) (F.×ᶠ _ _) (Tmᶠ t))) F.sndᶠ
    MorphismOver.lamᶠ over = rec-uniqueP (M.tm-local _ _)
      (λ t → Tmᶠ (lamᴾ t))
      (λ t → M.lam (subst (λ Δ → M.Tm Δ _) (F.▷ᶠ _ _) (Tmᶠ t))) F.lamᶠ
    MorphismOver.appᶠ over = rec-unique₂ (M.tm-local _ _)
      (λ t u → Tmᶠ (appᴾ t u))
      (λ t u → M.app (subst (M.Tm _) (F.⇒ᶠ _ _) (Tmᶠ t)) (Tmᶠ u)) F.appᶠ

  restriction≃ : 
    SimpleMorphism LocalizedSyntaxCwF M.cwf ≃ SimpleMorphism RawSyntaxCwF M.cwf
  restriction≃ = isoToEquiv (iso restrictMorphism extendMorphism section retraction)
    where
    section : (f : SimpleMorphism RawSyntaxCwF M.cwf)
      → restrictMorphism (extendMorphism f) ≡ f
    section f = cong (simple-morphism (SimpleMorphism.sorts f))
      (morphismOver-path M.sub-set M.tm-set (λ _ → refl) (λ _ → refl))

    retraction : (f : SimpleMorphism LocalizedSyntaxCwF M.cwf)
      → extendMorphism (restrictMorphism f) ≡ f
    retraction f = cong (simple-morphism F.sorts)
      (morphismOver-path M.sub-set M.tm-set
        (rec-unique (M.sub-local _ _) E.Subᶠ F.Subᶠ (λ _ → refl))
        (rec-unique (M.tm-local _ _) E.Tmᶠ F.Tmᶠ (λ _ → refl)))
      where
      module F = SimpleMorphism f
      module E = SimpleMorphism (extendMorphism (restrictMorphism f))

localized-syntax-isInitial : (ℓS ℓM : Level) → isInitialDirected LocalizedSyntaxModel ℓS ℓM
localized-syntax-isInitial ℓS ℓM 𝓜 =
  isOfHLevelRespectEquiv 0 (invEquiv (restriction≃ 𝓜)) (raw-syntax-isInitial 𝓜)
