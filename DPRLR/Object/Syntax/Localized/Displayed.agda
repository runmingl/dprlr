module DPRLR.Object.Syntax.Localized.Displayed where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)

open import DPRLR.Simplicial.Hom
open import DPRLR.Object.Model.DisplayedModel
open import DPRLR.Object.Syntax.Raw.Model
open import DPRLR.Object.Syntax.Localized.Base
open import DPRLR.Object.Syntax.Localized.Model
import DPRLR.Object.Syntax.Raw.Base as Raw

private
  variable
    ℓD₀ ℓD₁ : Level

ηDisplayedSimpleCwF :
  DisplayedSimpleCwF ℓD₀ ℓD₁ LocalizedSyntaxCwF
  → DisplayedSimpleCwF ℓD₀ ℓD₁ RawSyntaxCwF
ηDisplayedSimpleCwF 𝓓 = 𝓔
  where
  module Disp = DisplayedSimpleCwF 𝓓

  reindexSubPath :
    {Γ Δ : Raw.Ctx}
    {Γ∙ : Disp.Ctx∙ Γ} {Δ∙ : Disp.Ctx∙ Δ}
    {σ τ : Subᴾ Γ Δ}
    {p q : σ ≡ τ}
    {σ∙ : Disp.Sub∙ Γ∙ Δ∙ σ} {τ∙ : Disp.Sub∙ Γ∙ Δ∙ τ}
    → PathP (λ i → Disp.Sub∙ Γ∙ Δ∙ (p i)) σ∙ τ∙
    → PathP (λ i → Disp.Sub∙ Γ∙ Δ∙ (q i)) σ∙ τ∙
  reindexSubPath {Γ∙ = Γ∙} {Δ∙ = Δ∙} {σ∙ = σ∙} {τ∙ = τ∙} =
    subst
      (λ q → PathP (λ i → Disp.Sub∙ Γ∙ Δ∙ (q i)) σ∙ τ∙)
      (Subᴾ-isSet _ _ _ _)

  reindexTmPath :
    {Γ : Raw.Ctx} {A : Raw.Ty}
    {Γ∙ : Disp.Ctx∙ Γ} {A∙ : Disp.Ty∙ A}
    {M N : Tmᴾ Γ A}
    {p q : M ≡ N}
    {M∙ : Disp.Tm∙ Γ∙ A∙ M} {N∙ : Disp.Tm∙ Γ∙ A∙ N}
    → PathP (λ i → Disp.Tm∙ Γ∙ A∙ (p i)) M∙ N∙
    → PathP (λ i → Disp.Tm∙ Γ∙ A∙ (q i)) M∙ N∙
  reindexTmPath {Γ∙ = Γ∙} {A∙ = A∙} {M∙ = M∙} {N∙ = N∙} =
    subst
      (λ q → PathP (λ i → Disp.Tm∙ Γ∙ A∙ (q i)) M∙ N∙)
      (Tmᴾ-isSet _ _ _ _)

  reindexTmHom :
    {Γ : Raw.Ctx} {A : Raw.Ty}
    {Γ∙ : Disp.Ctx∙ Γ} {A∙ : Disp.Ty∙ A}
    {M N : Tmᴾ Γ A}
    {h k : M ≤ N}
    {M∙ : Disp.Tm∙ Γ∙ A∙ M} {N∙ : Disp.Tm∙ Γ∙ A∙ N}
    → Disp.Tm∙ Γ∙ A∙ ⊢ M∙ ≤[ h ] N∙
    → Disp.Tm∙ Γ∙ A∙ ⊢ M∙ ≤[ k ] N∙
  reindexTmHom {Γ∙ = Γ∙} {A∙ = A∙} {M∙ = M∙} {N∙ = N∙} =
    subst (λ h → Disp.Tm∙ Γ∙ A∙ ⊢ M∙ ≤[ h ] N∙) (Tmᴾ-isThin _ _ _ _)

  homPTm-η :
    {Γ : Raw.Ctx} {A : Raw.Ty}
    {Γ∙ : Disp.Ctx∙ Γ} {A∙ : Disp.Ty∙ A}
    {M N : Raw.Tm Γ A}
    (h : M ≤ N)
    {M∙ : Disp.Tm∙ Γ∙ A∙ (ηTmᴾ M)}
    {N∙ : Disp.Tm∙ Γ∙ A∙ (ηTmᴾ N)}
    → Disp.Tm∙ Γ∙ A∙ ⊢ M∙ ≤[ hom-map ηTmᴾ h ] N∙
    → (λ M → Disp.Tm∙ Γ∙ A∙ (ηTmᴾ M)) ⊢ M∙ ≤[ h ] N∙
  homPTm-η h h∙ = h∙

  𝓔 : DisplayedSimpleCwF _ _ RawSyntaxCwF
  DisplayedSimpleCwF.Ctx∙ 𝓔 = Disp.Ctx∙
  DisplayedSimpleCwF.Ty∙ 𝓔 = Disp.Ty∙
  DisplayedSimpleCwF.Sub∙ 𝓔 Γ∙ Δ∙ σ =
    Disp.Sub∙ Γ∙ Δ∙ (ηSubᴾ σ)
  DisplayedSimpleCwF.Tm∙ 𝓔 Γ∙ A∙ M =
    Disp.Tm∙ Γ∙ A∙ (ηTmᴾ M)
  DisplayedSimpleCwF.id∙ 𝓔 = Disp.id∙
  DisplayedSimpleCwF._∘∙_ 𝓔 = Disp._∘∙_
  DisplayedSimpleCwF.id-left∙ 𝓔 σ∙ =
    reindexSubPath (Disp.id-left∙ σ∙)
  DisplayedSimpleCwF.id-right∙ 𝓔 σ∙ =
    reindexSubPath (Disp.id-right∙ σ∙)
  DisplayedSimpleCwF.∘-assoc∙ 𝓔 ρ∙ τ∙ σ∙ =
    reindexSubPath (Disp.∘-assoc∙ ρ∙ τ∙ σ∙)
  DisplayedSimpleCwF._[_]Tm∙ 𝓔 = Disp._[_]Tm∙
  DisplayedSimpleCwF.Tm-id∙ 𝓔 M∙ =
    reindexTmPath (Disp.Tm-id∙ M∙)
  DisplayedSimpleCwF.Tm-∘∙ 𝓔 M∙ τ∙ σ∙ =
    reindexTmPath (Disp.Tm-∘∙ M∙ τ∙ σ∙)
  DisplayedSimpleCwF.ε∙ 𝓔 = Disp.ε∙
  DisplayedSimpleCwF.ε-sub∙ 𝓔 = Disp.ε-sub∙
  DisplayedSimpleCwF.εη∙ 𝓔 σ∙ =
    reindexSubPath (Disp.εη∙ σ∙)
  DisplayedSimpleCwF._▷∙_ 𝓔 = Disp._▷∙_
  DisplayedSimpleCwF.p∙ 𝓔 = Disp.p∙
  DisplayedSimpleCwF.q∙ 𝓔 = Disp.q∙
  DisplayedSimpleCwF.⟨_,_⟩∙ 𝓔 = Disp.⟨_,_⟩∙
  DisplayedSimpleCwF.p-⟨⟩∙ 𝓔 σ∙ M∙ =
    reindexSubPath (Disp.p-⟨⟩∙ σ∙ M∙)
  DisplayedSimpleCwF.q-⟨⟩∙ 𝓔 σ∙ M∙ =
    reindexTmPath (Disp.q-⟨⟩∙ σ∙ M∙)
  DisplayedSimpleCwF.▷η∙ 𝓔 =
    reindexSubPath Disp.▷η∙
  DisplayedSimpleCwF.⟨⟩-∘∙ 𝓔 σ∙ M∙ ρ∙ =
    reindexSubPath (Disp.⟨⟩-∘∙ σ∙ M∙ ρ∙)
  DisplayedSimpleCwF.Bool∙ 𝓔 = Disp.Bool∙
  DisplayedSimpleCwF.true∙ 𝓔 = Disp.true∙
  DisplayedSimpleCwF.false∙ 𝓔 = Disp.false∙
  DisplayedSimpleCwF.if∙ 𝓔 = Disp.if∙
  DisplayedSimpleCwF.true[]∙ 𝓔 σ∙ =
    reindexTmPath (Disp.true[]∙ σ∙)
  DisplayedSimpleCwF.false[]∙ 𝓔 σ∙ =
    reindexTmPath (Disp.false[]∙ σ∙)
  DisplayedSimpleCwF.if[]∙ 𝓔 M∙ N∙ O∙ σ∙ =
    reindexTmPath (Disp.if[]∙ M∙ N∙ O∙ σ∙)
  DisplayedSimpleCwF.βif-true∙ 𝓔 {T = T} {F = F} T∙ F∙ =
    homPTm-η (Raw.βif-true T F)
      (reindexTmHom (Disp.βif-true∙ T∙ F∙))
  DisplayedSimpleCwF.βif-false∙ 𝓔 {T = T} {F = F} T∙ F∙ =
    homPTm-η (Raw.βif-false T F)
      (reindexTmHom (Disp.βif-false∙ T∙ F∙))
  DisplayedSimpleCwF._×ᵗʸ∙_ 𝓔 = Disp._×ᵗʸ∙_
  DisplayedSimpleCwF.pair∙ 𝓔 = Disp.pair∙
  DisplayedSimpleCwF.fst∙ 𝓔 = Disp.fst∙
  DisplayedSimpleCwF.snd∙ 𝓔 = Disp.snd∙
  DisplayedSimpleCwF.pair[]∙ 𝓔 M∙ N∙ σ∙ =
    reindexTmPath (Disp.pair[]∙ M∙ N∙ σ∙)
  DisplayedSimpleCwF.fst[]∙ 𝓔 P∙ σ∙ =
    reindexTmPath (Disp.fst[]∙ P∙ σ∙)
  DisplayedSimpleCwF.snd[]∙ 𝓔 P∙ σ∙ =
    reindexTmPath (Disp.snd[]∙ P∙ σ∙)
  DisplayedSimpleCwF.β×₁∙ 𝓔 {M = M} {N = N} M∙ N∙ =
    homPTm-η (Raw.β×₁ M N)
      (reindexTmHom (Disp.β×₁∙ M∙ N∙))
  DisplayedSimpleCwF.β×₂∙ 𝓔 {M = M} {N = N} M∙ N∙ =
    homPTm-η (Raw.β×₂ M N)
      (reindexTmHom (Disp.β×₂∙ M∙ N∙))
  DisplayedSimpleCwF.η×∙ 𝓔 {P = P} P∙ =
    homPTm-η (Raw.η× P)
      (reindexTmHom (Disp.η×∙ P∙))
  DisplayedSimpleCwF._⇒ᵗʸ∙_ 𝓔 = Disp._⇒ᵗʸ∙_
  DisplayedSimpleCwF.lam∙ 𝓔 = Disp.lam∙
  DisplayedSimpleCwF.app∙ 𝓔 = Disp.app∙
  DisplayedSimpleCwF.lam[]∙ 𝓔 N∙ σ∙ =
    reindexTmPath (Disp.lam[]∙ N∙ σ∙)
  DisplayedSimpleCwF.app[]∙ 𝓔 F∙ M∙ σ∙ =
    reindexTmPath (Disp.app[]∙ F∙ M∙ σ∙)
  DisplayedSimpleCwF.β⇒∙ 𝓔 {N = N} {M = M} N∙ M∙ =
    homPTm-η (Raw.β⇒ N M)
      (reindexTmHom (Disp.β⇒∙ N∙ M∙))
  DisplayedSimpleCwF.η⇒∙ 𝓔 {F = F} F∙ =
    homPTm-η (Raw.η⇒ F)
      (reindexTmHom (Disp.η⇒∙ F∙))
