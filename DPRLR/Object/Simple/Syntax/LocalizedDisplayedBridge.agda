module DPRLR.Object.Simple.Syntax.LocalizedDisplayedBridge where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)

open import DPRLR.Simplicial.Hom
open import DPRLR.Object.Simple.Displayed
open import DPRLR.Object.Simple.Syntax.RawModel
open import DPRLR.Object.Simple.Syntax.LocalizedSyntax
open import DPRLR.Object.Simple.Syntax.LocalizedModel
open import DPRLR.Object.Simple.Syntax.LocalizedCoherence
import DPRLR.Object.Simple.Syntax.Base as Raw

private
  variable
    ℓ ℓD₀ ℓD₁ : Level
    Γ Δ Θ Ξ : Raw.Ctx
    A B : Raw.Ty

substPathP :
  {X : Type ℓ} {P : X → Type ℓD₁}
  {x y : X} {p q : x ≡ y} {u : P x} {v : P y}
  → p ≡ q
  → PathP (λ i → P (p i)) u v
  → PathP (λ i → P (q i)) u v
substPathP {P = P} {u = u} {v = v} e =
  subst (λ q → PathP (λ i → P (q i)) u v) e

homP-subst :
  {X : Type ℓ} {P : X → Type ℓD₁}
  {x y : X} {h k : x ≤ y} {u : P x} {v : P y}
  → h ≡ k
  → P ⊢ u ≤[ h ] v
  → P ⊢ u ≤[ k ] v
homP-subst {P = P} {u = u} {v = v} e =
  subst (λ h → P ⊢ u ≤[ h ] v) e

homP-η :
  {P : Tmᴾ Γ A → Type ℓD₁}
  {M N : Raw.Tm Γ A}
  (h : M ≤ N)
  {M∙ : P (ηTmᴾ M)} {N∙ : P (ηTmᴾ N)}
  → P ⊢ M∙ ≤[ hom-map ηTmᴾ h ] N∙
  → (λ M → P (ηTmᴾ M)) ⊢ M∙ ≤[ h ] N∙
homP-η h h∙ = h∙

ηDisplayedSimpleCwF :
  DisplayedSimpleCwF ℓD₀ ℓD₁ LocalizedSyntaxCwF
  → DisplayedSimpleCwF ℓD₀ ℓD₁ RawSyntaxCwF
ηDisplayedSimpleCwF 𝓓 = 𝓔
  where
  module Disp = DisplayedSimpleCwF 𝓓

  substSubPathP :
    {Γ Δ : Raw.Ctx}
    {Γ∙ : Disp.Ctx∙ Γ} {Δ∙ : Disp.Ctx∙ Δ}
    {σ τ : Subᴾ Γ Δ}
    {p q : σ ≡ τ}
    {σ∙ : Disp.Sub∙ Γ∙ Δ∙ σ} {τ∙ : Disp.Sub∙ Γ∙ Δ∙ τ}
    → p ≡ q
    → PathP (λ i → Disp.Sub∙ Γ∙ Δ∙ (p i)) σ∙ τ∙
    → PathP (λ i → Disp.Sub∙ Γ∙ Δ∙ (q i)) σ∙ τ∙
  substSubPathP {Γ∙ = Γ∙} {Δ∙ = Δ∙} {σ∙ = σ∙} {τ∙ = τ∙} e =
    subst
      (λ q → PathP (λ i → Disp.Sub∙ Γ∙ Δ∙ (q i)) σ∙ τ∙)
      e

  substTmPathP :
    {Γ : Raw.Ctx} {A : Raw.Ty}
    {Γ∙ : Disp.Ctx∙ Γ} {A∙ : Disp.Ty∙ A}
    {M N : Tmᴾ Γ A}
    {p q : M ≡ N}
    {M∙ : Disp.Tm∙ Γ∙ A∙ M} {N∙ : Disp.Tm∙ Γ∙ A∙ N}
    → p ≡ q
    → PathP (λ i → Disp.Tm∙ Γ∙ A∙ (p i)) M∙ N∙
    → PathP (λ i → Disp.Tm∙ Γ∙ A∙ (q i)) M∙ N∙
  substTmPathP {Γ∙ = Γ∙} {A∙ = A∙} {M∙ = M∙} {N∙ = N∙} e =
    subst
      (λ q → PathP (λ i → Disp.Tm∙ Γ∙ A∙ (q i)) M∙ N∙)
      e

  homPTm-subst :
    {Γ : Raw.Ctx} {A : Raw.Ty}
    {Γ∙ : Disp.Ctx∙ Γ} {A∙ : Disp.Ty∙ A}
    {M N : Tmᴾ Γ A}
    {h k : M ≤ N}
    {M∙ : Disp.Tm∙ Γ∙ A∙ M} {N∙ : Disp.Tm∙ Γ∙ A∙ N}
    → h ≡ k
    → Disp.Tm∙ Γ∙ A∙ ⊢ M∙ ≤[ h ] N∙
    → Disp.Tm∙ Γ∙ A∙ ⊢ M∙ ≤[ k ] N∙
  homPTm-subst {Γ∙ = Γ∙} {A∙ = A∙} {M∙ = M∙} {N∙ = N∙} e =
    subst (λ h → Disp.Tm∙ Γ∙ A∙ ⊢ M∙ ≤[ h ] N∙) e

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
  DisplayedSimpleCwF.id-left∙ 𝓔 {σ = σ} σ∙ =
    substSubPathP (id-leftᴾ-η σ) (Disp.id-left∙ σ∙)
  DisplayedSimpleCwF.id-right∙ 𝓔 {σ = σ} σ∙ =
    substSubPathP (id-rightᴾ-η σ) (Disp.id-right∙ σ∙)
  DisplayedSimpleCwF.∘-assoc∙ 𝓔 {σ = σ} {τ = τ} {ρ = ρ} ρ∙ τ∙ σ∙ =
    substSubPathP (∘-assocᴾ-η ρ τ σ) (Disp.∘-assoc∙ ρ∙ τ∙ σ∙)
  DisplayedSimpleCwF._[_]Tm∙ 𝓔 = Disp._[_]Tm∙
  DisplayedSimpleCwF.Tm-id∙ 𝓔 {M = M} M∙ =
    substTmPathP (Tmᴾ-id-η M) (Disp.Tm-id∙ M∙)
  DisplayedSimpleCwF.Tm-∘∙ 𝓔 {M = M} {τ = τ} {σ = σ} M∙ τ∙ σ∙ =
    substTmPathP (Tmᴾ-∘-η M τ σ) (Disp.Tm-∘∙ M∙ τ∙ σ∙)
  DisplayedSimpleCwF.ε∙ 𝓔 = Disp.ε∙
  DisplayedSimpleCwF.ε-sub∙ 𝓔 = Disp.ε-sub∙
  DisplayedSimpleCwF.εη∙ 𝓔 {σ = σ} σ∙ =
    substSubPathP (εηᴾ-η σ) (Disp.εη∙ σ∙)
  DisplayedSimpleCwF._▷∙_ 𝓔 = Disp._▷∙_
  DisplayedSimpleCwF.p∙ 𝓔 = Disp.p∙
  DisplayedSimpleCwF.q∙ 𝓔 = Disp.q∙
  DisplayedSimpleCwF.⟨_,_⟩∙ 𝓔 = Disp.⟨_,_⟩∙
  DisplayedSimpleCwF.p-⟨⟩∙ 𝓔 {σ = σ} {M = M} σ∙ M∙ =
    substSubPathP (p-⟨⟩ᴾ-η σ M) (Disp.p-⟨⟩∙ σ∙ M∙)
  DisplayedSimpleCwF.q-⟨⟩∙ 𝓔 {σ = σ} {M = M} σ∙ M∙ =
    substTmPathP (q-⟨⟩ᴾ-η σ M) (Disp.q-⟨⟩∙ σ∙ M∙)
  DisplayedSimpleCwF.▷η∙ 𝓔 {Γ = Γ} {A = A} =
    substSubPathP (▷ηᴾ-η {Γ = Γ} {A = A}) Disp.▷η∙
  DisplayedSimpleCwF.⟨⟩-∘∙ 𝓔 {σ = σ} {M = M} {ρ = ρ} σ∙ M∙ ρ∙ =
    substSubPathP (⟨⟩-∘ᴾ-η σ M ρ) (Disp.⟨⟩-∘∙ σ∙ M∙ ρ∙)
  DisplayedSimpleCwF.Bool∙ 𝓔 = Disp.Bool∙
  DisplayedSimpleCwF.true∙ 𝓔 = Disp.true∙
  DisplayedSimpleCwF.false∙ 𝓔 = Disp.false∙
  DisplayedSimpleCwF.if∙ 𝓔 = Disp.if∙
  DisplayedSimpleCwF.true[]∙ 𝓔 {σ = σ} σ∙ =
    substTmPathP (true[]ᴾ-η σ) (Disp.true[]∙ σ∙)
  DisplayedSimpleCwF.false[]∙ 𝓔 {σ = σ} σ∙ =
    substTmPathP (false[]ᴾ-η σ) (Disp.false[]∙ σ∙)
  DisplayedSimpleCwF.if[]∙ 𝓔 {B = M} {T = N} {F = O} {σ = σ} M∙ N∙ O∙ σ∙ =
    substTmPathP (if[]ᴾ-η M N O σ) (Disp.if[]∙ M∙ N∙ O∙ σ∙)
  DisplayedSimpleCwF.βif-true∙ 𝓔 {T = T} {F = F} T∙ F∙ =
    homPTm-η (Raw.βif-true T F)
      (homPTm-subst (βif-trueᴾ-η T F) (Disp.βif-true∙ T∙ F∙))
  DisplayedSimpleCwF.βif-false∙ 𝓔 {T = T} {F = F} T∙ F∙ =
    homPTm-η (Raw.βif-false T F)
      (homPTm-subst (βif-falseᴾ-η T F) (Disp.βif-false∙ T∙ F∙))
  DisplayedSimpleCwF._×ᵗʸ∙_ 𝓔 = Disp._×ᵗʸ∙_
  DisplayedSimpleCwF.pair∙ 𝓔 = Disp.pair∙
  DisplayedSimpleCwF.fst∙ 𝓔 = Disp.fst∙
  DisplayedSimpleCwF.snd∙ 𝓔 = Disp.snd∙
  DisplayedSimpleCwF.pair[]∙ 𝓔 {M = M} {N = N} {σ = σ} M∙ N∙ σ∙ =
    substTmPathP (pair[]ᴾ-η M N σ) (Disp.pair[]∙ M∙ N∙ σ∙)
  DisplayedSimpleCwF.fst[]∙ 𝓔 {P = P} {σ = σ} P∙ σ∙ =
    substTmPathP (fst[]ᴾ-η P σ) (Disp.fst[]∙ P∙ σ∙)
  DisplayedSimpleCwF.snd[]∙ 𝓔 {P = P} {σ = σ} P∙ σ∙ =
    substTmPathP (snd[]ᴾ-η P σ) (Disp.snd[]∙ P∙ σ∙)
  DisplayedSimpleCwF.β×₁∙ 𝓔 {M = M} {N = N} M∙ N∙ =
    homPTm-η (Raw.β×₁ M N)
      (homPTm-subst (β×₁ᴾ-η M N) (Disp.β×₁∙ M∙ N∙))
  DisplayedSimpleCwF.β×₂∙ 𝓔 {M = M} {N = N} M∙ N∙ =
    homPTm-η (Raw.β×₂ M N)
      (homPTm-subst (β×₂ᴾ-η M N) (Disp.β×₂∙ M∙ N∙))
  DisplayedSimpleCwF.η×∙ 𝓔 {P = P} P∙ =
    homPTm-η (Raw.η× P)
      (homPTm-subst (η×ᴾ-η P) (Disp.η×∙ P∙))
  DisplayedSimpleCwF._⇒ᵗʸ∙_ 𝓔 = Disp._⇒ᵗʸ∙_
  DisplayedSimpleCwF.lam∙ 𝓔 = Disp.lam∙
  DisplayedSimpleCwF.app∙ 𝓔 = Disp.app∙
  DisplayedSimpleCwF.lam[]∙ 𝓔 {N = N} {σ = σ} N∙ σ∙ =
    substTmPathP (lam[]ᴾ-η N σ) (Disp.lam[]∙ N∙ σ∙)
  DisplayedSimpleCwF.app[]∙ 𝓔 {F = F} {M = M} {σ = σ} F∙ M∙ σ∙ =
    substTmPathP (app[]ᴾ-η F M σ) (Disp.app[]∙ F∙ M∙ σ∙)
  DisplayedSimpleCwF.β⇒∙ 𝓔 {N = N} {M = M} N∙ M∙ =
    homPTm-η (Raw.β⇒ N M)
      (homPTm-subst (β⇒ᴾ-η N M) (Disp.β⇒∙ N∙ M∙))
  DisplayedSimpleCwF.η⇒∙ 𝓔 {F = F} F∙ =
    homPTm-η (Raw.η⇒ F)
      (homPTm-subst (η⇒ᴾ-η F) (Disp.η⇒∙ F∙))
