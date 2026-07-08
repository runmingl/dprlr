module DPRLR.Object.Simple.Syntax.LocalizedCoherence where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)

open import DPRLR.Simplicial.Hom
open import DPRLR.Object.Simple.Syntax.LocalizedSyntax
import DPRLR.Object.Simple.Syntax.Base as Raw

private
  variable
    Γ Δ Θ Ξ : Raw.Ctx
    A B : Raw.Ty

id-leftᴾ-η :
  (σ : Raw.Sub Γ Δ)
  → id-leftᴾ (ηSubᴾ σ) ≡ cong ηSubᴾ (Raw.id-left σ)
id-leftᴾ-η σ =
  Subᴾ-isSet _ _ (id-leftᴾ (ηSubᴾ σ)) (cong ηSubᴾ (Raw.id-left σ))

id-rightᴾ-η :
  (σ : Raw.Sub Γ Δ)
  → id-rightᴾ (ηSubᴾ σ) ≡ cong ηSubᴾ (Raw.id-right σ)
id-rightᴾ-η σ =
  Subᴾ-isSet _ _ (id-rightᴾ (ηSubᴾ σ)) (cong ηSubᴾ (Raw.id-right σ))

∘-assocᴾ-η :
  (ρ : Raw.Sub Θ Ξ) (τ : Raw.Sub Δ Θ) (σ : Raw.Sub Γ Δ)
  → ∘-assocᴾ (ηSubᴾ ρ) (ηSubᴾ τ) (ηSubᴾ σ)
    ≡ cong ηSubᴾ (Raw.∘-assoc ρ τ σ)
∘-assocᴾ-η ρ τ σ =
  Subᴾ-isSet
    _
    _
    (∘-assocᴾ (ηSubᴾ ρ) (ηSubᴾ τ) (ηSubᴾ σ))
    (cong ηSubᴾ (Raw.∘-assoc ρ τ σ))

εηᴾ-η :
  (σ : Raw.Sub Γ Raw.ε)
  → εηᴾ (ηSubᴾ σ) ≡ cong ηSubᴾ (Raw.εη σ)
εηᴾ-η σ =
  Subᴾ-isSet _ _ (εηᴾ (ηSubᴾ σ)) (cong ηSubᴾ (Raw.εη σ))

p-⟨⟩ᴾ-η :
  (σ : Raw.Sub Γ Δ) (M : Raw.Tm Γ A)
  → p-⟨⟩ᴾ (ηSubᴾ σ) (ηTmᴾ M)
    ≡ cong ηSubᴾ (Raw.p-⟨⟩ σ M)
p-⟨⟩ᴾ-η σ M =
  Subᴾ-isSet
    _
    _
    (p-⟨⟩ᴾ (ηSubᴾ σ) (ηTmᴾ M))
    (cong ηSubᴾ (Raw.p-⟨⟩ σ M))

q-⟨⟩ᴾ-η :
  (σ : Raw.Sub Γ Δ) (M : Raw.Tm Γ A)
  → q-⟨⟩ᴾ (ηSubᴾ σ) (ηTmᴾ M)
    ≡ cong ηTmᴾ (Raw.q-⟨⟩ σ M)
q-⟨⟩ᴾ-η σ M =
  Tmᴾ-isSet
    _
    _
    (q-⟨⟩ᴾ (ηSubᴾ σ) (ηTmᴾ M))
    (cong ηTmᴾ (Raw.q-⟨⟩ σ M))

▷ηᴾ-η :
  {Γ : Raw.Ctx} {A : Raw.Ty}
  → ▷ηᴾ {Γ = Γ} {A = A} ≡ cong ηSubᴾ (Raw.▷η {Γ = Γ} {A = A})
▷ηᴾ-η =
  Subᴾ-isSet _ _ ▷ηᴾ (cong ηSubᴾ Raw.▷η)

Tmᴾ-id-η :
  (M : Raw.Tm Γ A)
  → Tmᴾ-id (ηTmᴾ M) ≡ cong ηTmᴾ (Raw.Tm-id M)
Tmᴾ-id-η M =
  Tmᴾ-isSet _ _ (Tmᴾ-id (ηTmᴾ M)) (cong ηTmᴾ (Raw.Tm-id M))

Tmᴾ-∘-η :
  (M : Raw.Tm Ξ A)
  (τ : Raw.Sub Δ Ξ)
  (σ : Raw.Sub Γ Δ)
  → Tmᴾ-∘ (ηTmᴾ M) (ηSubᴾ τ) (ηSubᴾ σ)
    ≡ cong ηTmᴾ (Raw.Tm-∘ M τ σ)
Tmᴾ-∘-η M τ σ =
  Tmᴾ-isSet
    _
    _
    (Tmᴾ-∘ (ηTmᴾ M) (ηSubᴾ τ) (ηSubᴾ σ))
    (cong ηTmᴾ (Raw.Tm-∘ M τ σ))

⟨⟩-∘ᴾ-η :
  (σ : Raw.Sub Γ Δ) (M : Raw.Tm Γ A) (ρ : Raw.Sub Θ Γ)
  → ⟨⟩-∘ᴾ (ηSubᴾ σ) (ηTmᴾ M) (ηSubᴾ ρ)
    ≡ cong ηSubᴾ (Raw.⟨⟩-∘ σ M ρ)
⟨⟩-∘ᴾ-η σ M ρ =
  Subᴾ-isSet
    _
    _
    (⟨⟩-∘ᴾ (ηSubᴾ σ) (ηTmᴾ M) (ηSubᴾ ρ))
    (cong ηSubᴾ (Raw.⟨⟩-∘ σ M ρ))

true[]ᴾ-η :
  (σ : Raw.Sub Γ Δ)
  → true[]ᴾ (ηSubᴾ σ) ≡ cong ηTmᴾ (Raw.true[] σ)
true[]ᴾ-η σ =
  Tmᴾ-isSet _ _ (true[]ᴾ (ηSubᴾ σ)) (cong ηTmᴾ (Raw.true[] σ))

false[]ᴾ-η :
  (σ : Raw.Sub Γ Δ)
  → false[]ᴾ (ηSubᴾ σ) ≡ cong ηTmᴾ (Raw.false[] σ)
false[]ᴾ-η σ =
  Tmᴾ-isSet _ _ (false[]ᴾ (ηSubᴾ σ)) (cong ηTmᴾ (Raw.false[] σ))

if[]ᴾ-η :
  (M : Raw.Tm Δ Raw.Bool) (N O : Raw.Tm Δ A) (σ : Raw.Sub Γ Δ)
  → if[]ᴾ (ηTmᴾ M) (ηTmᴾ N) (ηTmᴾ O) (ηSubᴾ σ)
    ≡ cong ηTmᴾ (Raw.if[] M N O σ)
if[]ᴾ-η M N O σ =
  Tmᴾ-isSet
    _
    _
    (if[]ᴾ (ηTmᴾ M) (ηTmᴾ N) (ηTmᴾ O) (ηSubᴾ σ))
    (cong ηTmᴾ (Raw.if[] M N O σ))

pair[]ᴾ-η :
  (M : Raw.Tm Δ A) (N : Raw.Tm Δ B) (σ : Raw.Sub Γ Δ)
  → pair[]ᴾ (ηTmᴾ M) (ηTmᴾ N) (ηSubᴾ σ)
    ≡ cong ηTmᴾ (Raw.pair[] M N σ)
pair[]ᴾ-η M N σ =
  Tmᴾ-isSet
    _
    _
    (pair[]ᴾ (ηTmᴾ M) (ηTmᴾ N) (ηSubᴾ σ))
    (cong ηTmᴾ (Raw.pair[] M N σ))

fst[]ᴾ-η :
  (P : Raw.Tm Δ (A Raw.×ᵗʸ B)) (σ : Raw.Sub Γ Δ)
  → fst[]ᴾ (ηTmᴾ P) (ηSubᴾ σ)
    ≡ cong ηTmᴾ (Raw.fst[] P σ)
fst[]ᴾ-η P σ =
  Tmᴾ-isSet _ _ (fst[]ᴾ (ηTmᴾ P) (ηSubᴾ σ)) (cong ηTmᴾ (Raw.fst[] P σ))

snd[]ᴾ-η :
  (P : Raw.Tm Δ (A Raw.×ᵗʸ B)) (σ : Raw.Sub Γ Δ)
  → snd[]ᴾ (ηTmᴾ P) (ηSubᴾ σ)
    ≡ cong ηTmᴾ (Raw.snd[] P σ)
snd[]ᴾ-η P σ =
  Tmᴾ-isSet _ _ (snd[]ᴾ (ηTmᴾ P) (ηSubᴾ σ)) (cong ηTmᴾ (Raw.snd[] P σ))

lam[]ᴾ-η :
  (N : Raw.Tm (Δ Raw.▷ A) B) (σ : Raw.Sub Γ Δ)
  → lam[]ᴾ (ηTmᴾ N) (ηSubᴾ σ)
    ≡ cong ηTmᴾ (Raw.lam[] N σ)
lam[]ᴾ-η N σ =
  Tmᴾ-isSet
    _
    _
    (lam[]ᴾ (ηTmᴾ N) (ηSubᴾ σ))
    (cong ηTmᴾ (Raw.lam[] N σ))

app[]ᴾ-η :
  (F : Raw.Tm Δ (A Raw.⇒ᵗʸ B)) (M : Raw.Tm Δ A) (σ : Raw.Sub Γ Δ)
  → app[]ᴾ (ηTmᴾ F) (ηTmᴾ M) (ηSubᴾ σ)
    ≡ cong ηTmᴾ (Raw.app[] F M σ)
app[]ᴾ-η F M σ =
  Tmᴾ-isSet
    _
    _
    (app[]ᴾ (ηTmᴾ F) (ηTmᴾ M) (ηSubᴾ σ))
    (cong ηTmᴾ (Raw.app[] F M σ))

βif-trueᴾ-η :
  (T F : Raw.Tm Γ A)
  → βif-trueᴾ (ηTmᴾ T) (ηTmᴾ F)
    ≡ hom-map ηTmᴾ (Raw.βif-true T F)
βif-trueᴾ-η T F =
  Tmᴾ-isThin
    _
    _
    (βif-trueᴾ (ηTmᴾ T) (ηTmᴾ F))
    (hom-map ηTmᴾ (Raw.βif-true T F))

βif-falseᴾ-η :
  (T F : Raw.Tm Γ A)
  → βif-falseᴾ (ηTmᴾ T) (ηTmᴾ F)
    ≡ hom-map ηTmᴾ (Raw.βif-false T F)
βif-falseᴾ-η T F =
  Tmᴾ-isThin
    _
    _
    (βif-falseᴾ (ηTmᴾ T) (ηTmᴾ F))
    (hom-map ηTmᴾ (Raw.βif-false T F))

β×₁ᴾ-η :
  (M : Raw.Tm Γ A) (N : Raw.Tm Γ B)
  → β×₁ᴾ (ηTmᴾ M) (ηTmᴾ N)
    ≡ hom-map ηTmᴾ (Raw.β×₁ M N)
β×₁ᴾ-η M N =
  Tmᴾ-isThin
    _
    _
    (β×₁ᴾ (ηTmᴾ M) (ηTmᴾ N))
    (hom-map ηTmᴾ (Raw.β×₁ M N))

β×₂ᴾ-η :
  (M : Raw.Tm Γ A) (N : Raw.Tm Γ B)
  → β×₂ᴾ (ηTmᴾ M) (ηTmᴾ N)
    ≡ hom-map ηTmᴾ (Raw.β×₂ M N)
β×₂ᴾ-η M N =
  Tmᴾ-isThin
    _
    _
    (β×₂ᴾ (ηTmᴾ M) (ηTmᴾ N))
    (hom-map ηTmᴾ (Raw.β×₂ M N))

η×ᴾ-η :
  (P : Raw.Tm Γ (A Raw.×ᵗʸ B))
  → η×ᴾ (ηTmᴾ P) ≡ hom-map ηTmᴾ (Raw.η× P)
η×ᴾ-η P =
  Tmᴾ-isThin
    _
    _
    (η×ᴾ (ηTmᴾ P))
    (hom-map ηTmᴾ (Raw.η× P))

β⇒ᴾ-η :
  (N : Raw.Tm (Γ Raw.▷ A) B) (M : Raw.Tm Γ A)
  → β⇒ᴾ (ηTmᴾ N) (ηTmᴾ M)
    ≡ hom-map ηTmᴾ (Raw.β⇒ N M)
β⇒ᴾ-η N M =
  Tmᴾ-isThin
    _
    _
    (β⇒ᴾ (ηTmᴾ N) (ηTmᴾ M))
    (hom-map ηTmᴾ (Raw.β⇒ N M))

η⇒ᴾ-η :
  (F : Raw.Tm Γ (A Raw.⇒ᵗʸ B))
  → η⇒ᴾ (ηTmᴾ F) ≡ hom-map ηTmᴾ (Raw.η⇒ F)
η⇒ᴾ-η F =
  Tmᴾ-isThin
    _
    _
    (η⇒ᴾ (ηTmᴾ F))
    (hom-map ηTmᴾ (Raw.η⇒ F))
