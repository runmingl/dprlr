module DPRLR.Object.Syntax.Localized.Base where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Interval
open import DPRLR.Simplicial.PreorderLocalization
open import DPRLR.Simplicial.Segal
import DPRLR.Object.Syntax.Raw.Base as Raw

infixl 30 _∘ᴾ_
infixl 40 _[_]Tmᴾ
infix  5 ⟨_,_⟩ᴾ

private
  variable
    Γ Δ Θ Ξ : Raw.Ctx
    A B : Raw.Ty

Subᴾ : Raw.Ctx → Raw.Ctx → Type
Subᴾ Γ Δ = ∥ Raw.Sub Γ Δ ∥ᴾ

Tmᴾ : Raw.Ctx → Raw.Ty → Type
Tmᴾ Γ A = ∥ Raw.Tm Γ A ∥ᴾ

Lineᴾ : Raw.Ctx → Raw.Ty → Type
Lineᴾ Γ A = 𝟚 → Tmᴾ Γ A

ηSubᴾ : Raw.Sub Γ Δ → Subᴾ Γ Δ
ηSubᴾ = ηᴾ

ηTmᴾ : Raw.Tm Γ A → Tmᴾ Γ A
ηTmᴾ = ηᴾ

Subᴾ-isSet : isSet (Subᴾ Γ Δ)
Subᴾ-isSet = isPreorder→isSet isPreorderP

Subᴾ-isThin : isThin (Subᴾ Γ Δ)
Subᴾ-isThin = isPreorder→isThin isPreorderP

Subᴾ-isSegal : isSegal (Subᴾ Γ Δ)
Subᴾ-isSegal = isPreorder→isSegal isPreorderP

Tmᴾ-isSet : isSet (Tmᴾ Γ A)
Tmᴾ-isSet = isPreorder→isSet isPreorderP

Tmᴾ-isThin : isThin (Tmᴾ Γ A)
Tmᴾ-isThin = isPreorder→isThin isPreorderP

Tmᴾ-isSegal : isSegal (Tmᴾ Γ A)
Tmᴾ-isSegal = isPreorder→isSegal isPreorderP

Lineᴾ-isPreorder : isPreorder (Lineᴾ Γ A)
Lineᴾ-isPreorder = isPreorderΠ λ _ → isPreorderP

idᴾ : Subᴾ Γ Γ
idᴾ = ηᴾ Raw.id

_∘ᴾ_ : Subᴾ Θ Δ → Subᴾ Γ Θ → Subᴾ Γ Δ
τ ∘ᴾ σ =
  rec isPreorderP
    (λ τ₀ →
      rec isPreorderP
        (λ σ₀ → ηᴾ (τ₀ Raw.∘ σ₀))
        σ)
    τ

ε-subᴾ : Subᴾ Γ Raw.ε
ε-subᴾ = ηᴾ Raw.ε-sub

pᴾ : Subᴾ (Γ Raw.▷ A) Γ
pᴾ = ηᴾ Raw.p

qᴾ : Tmᴾ (Γ Raw.▷ A) A
qᴾ = ηᴾ Raw.q

⟨_,_⟩ᴾ : Subᴾ Γ Δ → Tmᴾ Γ A → Subᴾ Γ (Δ Raw.▷ A)
⟨ σ , M ⟩ᴾ =
  rec isPreorderP
    (λ σ₀ →
      rec isPreorderP
        (λ M₀ → ηᴾ (Raw.⟨ σ₀ , M₀ ⟩))
        M)
    σ

trueᴾ : Tmᴾ Γ Raw.Bool
trueᴾ = ηᴾ Raw.true

falseᴾ : Tmᴾ Γ Raw.Bool
falseᴾ = ηᴾ Raw.false

ifᴾ : Tmᴾ Γ Raw.Bool → Tmᴾ Γ A → Tmᴾ Γ A → Tmᴾ Γ A
ifᴾ B T F =
  rec isPreorderP
    (λ B₀ →
      rec isPreorderP
        (λ T₀ →
          rec isPreorderP
            (λ F₀ → ηᴾ (Raw.if B₀ then T₀ else F₀))
            F)
        T)
    B

fstᴾ : Tmᴾ Γ (A Raw.×ᵗʸ B) → Tmᴾ Γ A
fstᴾ = rec isPreorderP (λ P → ηᴾ (Raw.fst P))

sndᴾ : Tmᴾ Γ (A Raw.×ᵗʸ B) → Tmᴾ Γ B
sndᴾ = rec isPreorderP (λ P → ηᴾ (Raw.snd P))

pairᴾ : Tmᴾ Γ A → Tmᴾ Γ B → Tmᴾ Γ (A Raw.×ᵗʸ B)
pairᴾ M N =
  rec isPreorderP
    (λ M₀ →
      rec isPreorderP
        (λ N₀ → ηᴾ (Raw.pair M₀ N₀))
        N)
    M

lamᴾ : Tmᴾ (Γ Raw.▷ A) B → Tmᴾ Γ (A Raw.⇒ᵗʸ B)
lamᴾ = rec isPreorderP (λ N → ηᴾ (Raw.lam N))

appᴾ : Tmᴾ Γ (A Raw.⇒ᵗʸ B) → Tmᴾ Γ A → Tmᴾ Γ B
appᴾ F M =
  rec isPreorderP
    (λ F₀ →
      rec isPreorderP
        (λ M₀ → ηᴾ (Raw.app F₀ M₀))
        M)
    F

_[_]Tmᴾ : Tmᴾ Δ A → Subᴾ Γ Δ → Tmᴾ Γ A
M [ σ ]Tmᴾ =
  rec isPreorderP
    (λ M₀ →
      rec isPreorderP
        (λ σ₀ → ηᴾ (Raw._[_]Tm M₀ σ₀))
        σ)
    M

id-leftᴾ :
  (σ : Subᴾ Γ Δ)
  → idᴾ ∘ᴾ σ ≡ σ
id-leftᴾ =
  rec-unique
    isPreorderP
    (λ σ → idᴾ ∘ᴾ σ)
    (λ σ → σ)
    (λ σ₀ → cong ηᴾ (Raw.id-left σ₀))

id-rightᴾ :
  (σ : Subᴾ Γ Δ)
  → σ ∘ᴾ idᴾ ≡ σ
id-rightᴾ =
  rec-unique
    isPreorderP
    (λ σ → σ ∘ᴾ idᴾ)
    (λ σ → σ)
    (λ σ₀ → cong ηᴾ (Raw.id-right σ₀))

∘-assocᴾ :
  (ρ : Subᴾ Θ Ξ) (τ : Subᴾ Δ Θ) (σ : Subᴾ Γ Δ)
  → (ρ ∘ᴾ τ) ∘ᴾ σ ≡ ρ ∘ᴾ (τ ∘ᴾ σ)
∘-assocᴾ ρ τ σ =
  rec-unique
    isPreorderP
    (λ ρ → (ρ ∘ᴾ τ) ∘ᴾ σ)
    (λ ρ → ρ ∘ᴾ (τ ∘ᴾ σ))
    (λ ρ₀ →
      rec-unique
        isPreorderP
        (λ τ → (ηᴾ ρ₀ ∘ᴾ τ) ∘ᴾ σ)
        (λ τ → ηᴾ ρ₀ ∘ᴾ (τ ∘ᴾ σ))
        (λ τ₀ →
          rec-unique
            isPreorderP
            (λ σ → (ηᴾ ρ₀ ∘ᴾ ηᴾ τ₀) ∘ᴾ σ)
            (λ σ → ηᴾ ρ₀ ∘ᴾ (ηᴾ τ₀ ∘ᴾ σ))
            (λ σ₀ → cong ηᴾ (Raw.∘-assoc ρ₀ τ₀ σ₀))
            σ)
        τ)
    ρ

εηᴾ :
  (σ : Subᴾ Γ Raw.ε)
  → σ ≡ ε-subᴾ
εηᴾ =
  rec-unique
    isPreorderP
    (λ σ → σ)
    (λ _ → ε-subᴾ)
    (λ σ₀ → cong ηᴾ (Raw.εη σ₀))

p-⟨⟩ᴾ :
  (σ : Subᴾ Γ Δ) (M : Tmᴾ Γ A)
  → pᴾ ∘ᴾ ⟨ σ , M ⟩ᴾ ≡ σ
p-⟨⟩ᴾ σ M =
  rec-unique
    isPreorderP
    (λ σ → pᴾ ∘ᴾ ⟨ σ , M ⟩ᴾ)
    (λ σ → σ)
    (λ σ₀ →
      rec-unique
        isPreorderP
        (λ M → pᴾ ∘ᴾ ⟨ ηᴾ σ₀ , M ⟩ᴾ)
        (λ _ → ηᴾ σ₀)
        (λ M₀ → cong ηᴾ (Raw.p-⟨⟩ σ₀ M₀))
        M)
    σ

q-⟨⟩ᴾ :
  (σ : Subᴾ Γ Δ) (M : Tmᴾ Γ A)
  → qᴾ [ ⟨ σ , M ⟩ᴾ ]Tmᴾ ≡ M
q-⟨⟩ᴾ σ M =
  rec-unique
    isPreorderP
    (λ σ → qᴾ [ ⟨ σ , M ⟩ᴾ ]Tmᴾ)
    (λ _ → M)
    (λ σ₀ →
      rec-unique
        isPreorderP
        (λ M → qᴾ [ ⟨ ηᴾ σ₀ , M ⟩ᴾ ]Tmᴾ)
        (λ M → M)
        (λ M₀ → cong ηᴾ (Raw.q-⟨⟩ σ₀ M₀))
        M)
    σ

▷ηᴾ :
  {Γ : Raw.Ctx} {A : Raw.Ty}
  → ⟨ pᴾ {Γ = Γ} {A = A} , qᴾ {Γ = Γ} {A = A} ⟩ᴾ ≡ idᴾ
▷ηᴾ = cong ηᴾ Raw.▷η

Tmᴾ-id :
  (M : Tmᴾ Γ A)
  → M [ idᴾ ]Tmᴾ ≡ M
Tmᴾ-id =
  rec-unique
    isPreorderP
    (λ M → M [ idᴾ ]Tmᴾ)
    (λ M → M)
    (λ M₀ → cong ηᴾ (Raw.Tm-id M₀))

Tmᴾ-∘ :
  (M : Tmᴾ Ξ A)
  (τ : Subᴾ Δ Ξ)
  (σ : Subᴾ Γ Δ)
  → (M [ τ ]Tmᴾ) [ σ ]Tmᴾ ≡ M [ τ ∘ᴾ σ ]Tmᴾ
Tmᴾ-∘ M τ σ =
  rec-unique
    isPreorderP
    (λ M → (M [ τ ]Tmᴾ) [ σ ]Tmᴾ)
    (λ M → M [ τ ∘ᴾ σ ]Tmᴾ)
    (λ M₀ →
      rec-unique
        isPreorderP
        (λ τ → (ηᴾ M₀ [ τ ]Tmᴾ) [ σ ]Tmᴾ)
        (λ τ → ηᴾ M₀ [ τ ∘ᴾ σ ]Tmᴾ)
        (λ τ₀ →
          rec-unique
            isPreorderP
            (λ σ → (ηᴾ M₀ [ ηᴾ τ₀ ]Tmᴾ) [ σ ]Tmᴾ)
            (λ σ → ηᴾ M₀ [ ηᴾ τ₀ ∘ᴾ σ ]Tmᴾ)
            (λ σ₀ → cong ηᴾ (Raw.Tm-∘ M₀ τ₀ σ₀))
            σ)
        τ)
    M

true[]ᴾ :
  (σ : Subᴾ Γ Δ)
  → trueᴾ [ σ ]Tmᴾ ≡ trueᴾ
true[]ᴾ =
  rec-unique
    isPreorderP
    (λ σ → trueᴾ [ σ ]Tmᴾ)
    (λ _ → trueᴾ)
    (λ σ₀ → cong ηᴾ (Raw.true[] σ₀))

false[]ᴾ :
  (σ : Subᴾ Γ Δ)
  → falseᴾ [ σ ]Tmᴾ ≡ falseᴾ
false[]ᴾ =
  rec-unique
    isPreorderP
    (λ σ → falseᴾ [ σ ]Tmᴾ)
    (λ _ → falseᴾ)
    (λ σ₀ → cong ηᴾ (Raw.false[] σ₀))

if[]ᴾ :
  (B : Tmᴾ Δ Raw.Bool) (T F : Tmᴾ Δ A) (σ : Subᴾ Γ Δ)
  → ifᴾ B T F [ σ ]Tmᴾ
    ≡ ifᴾ (B [ σ ]Tmᴾ) (T [ σ ]Tmᴾ) (F [ σ ]Tmᴾ)
if[]ᴾ B T F σ =
  rec-unique
    isPreorderP
    (λ B → ifᴾ B T F [ σ ]Tmᴾ)
    (λ B → ifᴾ (B [ σ ]Tmᴾ) (T [ σ ]Tmᴾ) (F [ σ ]Tmᴾ))
    (λ B₀ →
      rec-unique
        isPreorderP
        (λ T → ifᴾ (ηᴾ B₀) T F [ σ ]Tmᴾ)
        (λ T → ifᴾ (ηᴾ B₀ [ σ ]Tmᴾ) (T [ σ ]Tmᴾ) (F [ σ ]Tmᴾ))
        (λ T₀ →
          rec-unique
            isPreorderP
            (λ F → ifᴾ (ηᴾ B₀) (ηᴾ T₀) F [ σ ]Tmᴾ)
            (λ F → ifᴾ (ηᴾ B₀ [ σ ]Tmᴾ) (ηᴾ T₀ [ σ ]Tmᴾ) (F [ σ ]Tmᴾ))
            (λ F₀ →
              rec-unique
                isPreorderP
                (λ σ → ifᴾ (ηᴾ B₀) (ηᴾ T₀) (ηᴾ F₀) [ σ ]Tmᴾ)
                (λ σ →
                  ifᴾ
                    (ηᴾ B₀ [ σ ]Tmᴾ)
                    (ηᴾ T₀ [ σ ]Tmᴾ)
                    (ηᴾ F₀ [ σ ]Tmᴾ))
                (λ σ₀ → cong ηᴾ (Raw.if[] B₀ T₀ F₀ σ₀))
                σ)
            F)
        T)
    B

⟨⟩-∘ᴾ :
  (σ : Subᴾ Γ Δ) (M : Tmᴾ Γ A) (ρ : Subᴾ Θ Γ)
  → ⟨ σ , M ⟩ᴾ ∘ᴾ ρ ≡ ⟨ σ ∘ᴾ ρ , M [ ρ ]Tmᴾ ⟩ᴾ
⟨⟩-∘ᴾ σ M ρ =
  rec-unique
    isPreorderP
    (λ σ → ⟨ σ , M ⟩ᴾ ∘ᴾ ρ)
    (λ σ → ⟨ σ ∘ᴾ ρ , M [ ρ ]Tmᴾ ⟩ᴾ)
    (λ σ₀ →
      rec-unique
        isPreorderP
        (λ M → ⟨ ηᴾ σ₀ , M ⟩ᴾ ∘ᴾ ρ)
        (λ M → ⟨ ηᴾ σ₀ ∘ᴾ ρ , M [ ρ ]Tmᴾ ⟩ᴾ)
        (λ M₀ →
          rec-unique
            isPreorderP
            (λ ρ → ⟨ ηᴾ σ₀ , ηᴾ M₀ ⟩ᴾ ∘ᴾ ρ)
            (λ ρ → ⟨ ηᴾ σ₀ ∘ᴾ ρ , ηᴾ M₀ [ ρ ]Tmᴾ ⟩ᴾ)
            (λ ρ₀ → cong ηᴾ (Raw.⟨⟩-∘ σ₀ M₀ ρ₀))
            ρ)
        M)
    σ

pair[]ᴾ :
  (M : Tmᴾ Δ A) (N : Tmᴾ Δ B) (σ : Subᴾ Γ Δ)
  → pairᴾ M N [ σ ]Tmᴾ ≡ pairᴾ (M [ σ ]Tmᴾ) (N [ σ ]Tmᴾ)
pair[]ᴾ M N σ =
  rec-unique
    isPreorderP
    (λ M → pairᴾ M N [ σ ]Tmᴾ)
    (λ M → pairᴾ (M [ σ ]Tmᴾ) (N [ σ ]Tmᴾ))
    (λ M₀ →
      rec-unique
        isPreorderP
        (λ N → pairᴾ (ηᴾ M₀) N [ σ ]Tmᴾ)
        (λ N → pairᴾ (ηᴾ M₀ [ σ ]Tmᴾ) (N [ σ ]Tmᴾ))
        (λ N₀ →
          rec-unique
            isPreorderP
            (λ σ → pairᴾ (ηᴾ M₀) (ηᴾ N₀) [ σ ]Tmᴾ)
            (λ σ → pairᴾ (ηᴾ M₀ [ σ ]Tmᴾ) (ηᴾ N₀ [ σ ]Tmᴾ))
            (λ σ₀ → cong ηᴾ (Raw.pair[] M₀ N₀ σ₀))
            σ)
        N)
    M

fst[]ᴾ :
  (P : Tmᴾ Δ (A Raw.×ᵗʸ B)) (σ : Subᴾ Γ Δ)
  → fstᴾ P [ σ ]Tmᴾ ≡ fstᴾ (P [ σ ]Tmᴾ)
fst[]ᴾ P σ =
  rec-unique
    isPreorderP
    (λ P → fstᴾ P [ σ ]Tmᴾ)
    (λ P → fstᴾ (P [ σ ]Tmᴾ))
    (λ P₀ →
      rec-unique
        isPreorderP
        (λ σ → fstᴾ (ηᴾ P₀) [ σ ]Tmᴾ)
        (λ σ → fstᴾ (ηᴾ P₀ [ σ ]Tmᴾ))
        (λ σ₀ → cong ηᴾ (Raw.fst[] P₀ σ₀))
        σ)
    P

snd[]ᴾ :
  (P : Tmᴾ Δ (A Raw.×ᵗʸ B)) (σ : Subᴾ Γ Δ)
  → sndᴾ P [ σ ]Tmᴾ ≡ sndᴾ (P [ σ ]Tmᴾ)
snd[]ᴾ P σ =
  rec-unique
    isPreorderP
    (λ P → sndᴾ P [ σ ]Tmᴾ)
    (λ P → sndᴾ (P [ σ ]Tmᴾ))
    (λ P₀ →
      rec-unique
        isPreorderP
        (λ σ → sndᴾ (ηᴾ P₀) [ σ ]Tmᴾ)
        (λ σ → sndᴾ (ηᴾ P₀ [ σ ]Tmᴾ))
        (λ σ₀ → cong ηᴾ (Raw.snd[] P₀ σ₀))
        σ)
    P

βif-true-relᴾ : Tmᴾ Γ A → Tmᴾ Γ A → 𝟚 → Tmᴾ Γ A
βif-true-relᴾ {Γ = Γ} {A = A} T F =
  rec
    Lineᴾ-isPreorder
    (λ T₀ →
      rec
        Lineᴾ-isPreorder
        (λ F₀ i → ηᴾ (Raw.βif-true-rel T₀ F₀ i))
        F)
    T

βif-true-leftᴾ :
  (T F : Tmᴾ Γ A)
  → βif-true-relᴾ T F 𝟎 ≡ ifᴾ trueᴾ T F
βif-true-leftᴾ T F =
  funExt⁻ (funExt⁻ path T) F
  where
  path :
    (λ T F → βif-true-relᴾ T F 𝟎)
      ≡
    (λ T F → ifᴾ trueᴾ T F)
  path =
    funExt
    (rec-unique
      (isPreorderΠ λ _ → isPreorderP)
      (λ T F → βif-true-relᴾ T F 𝟎)
      (λ T F → ifᴾ trueᴾ T F)
      (λ T₀ →
        funExt
        (rec-unique
          isPreorderP
          (λ F → βif-true-relᴾ (ηᴾ T₀) F 𝟎)
          (λ F → ifᴾ trueᴾ (ηᴾ T₀) F)
          (λ F₀ → cong ηᴾ (Raw.βif-true-left T₀ F₀))))
    )

βif-true-rightᴾ :
  (T F : Tmᴾ Γ A)
  → βif-true-relᴾ T F 𝟏 ≡ T
βif-true-rightᴾ T F =
  funExt⁻ (funExt⁻ path T) F
  where
  path :
    (λ T F → βif-true-relᴾ T F 𝟏)
      ≡
    (λ T F → T)
  path =
    funExt
    (rec-unique
      (isPreorderΠ λ _ → isPreorderP)
      (λ T F → βif-true-relᴾ T F 𝟏)
      (λ T F → T)
      (λ T₀ →
        funExt
        (rec-unique
          isPreorderP
          (λ F → βif-true-relᴾ (ηᴾ T₀) F 𝟏)
          (λ _ → ηᴾ T₀)
          (λ F₀ → cong ηᴾ (Raw.βif-true-right T₀ F₀))))
    )

βif-trueᴾ :
  (T F : Tmᴾ Γ A)
  → ifᴾ trueᴾ T F ≤ T
βif-trueᴾ T F =
  βif-true-relᴾ T F
  , βif-true-leftᴾ T F
  , βif-true-rightᴾ T F

βif-false-relᴾ : Tmᴾ Γ A → Tmᴾ Γ A → 𝟚 → Tmᴾ Γ A
βif-false-relᴾ {Γ = Γ} {A = A} T F =
  rec
    Lineᴾ-isPreorder
    (λ T₀ →
      rec
        Lineᴾ-isPreorder
        (λ F₀ i → ηᴾ (Raw.βif-false-rel T₀ F₀ i))
        F)
    T

βif-false-leftᴾ :
  (T F : Tmᴾ Γ A)
  → βif-false-relᴾ T F 𝟎 ≡ ifᴾ falseᴾ T F
βif-false-leftᴾ T F =
  funExt⁻ (funExt⁻ path T) F
  where
  path :
    (λ T F → βif-false-relᴾ T F 𝟎)
      ≡
    (λ T F → ifᴾ falseᴾ T F)
  path =
    funExt
    (rec-unique
      (isPreorderΠ λ _ → isPreorderP)
      (λ T F → βif-false-relᴾ T F 𝟎)
      (λ T F → ifᴾ falseᴾ T F)
      (λ T₀ →
        funExt
        (rec-unique
          isPreorderP
          (λ F → βif-false-relᴾ (ηᴾ T₀) F 𝟎)
          (λ F → ifᴾ falseᴾ (ηᴾ T₀) F)
          (λ F₀ → cong ηᴾ (Raw.βif-false-left T₀ F₀))))
    )

βif-false-rightᴾ :
  (T F : Tmᴾ Γ A)
  → βif-false-relᴾ T F 𝟏 ≡ F
βif-false-rightᴾ T F =
  funExt⁻ (funExt⁻ path T) F
  where
  path :
    (λ T F → βif-false-relᴾ T F 𝟏)
      ≡
    (λ T F → F)
  path =
    funExt
    (rec-unique
      (isPreorderΠ λ _ → isPreorderP)
      (λ T F → βif-false-relᴾ T F 𝟏)
      (λ T F → F)
      (λ T₀ →
        funExt
        (rec-unique
          isPreorderP
          (λ F → βif-false-relᴾ (ηᴾ T₀) F 𝟏)
          (λ F → F)
          (λ F₀ → cong ηᴾ (Raw.βif-false-right T₀ F₀))))
    )

βif-falseᴾ :
  (T F : Tmᴾ Γ A)
  → ifᴾ falseᴾ T F ≤ F
βif-falseᴾ T F =
  βif-false-relᴾ T F
  , βif-false-leftᴾ T F
  , βif-false-rightᴾ T F

lam[]ᴾ :
  (N : Tmᴾ (Δ Raw.▷ A) B) (σ : Subᴾ Γ Δ)
  → lamᴾ N [ σ ]Tmᴾ
    ≡ lamᴾ (N [ ⟨ σ ∘ᴾ pᴾ , qᴾ ⟩ᴾ ]Tmᴾ)
lam[]ᴾ N σ =
  rec-unique
    isPreorderP
    (λ N → lamᴾ N [ σ ]Tmᴾ)
    (λ N → lamᴾ (N [ ⟨ σ ∘ᴾ pᴾ , qᴾ ⟩ᴾ ]Tmᴾ))
    (λ N₀ →
      rec-unique
        isPreorderP
        (λ σ → lamᴾ (ηᴾ N₀) [ σ ]Tmᴾ)
        (λ σ → lamᴾ (ηᴾ N₀ [ ⟨ σ ∘ᴾ pᴾ , qᴾ ⟩ᴾ ]Tmᴾ))
        (λ σ₀ → cong ηᴾ (Raw.lam[] N₀ σ₀))
        σ)
    N

app[]ᴾ :
  (F : Tmᴾ Δ (A Raw.⇒ᵗʸ B)) (M : Tmᴾ Δ A) (σ : Subᴾ Γ Δ)
  → appᴾ F M [ σ ]Tmᴾ ≡ appᴾ (F [ σ ]Tmᴾ) (M [ σ ]Tmᴾ)
app[]ᴾ F M σ =
  rec-unique
    isPreorderP
    (λ F → appᴾ F M [ σ ]Tmᴾ)
    (λ F → appᴾ (F [ σ ]Tmᴾ) (M [ σ ]Tmᴾ))
    (λ F₀ →
      rec-unique
        isPreorderP
        (λ M → appᴾ (ηᴾ F₀) M [ σ ]Tmᴾ)
        (λ M → appᴾ (ηᴾ F₀ [ σ ]Tmᴾ) (M [ σ ]Tmᴾ))
        (λ M₀ →
          rec-unique
            isPreorderP
            (λ σ → appᴾ (ηᴾ F₀) (ηᴾ M₀) [ σ ]Tmᴾ)
            (λ σ → appᴾ (ηᴾ F₀ [ σ ]Tmᴾ) (ηᴾ M₀ [ σ ]Tmᴾ))
            (λ σ₀ → cong ηᴾ (Raw.app[] F₀ M₀ σ₀))
            σ)
        M)
    F

β×₁-relᴾ : Tmᴾ Γ A → Tmᴾ Γ B → Lineᴾ Γ A
β×₁-relᴾ {Γ = Γ} {A = A} {B = B} M N =
  rec
    Lineᴾ-isPreorder
    (λ M₀ →
      rec
        Lineᴾ-isPreorder
        (λ N₀ i → ηᴾ (Raw.β×₁-rel M₀ N₀ i))
        N)
    M

β×₁-leftᴾ :
  (M : Tmᴾ Γ A) (N : Tmᴾ Γ B)
  → β×₁-relᴾ M N 𝟎 ≡ fstᴾ (pairᴾ M N)
β×₁-leftᴾ M N =
  funExt⁻ (funExt⁻ path M) N
  where
  path :
    (λ M N → β×₁-relᴾ M N 𝟎)
      ≡
    (λ M N → fstᴾ (pairᴾ M N))
  path =
    funExt
    (rec-unique
      (isPreorderΠ λ _ → isPreorderP)
      (λ M N → β×₁-relᴾ M N 𝟎)
      (λ M N → fstᴾ (pairᴾ M N))
      (λ M₀ →
        funExt
        (rec-unique
          isPreorderP
          (λ N → β×₁-relᴾ (ηᴾ M₀) N 𝟎)
          (λ N → fstᴾ (pairᴾ (ηᴾ M₀) N))
          (λ N₀ → cong ηᴾ (Raw.β×₁-left M₀ N₀))))
    )

β×₁-rightᴾ :
  (M : Tmᴾ Γ A) (N : Tmᴾ Γ B)
  → β×₁-relᴾ M N 𝟏 ≡ M
β×₁-rightᴾ M N =
  funExt⁻ (funExt⁻ path M) N
  where
  path :
    (λ M N → β×₁-relᴾ M N 𝟏)
      ≡
    (λ M N → M)
  path =
    funExt
    (rec-unique
      (isPreorderΠ λ _ → isPreorderP)
      (λ M N → β×₁-relᴾ M N 𝟏)
      (λ M N → M)
      (λ M₀ →
        funExt
        (rec-unique
          isPreorderP
          (λ N → β×₁-relᴾ (ηᴾ M₀) N 𝟏)
          (λ _ → ηᴾ M₀)
          (λ N₀ → cong ηᴾ (Raw.β×₁-right M₀ N₀))))
    )

β×₁ᴾ :
  (M : Tmᴾ Γ A) (N : Tmᴾ Γ B)
  → fstᴾ (pairᴾ M N) ≤ M
β×₁ᴾ M N =
  β×₁-relᴾ M N
  , β×₁-leftᴾ M N
  , β×₁-rightᴾ M N

β×₂-relᴾ : Tmᴾ Γ A → Tmᴾ Γ B → Lineᴾ Γ B
β×₂-relᴾ {Γ = Γ} {A = A} {B = B} M N =
  rec
    Lineᴾ-isPreorder
    (λ M₀ →
      rec
        Lineᴾ-isPreorder
        (λ N₀ i → ηᴾ (Raw.β×₂-rel M₀ N₀ i))
        N)
    M

β×₂-leftᴾ :
  (M : Tmᴾ Γ A) (N : Tmᴾ Γ B)
  → β×₂-relᴾ M N 𝟎 ≡ sndᴾ (pairᴾ M N)
β×₂-leftᴾ M N =
  funExt⁻ (funExt⁻ path M) N
  where
  path :
    (λ M N → β×₂-relᴾ M N 𝟎)
      ≡
    (λ M N → sndᴾ (pairᴾ M N))
  path =
    funExt
    (rec-unique
      (isPreorderΠ λ _ → isPreorderP)
      (λ M N → β×₂-relᴾ M N 𝟎)
      (λ M N → sndᴾ (pairᴾ M N))
      (λ M₀ →
        funExt
        (rec-unique
          isPreorderP
          (λ N → β×₂-relᴾ (ηᴾ M₀) N 𝟎)
          (λ N → sndᴾ (pairᴾ (ηᴾ M₀) N))
          (λ N₀ → cong ηᴾ (Raw.β×₂-left M₀ N₀))))
    )

β×₂-rightᴾ :
  (M : Tmᴾ Γ A) (N : Tmᴾ Γ B)
  → β×₂-relᴾ M N 𝟏 ≡ N
β×₂-rightᴾ M N =
  funExt⁻ (funExt⁻ path M) N
  where
  path :
    (λ M N → β×₂-relᴾ M N 𝟏)
      ≡
    (λ M N → N)
  path =
    funExt
    (rec-unique
      (isPreorderΠ λ _ → isPreorderP)
      (λ M N → β×₂-relᴾ M N 𝟏)
      (λ M N → N)
      (λ M₀ →
        funExt
        (rec-unique
          isPreorderP
          (λ N → β×₂-relᴾ (ηᴾ M₀) N 𝟏)
          (λ N → N)
          (λ N₀ → cong ηᴾ (Raw.β×₂-right M₀ N₀))))
    )

β×₂ᴾ :
  (M : Tmᴾ Γ A) (N : Tmᴾ Γ B)
  → sndᴾ (pairᴾ M N) ≤ N
β×₂ᴾ M N =
  β×₂-relᴾ M N
  , β×₂-leftᴾ M N
  , β×₂-rightᴾ M N

η×-relᴾ : Tmᴾ Γ (A Raw.×ᵗʸ B) → Lineᴾ Γ (A Raw.×ᵗʸ B)
η×-relᴾ P =
  rec
    Lineᴾ-isPreorder
    (λ P₀ i → ηᴾ (Raw.η×-rel P₀ i))
    P

η×-leftᴾ :
  (P : Tmᴾ Γ (A Raw.×ᵗʸ B))
  → η×-relᴾ P 𝟎 ≡ pairᴾ (fstᴾ P) (sndᴾ P)
η×-leftᴾ P =
  funExt⁻ path P
  where
  path :
    (λ P → η×-relᴾ P 𝟎)
      ≡
    (λ P → pairᴾ (fstᴾ P) (sndᴾ P))
  path =
    funExt
    (rec-unique
      isPreorderP
      (λ P → η×-relᴾ P 𝟎)
      (λ P → pairᴾ (fstᴾ P) (sndᴾ P))
      (λ P₀ → cong ηᴾ (Raw.η×-left P₀)))

η×-rightᴾ :
  (P : Tmᴾ Γ (A Raw.×ᵗʸ B))
  → η×-relᴾ P 𝟏 ≡ P
η×-rightᴾ P =
  funExt⁻ path P
  where
  path :
    (λ P → η×-relᴾ P 𝟏)
      ≡
    (λ P → P)
  path =
    funExt
    (rec-unique
      isPreorderP
      (λ P → η×-relᴾ P 𝟏)
      (λ P → P)
      (λ P₀ → cong ηᴾ (Raw.η×-right P₀)))

η×ᴾ :
  (P : Tmᴾ Γ (A Raw.×ᵗʸ B))
  → pairᴾ (fstᴾ P) (sndᴾ P) ≤ P
η×ᴾ P =
  η×-relᴾ P
  , η×-leftᴾ P
  , η×-rightᴾ P

β⇒-relᴾ : Tmᴾ (Γ Raw.▷ A) B → Tmᴾ Γ A → Lineᴾ Γ B
β⇒-relᴾ {Γ = Γ} {A = A} {B = B} N M =
  rec
    Lineᴾ-isPreorder
    (λ N₀ →
      rec
        Lineᴾ-isPreorder
        (λ M₀ i → ηᴾ (Raw.β⇒-rel N₀ M₀ i))
        M)
    N

β⇒-leftᴾ :
  (N : Tmᴾ (Γ Raw.▷ A) B) (M : Tmᴾ Γ A)
  → β⇒-relᴾ N M 𝟎 ≡ appᴾ (lamᴾ N) M
β⇒-leftᴾ N M =
  funExt⁻ (funExt⁻ path N) M
  where
  path :
    (λ N M → β⇒-relᴾ N M 𝟎)
      ≡
    (λ N M → appᴾ (lamᴾ N) M)
  path =
    funExt
    (rec-unique
      (isPreorderΠ λ _ → isPreorderP)
      (λ N M → β⇒-relᴾ N M 𝟎)
      (λ N M → appᴾ (lamᴾ N) M)
      (λ N₀ →
        funExt
        (rec-unique
          isPreorderP
          (λ M → β⇒-relᴾ (ηᴾ N₀) M 𝟎)
          (λ M → appᴾ (lamᴾ (ηᴾ N₀)) M)
          (λ M₀ → cong ηᴾ (Raw.β⇒-left N₀ M₀))))
    )

β⇒-rightᴾ :
  (N : Tmᴾ (Γ Raw.▷ A) B) (M : Tmᴾ Γ A)
  → β⇒-relᴾ N M 𝟏 ≡ N [ ⟨ idᴾ , M ⟩ᴾ ]Tmᴾ
β⇒-rightᴾ N M =
  funExt⁻ (funExt⁻ path N) M
  where
  path :
    (λ N M → β⇒-relᴾ N M 𝟏)
      ≡
    (λ N M → N [ ⟨ idᴾ , M ⟩ᴾ ]Tmᴾ)
  path =
    funExt
    (rec-unique
      (isPreorderΠ λ _ → isPreorderP)
      (λ N M → β⇒-relᴾ N M 𝟏)
      (λ N M → N [ ⟨ idᴾ , M ⟩ᴾ ]Tmᴾ)
      (λ N₀ →
        funExt
        (rec-unique
          isPreorderP
          (λ M → β⇒-relᴾ (ηᴾ N₀) M 𝟏)
          (λ M → ηᴾ N₀ [ ⟨ idᴾ , M ⟩ᴾ ]Tmᴾ)
          (λ M₀ → cong ηᴾ (Raw.β⇒-right N₀ M₀))))
    )

β⇒ᴾ :
  (N : Tmᴾ (Γ Raw.▷ A) B) (M : Tmᴾ Γ A)
  → appᴾ (lamᴾ N) M ≤ N [ ⟨ idᴾ , M ⟩ᴾ ]Tmᴾ
β⇒ᴾ N M =
  β⇒-relᴾ N M
  , β⇒-leftᴾ N M
  , β⇒-rightᴾ N M

η⇒-relᴾ : Tmᴾ Γ (A Raw.⇒ᵗʸ B) → Lineᴾ Γ (A Raw.⇒ᵗʸ B)
η⇒-relᴾ F =
  rec
    Lineᴾ-isPreorder
    (λ F₀ i → ηᴾ (Raw.η⇒-rel F₀ i))
    F

η⇒-leftᴾ :
  (F : Tmᴾ Γ (A Raw.⇒ᵗʸ B))
  → η⇒-relᴾ F 𝟎 ≡ lamᴾ (appᴾ (F [ pᴾ ]Tmᴾ) qᴾ)
η⇒-leftᴾ F =
  funExt⁻ path F
  where
  path :
    (λ F → η⇒-relᴾ F 𝟎)
      ≡
    (λ F → lamᴾ (appᴾ (F [ pᴾ ]Tmᴾ) qᴾ))
  path =
    funExt
    (rec-unique
      isPreorderP
      (λ F → η⇒-relᴾ F 𝟎)
      (λ F → lamᴾ (appᴾ (F [ pᴾ ]Tmᴾ) qᴾ))
      (λ F₀ → cong ηᴾ (Raw.η⇒-left F₀)))

η⇒-rightᴾ :
  (F : Tmᴾ Γ (A Raw.⇒ᵗʸ B))
  → η⇒-relᴾ F 𝟏 ≡ F
η⇒-rightᴾ F =
  funExt⁻ path F
  where
  path :
    (λ F → η⇒-relᴾ F 𝟏)
      ≡
    (λ F → F)
  path =
    funExt
    (rec-unique
      isPreorderP
      (λ F → η⇒-relᴾ F 𝟏)
      (λ F → F)
      (λ F₀ → cong ηᴾ (Raw.η⇒-right F₀)))

η⇒ᴾ :
  (F : Tmᴾ Γ (A Raw.⇒ᵗʸ B))
  → lamᴾ (appᴾ (F [ pᴾ ]Tmᴾ) qᴾ) ≤ F
η⇒ᴾ F =
  η⇒-relᴾ F
  , η⇒-leftᴾ F
  , η⇒-rightᴾ F
