module DPRLR.Object.Syntax.Localized where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.PreorderLocalization
import DPRLR.Object.Syntax.Raw as Raw

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

ηSubᴾ : Raw.Sub Γ Δ → Subᴾ Γ Δ
ηSubᴾ = ηᴾ

ηTmᴾ : Raw.Tm Γ A → Tmᴾ Γ A
ηTmᴾ = ηᴾ

Subᴾ-isPreorder : isPreorder (Subᴾ Γ Δ)
Subᴾ-isPreorder = ∥∥ᴾ-isPreorder

Tmᴾ-isPreorder : isPreorder (Tmᴾ Γ A)
Tmᴾ-isPreorder = ∥∥ᴾ-isPreorder

idᴾ : Subᴾ Γ Γ
idᴾ = ηᴾ Raw.id

_∘ᴾ_ : Subᴾ Θ Δ → Subᴾ Γ Θ → Subᴾ Γ Δ
_∘ᴾ_ = recᴾ₂ ∥∥ᴾ-isPreorder λ τ σ → ηᴾ (τ Raw.∘ σ)

ε-subᴾ : Subᴾ Γ Raw.ε
ε-subᴾ = ηᴾ Raw.ε-sub

pᴾ : Subᴾ (Γ Raw.▷ A) Γ
pᴾ = ηᴾ Raw.p

qᴾ : Tmᴾ (Γ Raw.▷ A) A
qᴾ = ηᴾ Raw.q

⟨_,_⟩ᴾ : Subᴾ Γ Δ → Tmᴾ Γ A → Subᴾ Γ (Δ Raw.▷ A)
⟨_,_⟩ᴾ = recᴾ₂ ∥∥ᴾ-isPreorder λ σ M → ηᴾ (Raw.⟨ σ , M ⟩)

_[_]Tmᴾ : Tmᴾ Δ A → Subᴾ Γ Δ → Tmᴾ Γ A
_[_]Tmᴾ = recᴾ₂ ∥∥ᴾ-isPreorder λ M σ → ηᴾ (M Raw.[ σ ]Tm)

trueᴾ : Tmᴾ Γ Raw.Bool
trueᴾ = ηᴾ Raw.true

falseᴾ : Tmᴾ Γ Raw.Bool
falseᴾ = ηᴾ Raw.false

ifᴾ : Tmᴾ Γ Raw.Bool → Tmᴾ Γ A → Tmᴾ Γ A → Tmᴾ Γ A
ifᴾ = recᴾ₃ ∥∥ᴾ-isPreorder λ B T F → ηᴾ (Raw.if B then T else F)

pairᴾ : Tmᴾ Γ A → Tmᴾ Γ B → Tmᴾ Γ (A Raw.×ᵗʸ B)
pairᴾ = recᴾ₂ ∥∥ᴾ-isPreorder λ M N → ηᴾ (Raw.pair M N)

fstᴾ : Tmᴾ Γ (A Raw.×ᵗʸ B) → Tmᴾ Γ A
fstᴾ = recᴾ ∥∥ᴾ-isPreorder (ηᴾ ∘ Raw.fst)

sndᴾ : Tmᴾ Γ (A Raw.×ᵗʸ B) → Tmᴾ Γ B
sndᴾ = recᴾ ∥∥ᴾ-isPreorder (ηᴾ ∘ Raw.snd)

lamᴾ : Tmᴾ (Γ Raw.▷ A) B → Tmᴾ Γ (A Raw.⇒ᵗʸ B)
lamᴾ = recᴾ ∥∥ᴾ-isPreorder (ηᴾ ∘ Raw.lam)

appᴾ : Tmᴾ Γ (A Raw.⇒ᵗʸ B) → Tmᴾ Γ A → Tmᴾ Γ B
appᴾ = recᴾ₂ ∥∥ᴾ-isPreorder λ F M → ηᴾ (Raw.app F M)

id-leftᴾ : (σ : Subᴾ Γ Δ) → idᴾ ∘ᴾ σ ≡ σ
id-leftᴾ = recᴾ-unique ∥∥ᴾ-isPreorder (idᴾ ∘ᴾ_) (λ σ → σ) (cong ηᴾ ∘ Raw.id-left)

id-rightᴾ : (σ : Subᴾ Γ Δ) → σ ∘ᴾ idᴾ ≡ σ
id-rightᴾ = recᴾ-unique ∥∥ᴾ-isPreorder (_∘ᴾ idᴾ) (λ σ → σ) (cong ηᴾ ∘ Raw.id-right)

∘-assocᴾ : (ρ : Subᴾ Θ Ξ) (τ : Subᴾ Δ Θ) (σ : Subᴾ Γ Δ)
  → (ρ ∘ᴾ τ) ∘ᴾ σ ≡ ρ ∘ᴾ (τ ∘ᴾ σ)
∘-assocᴾ = recᴾ-unique₃ ∥∥ᴾ-isPreorder
  (λ ρ τ σ → (ρ ∘ᴾ τ) ∘ᴾ σ) (λ ρ τ σ → ρ ∘ᴾ (τ ∘ᴾ σ))
  λ ρ τ σ → cong ηᴾ (Raw.∘-assoc ρ τ σ)

εηᴾ : (σ : Subᴾ Γ Raw.ε) → σ ≡ ε-subᴾ
εηᴾ = recᴾ-unique ∥∥ᴾ-isPreorder (λ σ → σ) (λ _ → ε-subᴾ) (cong ηᴾ ∘ Raw.εη)

p-⟨⟩ᴾ : (σ : Subᴾ Γ Δ) (M : Tmᴾ Γ A) → pᴾ ∘ᴾ ⟨ σ , M ⟩ᴾ ≡ σ
p-⟨⟩ᴾ = recᴾ-unique₂ ∥∥ᴾ-isPreorder (λ σ M → pᴾ ∘ᴾ ⟨ σ , M ⟩ᴾ) (λ σ _ → σ)
  λ σ M → cong ηᴾ (Raw.p-⟨⟩ σ M)

q-⟨⟩ᴾ : (σ : Subᴾ Γ Δ) (M : Tmᴾ Γ A) → qᴾ [ ⟨ σ , M ⟩ᴾ ]Tmᴾ ≡ M
q-⟨⟩ᴾ = recᴾ-unique₂ ∥∥ᴾ-isPreorder (λ σ M → qᴾ [ ⟨ σ , M ⟩ᴾ ]Tmᴾ) (λ _ M → M)
  λ σ M → cong ηᴾ (Raw.q-⟨⟩ σ M)

▷ηᴾ : {Γ : Raw.Ctx} {A : Raw.Ty}
  → ⟨ pᴾ {Γ = Γ} {A = A} , qᴾ {Γ = Γ} {A = A} ⟩ᴾ ≡ idᴾ
▷ηᴾ = cong ηᴾ Raw.▷η

⟨⟩-∘ᴾ : (σ : Subᴾ Γ Δ) (M : Tmᴾ Γ A) (ρ : Subᴾ Θ Γ)
  → ⟨ σ , M ⟩ᴾ ∘ᴾ ρ ≡ ⟨ σ ∘ᴾ ρ , M [ ρ ]Tmᴾ ⟩ᴾ
⟨⟩-∘ᴾ = recᴾ-unique₃ ∥∥ᴾ-isPreorder
  (λ σ M ρ → ⟨ σ , M ⟩ᴾ ∘ᴾ ρ) (λ σ M ρ → ⟨ σ ∘ᴾ ρ , M [ ρ ]Tmᴾ ⟩ᴾ)
  λ σ M ρ → cong ηᴾ (Raw.⟨⟩-∘ σ M ρ)

Tmᴾ-id : (M : Tmᴾ Γ A) → M [ idᴾ ]Tmᴾ ≡ M
Tmᴾ-id = recᴾ-unique ∥∥ᴾ-isPreorder (_[ idᴾ ]Tmᴾ) (λ M → M) (cong ηᴾ ∘ Raw.Tm-id)

Tmᴾ-∘ : (M : Tmᴾ Ξ A) (τ : Subᴾ Δ Ξ) (σ : Subᴾ Γ Δ)
  → (M [ τ ]Tmᴾ) [ σ ]Tmᴾ ≡ M [ τ ∘ᴾ σ ]Tmᴾ
Tmᴾ-∘ = recᴾ-unique₃ ∥∥ᴾ-isPreorder
  (λ M τ σ → (M [ τ ]Tmᴾ) [ σ ]Tmᴾ) (λ M τ σ → M [ τ ∘ᴾ σ ]Tmᴾ)
  λ M τ σ → cong ηᴾ (Raw.Tm-∘ M τ σ)

true[]ᴾ : (σ : Subᴾ Γ Δ) → trueᴾ [ σ ]Tmᴾ ≡ trueᴾ
true[]ᴾ = recᴾ-unique ∥∥ᴾ-isPreorder (trueᴾ [_]Tmᴾ) (λ _ → trueᴾ) (cong ηᴾ ∘ Raw.true[])

false[]ᴾ : (σ : Subᴾ Γ Δ) → falseᴾ [ σ ]Tmᴾ ≡ falseᴾ
false[]ᴾ = recᴾ-unique ∥∥ᴾ-isPreorder (falseᴾ [_]Tmᴾ) (λ _ → falseᴾ) (cong ηᴾ ∘ Raw.false[])

if[]ᴾ : (B : Tmᴾ Δ Raw.Bool) (T F : Tmᴾ Δ A) (σ : Subᴾ Γ Δ)
  → ifᴾ B T F [ σ ]Tmᴾ ≡ ifᴾ (B [ σ ]Tmᴾ) (T [ σ ]Tmᴾ) (F [ σ ]Tmᴾ)
if[]ᴾ = recᴾ-unique₄ ∥∥ᴾ-isPreorder
  (λ B T F σ → ifᴾ B T F [ σ ]Tmᴾ)
  (λ B T F σ → ifᴾ (B [ σ ]Tmᴾ) (T [ σ ]Tmᴾ) (F [ σ ]Tmᴾ))
  λ B T F σ → cong ηᴾ (Raw.if[] B T F σ)

pair[]ᴾ : (M : Tmᴾ Δ A) (N : Tmᴾ Δ B) (σ : Subᴾ Γ Δ)
  → pairᴾ M N [ σ ]Tmᴾ ≡ pairᴾ (M [ σ ]Tmᴾ) (N [ σ ]Tmᴾ)
pair[]ᴾ = recᴾ-unique₃ ∥∥ᴾ-isPreorder
  (λ M N σ → pairᴾ M N [ σ ]Tmᴾ) (λ M N σ → pairᴾ (M [ σ ]Tmᴾ) (N [ σ ]Tmᴾ))
  λ M N σ → cong ηᴾ (Raw.pair[] M N σ)

fst[]ᴾ : (P : Tmᴾ Δ (A Raw.×ᵗʸ B)) (σ : Subᴾ Γ Δ)
  → fstᴾ P [ σ ]Tmᴾ ≡ fstᴾ (P [ σ ]Tmᴾ)
fst[]ᴾ = recᴾ-unique₂ ∥∥ᴾ-isPreorder
  (λ P σ → fstᴾ P [ σ ]Tmᴾ) (λ P σ → fstᴾ (P [ σ ]Tmᴾ))
  λ P σ → cong ηᴾ (Raw.fst[] P σ)

snd[]ᴾ : (P : Tmᴾ Δ (A Raw.×ᵗʸ B)) (σ : Subᴾ Γ Δ)
  → sndᴾ P [ σ ]Tmᴾ ≡ sndᴾ (P [ σ ]Tmᴾ)
snd[]ᴾ = recᴾ-unique₂ ∥∥ᴾ-isPreorder
  (λ P σ → sndᴾ P [ σ ]Tmᴾ) (λ P σ → sndᴾ (P [ σ ]Tmᴾ))
  λ P σ → cong ηᴾ (Raw.snd[] P σ)

lam[]ᴾ : (N : Tmᴾ (Δ Raw.▷ A) B) (σ : Subᴾ Γ Δ)
  → lamᴾ N [ σ ]Tmᴾ ≡ lamᴾ (N [ ⟨ σ ∘ᴾ pᴾ , qᴾ ⟩ᴾ ]Tmᴾ)
lam[]ᴾ = recᴾ-unique₂ ∥∥ᴾ-isPreorder
  (λ N σ → lamᴾ N [ σ ]Tmᴾ) (λ N σ → lamᴾ (N [ ⟨ σ ∘ᴾ pᴾ , qᴾ ⟩ᴾ ]Tmᴾ))
  λ N σ → cong ηᴾ (Raw.lam[] N σ)

app[]ᴾ : (F : Tmᴾ Δ (A Raw.⇒ᵗʸ B)) (M : Tmᴾ Δ A) (σ : Subᴾ Γ Δ)
  → appᴾ F M [ σ ]Tmᴾ ≡ appᴾ (F [ σ ]Tmᴾ) (M [ σ ]Tmᴾ)
app[]ᴾ = recᴾ-unique₃ ∥∥ᴾ-isPreorder
  (λ F M σ → appᴾ F M [ σ ]Tmᴾ) (λ F M σ → appᴾ (F [ σ ]Tmᴾ) (M [ σ ]Tmᴾ))
  λ F M σ → cong ηᴾ (Raw.app[] F M σ)

βif-trueᴾ : (T F : Tmᴾ Γ A) → ifᴾ trueᴾ T F ≤ T
βif-trueᴾ = recᴾ-hom₂ ∥∥ᴾ-isPreorder (λ T F → ifᴾ trueᴾ T F) (λ T _ → T)
  λ T F → hom-map ηᴾ (Raw.βif-true T F)

βif-falseᴾ : (T F : Tmᴾ Γ A) → ifᴾ falseᴾ T F ≤ F
βif-falseᴾ = recᴾ-hom₂ ∥∥ᴾ-isPreorder (λ T F → ifᴾ falseᴾ T F) (λ _ F → F)
  λ T F → hom-map ηᴾ (Raw.βif-false T F)

β×₁ᴾ : (M : Tmᴾ Γ A) (N : Tmᴾ Γ B) → fstᴾ (pairᴾ M N) ≤ M
β×₁ᴾ = recᴾ-hom₂ ∥∥ᴾ-isPreorder (λ M N → fstᴾ (pairᴾ M N)) (λ M _ → M)
  λ M N → hom-map ηᴾ (Raw.β×₁ M N)

β×₂ᴾ : (M : Tmᴾ Γ A) (N : Tmᴾ Γ B) → sndᴾ (pairᴾ M N) ≤ N
β×₂ᴾ = recᴾ-hom₂ ∥∥ᴾ-isPreorder (λ M N → sndᴾ (pairᴾ M N)) (λ _ N → N)
  λ M N → hom-map ηᴾ (Raw.β×₂ M N)

η×ᴾ : (P : Tmᴾ Γ (A Raw.×ᵗʸ B)) → pairᴾ (fstᴾ P) (sndᴾ P) ≤ P
η×ᴾ = recᴾ-hom ∥∥ᴾ-isPreorder (λ P → pairᴾ (fstᴾ P) (sndᴾ P)) (λ P → P)
  (hom-map ηᴾ ∘ Raw.η×)

β⇒ᴾ : (N : Tmᴾ (Γ Raw.▷ A) B) (M : Tmᴾ Γ A)
  → appᴾ (lamᴾ N) M ≤ N [ ⟨ idᴾ , M ⟩ᴾ ]Tmᴾ
β⇒ᴾ = recᴾ-hom₂ ∥∥ᴾ-isPreorder
  (λ N M → appᴾ (lamᴾ N) M) (λ N M → N [ ⟨ idᴾ , M ⟩ᴾ ]Tmᴾ)
  λ N M → hom-map ηᴾ (Raw.β⇒ N M)

η⇒ᴾ : (F : Tmᴾ Γ (A Raw.⇒ᵗʸ B)) → lamᴾ (appᴾ (F [ pᴾ ]Tmᴾ) qᴾ) ≤ F
η⇒ᴾ = recᴾ-hom ∥∥ᴾ-isPreorder (λ F → lamᴾ (appᴾ (F [ pᴾ ]Tmᴾ) qᴾ)) (λ F → F)
  (hom-map ηᴾ ∘ Raw.η⇒)
