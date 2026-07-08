module DPRLR.Object.Simple.Syntax.Base where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)

open import DPRLR.Simplicial.Interval
open import DPRLR.Simplicial.Hom

infixl 30 _∘_
infixl 40 _[_]Tm
infixr 35 _▷_
infixr 25 _×ᵗʸ_ _⇒ᵗʸ_
infix  5 ⟨_,_⟩

data Ty : Type where
  Bool : Ty
  _×ᵗʸ_ : Ty → Ty → Ty
  _⇒ᵗʸ_ : Ty → Ty → Ty

data Ctx : Type where
  ε : Ctx
  _▷_ : Ctx → Ty → Ctx

mutual
  data Sub : Ctx → Ctx → Type

  data Tm : Ctx → Ty → Type

  q :
    {Γ : Ctx} {A : Ty}
    → Tm (Γ ▷ A) A

  _[_]Tm :
    {Γ Δ : Ctx} {A : Ty}
    → Tm Δ A → Sub Γ Δ → Tm Γ A

  data Sub where
    id  : {Γ : Ctx} → Sub Γ Γ
    _∘_ : {Γ Δ Θ : Ctx} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ

    ε-sub : {Γ : Ctx} → Sub Γ ε
    εη : {Γ : Ctx} (σ : Sub Γ ε) → σ ≡ ε-sub

    p :
      {Γ : Ctx} {A : Ty}
      → Sub (Γ ▷ A) Γ
    ⟨_,_⟩ :
      {Γ Δ : Ctx} {A : Ty}
      → (σ : Sub Γ Δ) → Tm Γ A → Sub Γ (Δ ▷ A)

    id-left :
      {Γ Δ : Ctx}
      (σ : Sub Γ Δ)
      → id ∘ σ ≡ σ
    id-right :
      {Γ Δ : Ctx}
      (σ : Sub Γ Δ)
      → σ ∘ id ≡ σ
    ∘-assoc :
      {Γ Δ Θ Ξ : Ctx}
      (ρ : Sub Θ Ξ) (τ : Sub Δ Θ) (σ : Sub Γ Δ)
      → (ρ ∘ τ) ∘ σ ≡ ρ ∘ (τ ∘ σ)

    p-⟨⟩ :
      {Γ Δ : Ctx} {A : Ty}
      (σ : Sub Γ Δ) (M : Tm Γ A)
      → p ∘ ⟨ σ , M ⟩ ≡ σ
    ▷η :
      {Γ : Ctx} {A : Ty}
      → ⟨_,_⟩ {Γ = Γ ▷ A} {Δ = Γ} {A = A} p q ≡ id
    ⟨⟩-∘ :
      {Γ Δ Θ : Ctx} {A : Ty}
      (σ : Sub Γ Δ) (M : Tm Γ A) (ρ : Sub Θ Γ)
      → ⟨ σ , M ⟩ ∘ ρ ≡ ⟨ σ ∘ ρ , M [ ρ ]Tm ⟩

  data Tm where
    qᶜ :
      {Γ : Ctx} {A : Ty}
      → Tm (Γ ▷ A) A

    substTmᶜ :
      {Γ Δ : Ctx} {A : Ty}
      → Tm Δ A → Sub Γ Δ → Tm Γ A
    Tm-id :
      {Γ : Ctx} {A : Ty}
      (M : Tm Γ A)
      → M [ id ]Tm ≡ M
    Tm-∘ :
      {Γ Δ Θ : Ctx} {A : Ty}
      (M : Tm Θ A) (τ : Sub Δ Θ) (σ : Sub Γ Δ)
      → (M [ τ ]Tm) [ σ ]Tm ≡ M [ τ ∘ σ ]Tm

    q-⟨⟩ :
      {Γ Δ : Ctx} {A : Ty}
      (σ : Sub Γ Δ) (M : Tm Γ A)
      → q [ ⟨ σ , M ⟩ ]Tm ≡ M

    true false : {Γ : Ctx} → Tm Γ Bool
    if_then_else_ :
      {Γ : Ctx} {A : Ty}
      → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
    true[] :
      {Γ Δ : Ctx} (σ : Sub Γ Δ)
      → true [ σ ]Tm ≡ true
    false[] :
      {Γ Δ : Ctx} (σ : Sub Γ Δ)
      → false [ σ ]Tm ≡ false
    if[] :
      {Γ Δ : Ctx} {A : Ty}
      (B : Tm Δ Bool) (T F : Tm Δ A) (σ : Sub Γ Δ)
      → (if B then T else F) [ σ ]Tm
        ≡ if B [ σ ]Tm then T [ σ ]Tm else F [ σ ]Tm

    pair : {Γ : Ctx} {A B : Ty} → Tm Γ A → Tm Γ B → Tm Γ (A ×ᵗʸ B)
    fst  : {Γ : Ctx} {A B : Ty} → Tm Γ (A ×ᵗʸ B) → Tm Γ A
    snd  : {Γ : Ctx} {A B : Ty} → Tm Γ (A ×ᵗʸ B) → Tm Γ B
    pair[] :
      {Γ Δ : Ctx} {A B : Ty}
      (M : Tm Δ A) (N : Tm Δ B) (σ : Sub Γ Δ)
      → pair M N [ σ ]Tm ≡ pair (M [ σ ]Tm) (N [ σ ]Tm)
    fst[] :
      {Γ Δ : Ctx} {A B : Ty}
      (P : Tm Δ (A ×ᵗʸ B)) (σ : Sub Γ Δ)
      → fst P [ σ ]Tm ≡ fst (P [ σ ]Tm)
    snd[] :
      {Γ Δ : Ctx} {A B : Ty}
      (P : Tm Δ (A ×ᵗʸ B)) (σ : Sub Γ Δ)
      → snd P [ σ ]Tm ≡ snd (P [ σ ]Tm)

    lam : {Γ : Ctx} {A B : Ty} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ᵗʸ B)
    app : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ᵗʸ B) → Tm Γ A → Tm Γ B
    lam[] :
      {Γ Δ : Ctx} {A B : Ty}
      (N : Tm (Δ ▷ A) B) (σ : Sub Γ Δ)
      → lam N [ σ ]Tm ≡ lam (N [ ⟨ σ ∘ p , q ⟩ ]Tm)
    app[] :
      {Γ Δ : Ctx} {A B : Ty}
      (F : Tm Δ (A ⇒ᵗʸ B)) (M : Tm Δ A) (σ : Sub Γ Δ)
      → app F M [ σ ]Tm ≡ app (F [ σ ]Tm) (M [ σ ]Tm)

    βif-true-rel :
      {Γ : Ctx} {A : Ty}
      (T F : Tm Γ A) → 𝟚 → Tm Γ A
    βif-true-left :
      {Γ : Ctx} {A : Ty}
      (T F : Tm Γ A)
      → βif-true-rel T F 𝟎 ≡ if true then T else F
    βif-true-right :
      {Γ : Ctx} {A : Ty}
      (T F : Tm Γ A)
      → βif-true-rel T F 𝟏 ≡ T

    βif-false-rel :
      {Γ : Ctx} {A : Ty}
      (T F : Tm Γ A) → 𝟚 → Tm Γ A
    βif-false-left :
      {Γ : Ctx} {A : Ty}
      (T F : Tm Γ A)
      → βif-false-rel T F 𝟎 ≡ if false then T else F
    βif-false-right :
      {Γ : Ctx} {A : Ty}
      (T F : Tm Γ A)
      → βif-false-rel T F 𝟏 ≡ F

    β×₁-rel :
      {Γ : Ctx} {A B : Ty}
      (M : Tm Γ A) (N : Tm Γ B) → 𝟚 → Tm Γ A
    β×₁-left :
      {Γ : Ctx} {A B : Ty}
      (M : Tm Γ A) (N : Tm Γ B)
      → β×₁-rel M N 𝟎 ≡ fst (pair M N)
    β×₁-right :
      {Γ : Ctx} {A B : Ty}
      (M : Tm Γ A) (N : Tm Γ B)
      → β×₁-rel M N 𝟏 ≡ M

    β×₂-rel :
      {Γ : Ctx} {A B : Ty}
      (M : Tm Γ A) (N : Tm Γ B) → 𝟚 → Tm Γ B
    β×₂-left :
      {Γ : Ctx} {A B : Ty}
      (M : Tm Γ A) (N : Tm Γ B)
      → β×₂-rel M N 𝟎 ≡ snd (pair M N)
    β×₂-right :
      {Γ : Ctx} {A B : Ty}
      (M : Tm Γ A) (N : Tm Γ B)
      → β×₂-rel M N 𝟏 ≡ N

    η×-rel :
      {Γ : Ctx} {A B : Ty}
      (P : Tm Γ (A ×ᵗʸ B)) → 𝟚 → Tm Γ (A ×ᵗʸ B)
    η×-left :
      {Γ : Ctx} {A B : Ty}
      (P : Tm Γ (A ×ᵗʸ B))
      → η×-rel P 𝟎 ≡ pair (fst P) (snd P)
    η×-right :
      {Γ : Ctx} {A B : Ty}
      (P : Tm Γ (A ×ᵗʸ B))
      → η×-rel P 𝟏 ≡ P

    β⇒-rel :
      {Γ : Ctx} {A B : Ty}
      (N : Tm (Γ ▷ A) B) (M : Tm Γ A) → 𝟚 → Tm Γ B
    β⇒-left :
      {Γ : Ctx} {A B : Ty}
      (N : Tm (Γ ▷ A) B) (M : Tm Γ A)
      → β⇒-rel N M 𝟎 ≡ app (lam N) M
    β⇒-right :
      {Γ : Ctx} {A B : Ty}
      (N : Tm (Γ ▷ A) B) (M : Tm Γ A)
      → β⇒-rel N M 𝟏 ≡ N [ ⟨ id , M ⟩ ]Tm

    η⇒-rel :
      {Γ : Ctx} {A B : Ty}
      (F : Tm Γ (A ⇒ᵗʸ B)) → 𝟚 → Tm Γ (A ⇒ᵗʸ B)
    η⇒-left :
      {Γ : Ctx} {A B : Ty}
      (F : Tm Γ (A ⇒ᵗʸ B))
      → η⇒-rel F 𝟎 ≡ lam (app (F [ p ]Tm) q)
    η⇒-right :
      {Γ : Ctx} {A B : Ty}
      (F : Tm Γ (A ⇒ᵗʸ B))
      → η⇒-rel F 𝟏 ≡ F

  q = qᶜ

  M [ σ ]Tm = substTmᶜ M σ

βif-true :
  {Γ : Ctx} {A : Ty}
  (T F : Tm Γ A)
  → if true then T else F ≤ T
βif-true T F =
  βif-true-rel T F , βif-true-left T F , βif-true-right T F

βif-false :
  {Γ : Ctx} {A : Ty}
  (T F : Tm Γ A)
  → if false then T else F ≤ F
βif-false T F =
  βif-false-rel T F , βif-false-left T F , βif-false-right T F

β×₁ :
  {Γ : Ctx} {A B : Ty}
  (M : Tm Γ A) (N : Tm Γ B)
  → fst (pair M N) ≤ M
β×₁ M N =
  β×₁-rel M N , β×₁-left M N , β×₁-right M N

β×₂ :
  {Γ : Ctx} {A B : Ty}
  (M : Tm Γ A) (N : Tm Γ B)
  → snd (pair M N) ≤ N
β×₂ M N =
  β×₂-rel M N , β×₂-left M N , β×₂-right M N

η× :
  {Γ : Ctx} {A B : Ty}
  (P : Tm Γ (A ×ᵗʸ B))
  → pair (fst P) (snd P) ≤ P
η× P =
  η×-rel P , η×-left P , η×-right P

β⇒ :
  {Γ : Ctx} {A B : Ty}
  (N : Tm (Γ ▷ A) B)
  (M : Tm Γ A)
  → app (lam N) M ≤ N [ ⟨ id , M ⟩ ]Tm
β⇒ N M =
  β⇒-rel N M , β⇒-left N M , β⇒-right N M

η⇒ :
  {Γ : Ctx} {A B : Ty}
  (F : Tm Γ (A ⇒ᵗʸ B))
  → lam (app (F [ p ]Tm) q) ≤ F
η⇒ F =
  η⇒-rel F , η⇒-left F , η⇒-right F
