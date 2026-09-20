module DPRLR.Object.Model.Model where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd ; lift)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (iso ; isoToEquiv)
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Segal
open import DPRLR.Simplicial.PreorderLocalization
  using (isPreorder ; isSetThinSegal→isPreorder ; isPreorder≃ ; isPreorder×)

record SimpleCwF (ℓS ℓM : Level) : Type (ℓ-suc (ℓ-max ℓS ℓM)) where
  infixl 30 _∘_
  infixl 40 _[_]Tm
  infixr 35 _▷_
  infixr 25 _×ᵗʸ_ _⇒ᵗʸ_
  infix  5 ⟨_,_⟩

  field
    Ctx : Type ℓS
    Ty  : Type ℓS
    Sub : Ctx → Ctx → Type ℓM
    Tm  : Ctx → Ty → Type ℓM

    id  : {Γ : Ctx} → Sub Γ Γ
    _∘_ : {Γ Δ Θ : Ctx} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
    id-left : {Γ Δ : Ctx} (σ : Sub Γ Δ) → id ∘ σ ≡ σ
    id-right : {Γ Δ : Ctx} (σ : Sub Γ Δ) → σ ∘ id ≡ σ
    ∘-assoc :
      {Γ Δ Θ Ξ : Ctx}
      (ρ : Sub Θ Ξ) (τ : Sub Δ Θ) (σ : Sub Γ Δ)
      → (ρ ∘ τ) ∘ σ ≡ ρ ∘ (τ ∘ σ)

    _[_]Tm :
      {Γ Δ : Ctx} {A : Ty}
      → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ A

    Tm-id :
      {Γ : Ctx} {A : Ty}
      (t : Tm Γ A)
      → t [ id ]Tm ≡ t
    Tm-∘ :
      {Γ Δ Θ : Ctx} {A : Ty}
      (t : Tm Θ A) (τ : Sub Δ Θ) (σ : Sub Γ Δ)
      → (t [ τ ]Tm) [ σ ]Tm ≡ t [ τ ∘ σ ]Tm

    ε : Ctx
    ε-sub : {Γ : Ctx} → Sub Γ ε
    εη : {Γ : Ctx} (σ : Sub Γ ε) → σ ≡ ε-sub

    _▷_ : Ctx → Ty → Ctx
    p   : {Γ : Ctx} {A : Ty} → Sub (Γ ▷ A) Γ
    q   : {Γ : Ctx} {A : Ty} → Tm (Γ ▷ A) A
    ⟨_,_⟩ :
      {Γ Δ : Ctx} {A : Ty}
      → (σ : Sub Γ Δ) → Tm Γ A → Sub Γ (Δ ▷ A)
    p-⟨⟩ :
      {Γ Δ : Ctx} {A : Ty}
      (σ : Sub Γ Δ) (t : Tm Γ A)
      → p ∘ ⟨ σ , t ⟩ ≡ σ
    q-⟨⟩ :
      {Γ Δ : Ctx} {A : Ty}
      (σ : Sub Γ Δ) (t : Tm Γ A)
      → q [ ⟨ σ , t ⟩ ]Tm ≡ t
    ▷η :
      {Γ : Ctx} {A : Ty}
      → ⟨_,_⟩ {Γ = Γ ▷ A} {Δ = Γ} {A = A} p q ≡ id
    ⟨⟩-∘ :
      {Γ Δ Θ : Ctx} {A : Ty}
      (σ : Sub Γ Δ) (t : Tm Γ A) (ρ : Sub Θ Γ)
      → ⟨ σ , t ⟩ ∘ ρ ≡ ⟨ σ ∘ ρ , t [ ρ ]Tm ⟩

  ▷-universal : (Γ Δ : Ctx) (A : Ty)
    → (Sub Γ Δ × Tm Γ A) ≃ Sub Γ (Δ ▷ A)
  ▷-universal Γ Δ A = isoToEquiv (iso
    (λ { (σ , t) → ⟨ σ , t ⟩ })
    (λ σ → (p ∘ σ) , (q [ σ ]Tm))
    (λ σ → sym (⟨⟩-∘ p q σ)
      ∙ cong (λ τ → τ ∘ σ) ▷η ∙ id-left σ)
    (λ { (σ , t) i → p-⟨⟩ σ t i , q-⟨⟩ σ t i }))

  lift :
    {Γ Δ : Ctx} {A : Ty}
    (σ : Sub Γ Δ)
    → Sub (Γ ▷ A) (Δ ▷ A)
  lift σ = ⟨ σ ∘ p , q ⟩

  field
    Bool : Ty
    true false : {Γ : Ctx} → Tm Γ Bool
    if_then_else_ :
      {Γ : Ctx} {A : Ty}
      → Tm Γ Bool
      → Tm Γ A
      → Tm Γ A
      → Tm Γ A
    true[] :
      {Γ Δ : Ctx} (σ : Sub Γ Δ)
      → true [ σ ]Tm ≡ true
    false[] :
      {Γ Δ : Ctx} (σ : Sub Γ Δ)
      → false [ σ ]Tm ≡ false
    if[] :
      {Γ Δ : Ctx} {A : Ty}
      (b : Tm Δ Bool) (t f : Tm Δ A) (σ : Sub Γ Δ)
      → (if b then t else f) [ σ ]Tm
        ≡ if b [ σ ]Tm then t [ σ ]Tm else f [ σ ]Tm
    βif-true :
      {Γ : Ctx} {A : Ty}
      (t f : Tm Γ A)
      → if true then t else f ≤ t
    βif-false :
      {Γ : Ctx} {A : Ty}
      (t f : Tm Γ A)
      → if false then t else f ≤ f

    _×ᵗʸ_ : Ty → Ty → Ty
    pair  : {Γ : Ctx} {A B : Ty} → Tm Γ A → Tm Γ B → Tm Γ (A ×ᵗʸ B)
    fst   : {Γ : Ctx} {A B : Ty} → Tm Γ (A ×ᵗʸ B) → Tm Γ A
    snd   : {Γ : Ctx} {A B : Ty} → Tm Γ (A ×ᵗʸ B) → Tm Γ B
    pair[] :
      {Γ Δ : Ctx} {A B : Ty}
      (a : Tm Δ A) (b : Tm Δ B) (σ : Sub Γ Δ)
      → pair a b [ σ ]Tm ≡ pair (a [ σ ]Tm) (b [ σ ]Tm)
    fst[] :
      {Γ Δ : Ctx} {A B : Ty}
      (t : Tm Δ (A ×ᵗʸ B)) (σ : Sub Γ Δ)
      → fst t [ σ ]Tm ≡ fst (t [ σ ]Tm)
    snd[] :
      {Γ Δ : Ctx} {A B : Ty}
      (t : Tm Δ (A ×ᵗʸ B)) (σ : Sub Γ Δ)
      → snd t [ σ ]Tm ≡ snd (t [ σ ]Tm)

    _⇒ᵗʸ_ : Ty → Ty → Ty
    lam   : {Γ : Ctx} {A B : Ty} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ᵗʸ B)
    app   : {Γ : Ctx} {A B : Ty} → Tm Γ (A ⇒ᵗʸ B) → Tm Γ A → Tm Γ B
    lam[] :
      {Γ Δ : Ctx} {A B : Ty}
      (N : Tm (Δ ▷ A) B) (σ : Sub Γ Δ)
      → lam N [ σ ]Tm ≡ lam (N [ lift {A = A} σ ]Tm)
    app[] :
      {Γ Δ : Ctx} {A B : Ty}
      (F : Tm Δ (A ⇒ᵗʸ B)) (M : Tm Δ A) (σ : Sub Γ Δ)
      → app F M [ σ ]Tm ≡ app (F [ σ ]Tm) (M [ σ ]Tm)
    β⇒ :
      {Γ : Ctx} {A B : Ty}
      (N : Tm (Γ ▷ A) B)
      (M : Tm Γ A)
      → app (lam N) M ≤ N [ ⟨ id , M ⟩ ]Tm
    η⇒ :
      {Γ : Ctx} {A B : Ty}
      (F : Tm Γ (A ⇒ᵗʸ B))
      → lam (app (F [ p ]Tm) q) ≤ F

    β×₁ : {Γ : Ctx} {A B : Ty} (a : Tm Γ A) (b : Tm Γ B)
      → fst (pair a b) ≤ a
    β×₂ : {Γ : Ctx} {A B : Ty} (a : Tm Γ A) (b : Tm Γ B)
      → snd (pair a b) ≤ b
    η× : {Γ : Ctx} {A B : Ty} (t : Tm Γ (A ×ᵗʸ B))
      → pair (fst t) (snd t) ≤ t

  p-⟨⟩[] :
    {Γ Δ Θ : Ctx} {A : Ty}
    (σ : Sub Γ Δ) (t : Tm Γ A) (ρ : Sub Θ Γ)
    → p ∘ (⟨ σ , t ⟩ ∘ ρ) ≡ σ ∘ ρ
  p-⟨⟩[] σ t ρ =
    cong (λ δ → p ∘ δ) (⟨⟩-∘ σ t ρ)
    ∙ p-⟨⟩ (σ ∘ ρ) (t [ ρ ]Tm)

  lift-⟨id⟩ :
    {Γ Δ : Ctx} {A : Ty}
    (σ : Sub Γ Δ)
    (M : Tm Γ A)
    → lift σ ∘ ⟨ id , M ⟩ ≡ ⟨ σ , M ⟩
  lift-⟨id⟩ σ M =
    ⟨⟩-∘ (σ ∘ p) q ⟨ id , M ⟩
    ∙ (λ i → ⟨ p-path i , q-path i ⟩)
    where
    p-path :
      (σ ∘ p) ∘ ⟨ id , M ⟩ ≡ σ
    p-path =
      ∘-assoc σ p ⟨ id , M ⟩
      ∙ cong (λ τ → σ ∘ τ) (p-⟨⟩ id M)
      ∙ id-right σ

    q-path :
      q [ ⟨ id , M ⟩ ]Tm ≡ M
    q-path =
      q-⟨⟩ id M

  β⇒-subst :
    {Γ Δ : Ctx} {A B : Ty}
    (N : Tm (Δ ▷ A) B)
    (σ : Sub Γ Δ)
    (M : Tm Γ A)
    → app (lam N [ σ ]Tm) M ≤ N [ ⟨ σ , M ⟩ ]Tm
  β⇒-subst {A = A} N σ M =
    subst
      (λ s → s ≤ N [ ⟨ σ , M ⟩ ]Tm)
      (sym (cong (λ F → app F M) source-path))
      (subst
        (λ t → app (lam Nσ) M ≤ t)
        contractum-path
        (β⇒ Nσ M))
    where
    Nσ = N [ lift {A = A} σ ]Tm
    source-path = lam[] N σ

    contractum-path :
      Nσ [ ⟨ id , M ⟩ ]Tm ≡ N [ ⟨ σ , M ⟩ ]Tm
    contractum-path =
      Tm-∘ N (lift {A = A} σ) ⟨ id , M ⟩
      ∙ cong (λ ρ → N [ ρ ]Tm) (lift-⟨id⟩ σ M)

record SimpleDirectedCwF (ℓS ℓM : Level) : Type (ℓ-suc (ℓ-max ℓS ℓM)) where
  infixr 0 _≤⟨_⟩_
  infix 1 _∎≤

  field
    cwf : SimpleCwF ℓS ℓM

  open SimpleCwF cwf public

  field
    sub-set : (Γ Δ : Ctx) → isSet (Sub Γ Δ)
    tm-set : (Γ : Ctx) (A : Ty) → isSet (Tm Γ A)
    tm-thin : (Γ : Ctx) (A : Ty) → isThin (Tm Γ A)
    tm-segal : (Γ : Ctx) (A : Ty) → isSegal (Tm Γ A)

  tm-local : (Γ : Ctx) (A : Ty) → isPreorder (Tm Γ A)
  tm-local Γ A = isSetThinSegal→isPreorder
    (tm-set Γ A) (tm-thin Γ A) (tm-segal Γ A)

  sub-extension-local : (Γ Δ : Ctx) (A : Ty)
    → isPreorder (Sub Γ Δ) → isPreorder (Sub Γ (Δ ▷ A))
  sub-extension-local Γ Δ A localΔ =
    isPreorder≃ (▷-universal Γ Δ A) (isPreorder× localΔ (tm-local Γ A))

  tm-∙ : {Γ : Ctx} {A : Ty} {t u v : Tm Γ A}
    → t ≤ u → u ≤ v → t ≤ v
  tm-∙ {Γ} {A} = segal-compose (tm-segal Γ A)

  _≤⟨_⟩_ : {Γ : Ctx} {A : Ty} (t : Tm Γ A) {u v : Tm Γ A}
    → t ≤ u → u ≤ v → t ≤ v
  t ≤⟨ h ⟩ k = tm-∙ h k

  _∎≤ : {Γ : Ctx} {A : Ty} (t : Tm Γ A) → t ≤ t
  t ∎≤ = hom-refl t

open SimpleDirectedCwF public
