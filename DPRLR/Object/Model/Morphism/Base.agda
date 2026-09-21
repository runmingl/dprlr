module DPRLR.Object.Model.Morphism.Base where

open import Cubical.Foundations.Prelude

open import DPRLR.Object.Model.Model using (SimpleCwF ; SimpleDirectedCwF)

record SortMorphism {ℓCS ℓC ℓMS ℓM : Level} (𝓒 : SimpleCwF ℓCS ℓC) (𝓜 : SimpleCwF ℓMS ℓM)
  : Type (ℓ-max ℓCS ℓMS) where
  private
    module C = SimpleCwF 𝓒
    module M = SimpleCwF 𝓜
  field
    Tyᶠ : C.Ty → M.Ty
    Ctxᶠ : C.Ctx → M.Ctx
    Boolᶠ : Tyᶠ C.Bool ≡ M.Bool
    ×ᶠ : (A B : C.Ty) → Tyᶠ (A C.×ᵗʸ B) ≡ (Tyᶠ A M.×ᵗʸ Tyᶠ B)
    ⇒ᶠ : (A B : C.Ty) → Tyᶠ (A C.⇒ᵗʸ B) ≡ (Tyᶠ A M.⇒ᵗʸ Tyᶠ B)
    εᶠ : Ctxᶠ C.ε ≡ M.ε
    ▷ᶠ : (Γ : C.Ctx) (A : C.Ty) → Ctxᶠ (Γ C.▷ A) ≡ (Ctxᶠ Γ M.▷ Tyᶠ A)

record MorphismOver {ℓCS ℓC ℓMS ℓM : Level}
  (𝓒 : SimpleCwF ℓCS ℓC) (𝓜 : SimpleCwF ℓMS ℓM)
  (sorts : SortMorphism 𝓒 𝓜)
  : Type (ℓ-max ℓCS (ℓ-max ℓC ℓM)) where
  private
    module C = SimpleCwF 𝓒
    module M = SimpleCwF 𝓜
  open SortMorphism sorts

  field
    Subᶠ : {Γ Δ : C.Ctx} → C.Sub Γ Δ → M.Sub (Ctxᶠ Γ) (Ctxᶠ Δ)
    Tmᶠ : {Γ : C.Ctx} {A : C.Ty} → C.Tm Γ A → M.Tm (Ctxᶠ Γ) (Tyᶠ A)

    idᶠ : {Γ : C.Ctx} → Subᶠ (C.id {Γ}) ≡ M.id
    ∘ᶠ : {Γ Δ Θ : C.Ctx} (τ : C.Sub Θ Δ) (σ : C.Sub Γ Θ)
      → Subᶠ (τ C.∘ σ) ≡ (Subᶠ τ M.∘ Subᶠ σ)
    ε-subᶠ : {Γ : C.Ctx}
      → PathP (λ i → M.Sub (Ctxᶠ Γ) (εᶠ i)) (Subᶠ C.ε-sub) M.ε-sub
    pᶠ : {Γ : C.Ctx} {A : C.Ty}
      → PathP (λ i → M.Sub (▷ᶠ Γ A i) (Ctxᶠ Γ)) (Subᶠ C.p) M.p
    qᶠ : {Γ : C.Ctx} {A : C.Ty}
      → PathP (λ i → M.Tm (▷ᶠ Γ A i) (Tyᶠ A)) (Tmᶠ C.q) M.q
    ⟨⟩ᶠ : {Γ Δ : C.Ctx} {A : C.Ty} (σ : C.Sub Γ Δ) (t : C.Tm Γ A)
      → PathP (λ i → M.Sub (Ctxᶠ Γ) (▷ᶠ Δ A i))
          (Subᶠ C.⟨ σ , t ⟩) M.⟨ Subᶠ σ , Tmᶠ t ⟩
    []ᶠ : {Γ Δ : C.Ctx} {A : C.Ty} (t : C.Tm Δ A) (σ : C.Sub Γ Δ)
      → Tmᶠ (t C.[ σ ]Tm) ≡ (Tmᶠ t M.[ Subᶠ σ ]Tm)
    trueᶠ : {Γ : C.Ctx}
      → PathP (λ i → M.Tm (Ctxᶠ Γ) (Boolᶠ i)) (Tmᶠ C.true) M.true
    falseᶠ : {Γ : C.Ctx}
      → PathP (λ i → M.Tm (Ctxᶠ Γ) (Boolᶠ i)) (Tmᶠ C.false) M.false
    ifᶠ : {Γ : C.Ctx} {A : C.Ty} (b : C.Tm Γ C.Bool) (t u : C.Tm Γ A)
      → Tmᶠ (C.if b then t else u)
        ≡ M.if subst (M.Tm (Ctxᶠ Γ)) Boolᶠ (Tmᶠ b) then Tmᶠ t else Tmᶠ u
    pairᶠ : {Γ : C.Ctx} {A B : C.Ty} (t : C.Tm Γ A) (u : C.Tm Γ B)
      → PathP (λ i → M.Tm (Ctxᶠ Γ) (×ᶠ A B i))
          (Tmᶠ (C.pair t u)) (M.pair (Tmᶠ t) (Tmᶠ u))
    fstᶠ : {Γ : C.Ctx} {A B : C.Ty} (t : C.Tm Γ (A C.×ᵗʸ B))
      → Tmᶠ (C.fst t) ≡ M.fst (subst (M.Tm (Ctxᶠ Γ)) (×ᶠ A B) (Tmᶠ t))
    sndᶠ : {Γ : C.Ctx} {A B : C.Ty} (t : C.Tm Γ (A C.×ᵗʸ B))
      → Tmᶠ (C.snd t) ≡ M.snd (subst (M.Tm (Ctxᶠ Γ)) (×ᶠ A B) (Tmᶠ t))
    lamᶠ : {Γ : C.Ctx} {A B : C.Ty} (t : C.Tm (Γ C.▷ A) B)
      → PathP (λ i → M.Tm (Ctxᶠ Γ) (⇒ᶠ A B i))
          (Tmᶠ (C.lam t))
          (M.lam (subst (λ Δ → M.Tm Δ (Tyᶠ B)) (▷ᶠ Γ A) (Tmᶠ t)))
    appᶠ : {Γ : C.Ctx} {A B : C.Ty} (t : C.Tm Γ (A C.⇒ᵗʸ B)) (u : C.Tm Γ A)
      → Tmᶠ (C.app t u)
        ≡ M.app (subst (M.Tm (Ctxᶠ Γ)) (⇒ᶠ A B) (Tmᶠ t)) (Tmᶠ u)

record SimpleMorphism {ℓCS ℓC ℓMS ℓM : Level}
  (𝓒 : SimpleCwF ℓCS ℓC) (𝓜 : SimpleCwF ℓMS ℓM)
  : Type (ℓ-max (ℓ-max ℓCS ℓC) (ℓ-max ℓMS ℓM)) where
  constructor simple-morphism
  field
    sorts : SortMorphism 𝓒 𝓜
    over : MorphismOver 𝓒 𝓜 sorts

  open SortMorphism sorts public
  open MorphismOver over public

identityMorphism : {ℓS ℓ : Level} (𝓒 : SimpleCwF ℓS ℓ) → SimpleMorphism 𝓒 𝓒
identityMorphism 𝓒 = record
    { sorts = record
      { Tyᶠ = λ A → A ; Ctxᶠ = λ Γ → Γ
      ; Boolᶠ = refl ; ×ᶠ = λ _ _ → refl ; ⇒ᶠ = λ _ _ → refl
      ; εᶠ = refl ; ▷ᶠ = λ _ _ → refl }
    ; over = record
      { Subᶠ = λ σ → σ ; Tmᶠ = λ t → t
      ; idᶠ = refl ; ∘ᶠ = λ _ _ → refl
      ; ε-subᶠ = refl ; pᶠ = refl ; qᶠ = refl
      ; ⟨⟩ᶠ = λ _ _ → refl ; []ᶠ = λ _ _ → refl
      ; trueᶠ = refl ; falseᶠ = refl
      ; ifᶠ = λ b t u → cong (λ b → C.if b then t else u) (sym (transportRefl b))
      ; pairᶠ = λ _ _ → refl
      ; fstᶠ = λ t → cong C.fst (sym (transportRefl t))
      ; sndᶠ = λ t → cong C.snd (sym (transportRefl t))
      ; lamᶠ = λ t → cong C.lam (sym (transportRefl t))
      ; appᶠ = λ t u → cong (λ t → C.app t u) (sym (transportRefl t))
      }
    }
  where module C = SimpleCwF 𝓒

isInitialDirected : {ℓCS ℓC : Level} → SimpleDirectedCwF ℓCS ℓC → (ℓMS ℓM : Level)
  → Type (ℓ-max (ℓ-max ℓCS ℓC) (ℓ-suc (ℓ-max ℓMS ℓM)))
isInitialDirected C ℓMS ℓM = (M : SimpleDirectedCwF ℓMS ℓM)
  → isContr (SimpleMorphism (SimpleDirectedCwF.cwf C) (SimpleDirectedCwF.cwf M))
