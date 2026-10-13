module DPRLR.Object.Syntax.Initiality where

open import Cubical.Foundations.Prelude

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.PreorderLocalization
open import DPRLR.Object.Model.Model
open import DPRLR.Object.Model.Morphism.Base
open import DPRLR.Object.Model.Morphism.Properties
open import DPRLR.Object.Syntax.Localized
open import DPRLR.Object.Syntax.Model
import DPRLR.Object.Syntax.Raw as Raw

module _ {ℓS ℓM : Level} (𝓜 : SimpleCwF ℓS ℓM) where
  private
    module M = SimpleCwF 𝓜

    mutual
      Ctxʳ : Raw.Ctx → M.Ctx
      Ctxʳ Raw.ε = M.ε
      Ctxʳ (Γ Raw.▷ A) = Ctxʳ Γ M.▷ Tyʳ A

      Tyʳ : Raw.Ty → M.Ty
      Tyʳ Raw.Bool = M.Bool
      Tyʳ (A Raw.×ᵗʸ B) = Tyʳ A M.×ᵗʸ Tyʳ B
      Tyʳ (A Raw.⇒ᵗʸ B) = Tyʳ A M.⇒ᵗʸ Tyʳ B

      Subʳ :
        {Γ Δ : Raw.Ctx}
        (σ : Raw.Sub Γ Δ)
        → ⌞ M.Sub (Ctxʳ Γ) (Ctxʳ Δ) ⌟
      Subʳ Raw.id = M.id
      Subʳ (τ Raw.∘ σ) = Subʳ τ M.∘ Subʳ σ
      Subʳ Raw.ε-sub = M.ε-sub
      Subʳ (Raw.εη σ i) = M.εη (Subʳ σ) i
      Subʳ Raw.p = M.p
      Subʳ Raw.⟨ σ , M ⟩ = M.⟨ Subʳ σ , Tmʳ M ⟩
      Subʳ (Raw.id-left σ i) = M.id-left (Subʳ σ) i
      Subʳ (Raw.id-right σ i) = M.id-right (Subʳ σ) i
      Subʳ (Raw.∘-assoc ρ τ σ i) = M.∘-assoc (Subʳ ρ) (Subʳ τ) (Subʳ σ) i
      Subʳ (Raw.p-⟨⟩ σ M i) = M.p-⟨⟩ (Subʳ σ) (Tmʳ M) i
      Subʳ (Raw.▷η i) = M.▷η i
      Subʳ (Raw.⟨⟩-∘ σ M ρ i) = M.⟨⟩-∘ (Subʳ σ) (Tmʳ M) (Subʳ ρ) i

      Tmʳ :
        {Γ : Raw.Ctx} {A : Raw.Ty}
        (M : Raw.Tm Γ A)
        → ⌞ M.Tm (Ctxʳ Γ) (Tyʳ A) ⌟
      Tmʳ Raw.qᶜ = M.q
      Tmʳ (Raw.substTmᶜ M σ) = Tmʳ M M.[ Subʳ σ ]Tm
      Tmʳ (Raw.Tm-id M i) = M.Tm-id (Tmʳ M) i
      Tmʳ (Raw.Tm-∘ M τ σ i) = M.Tm-∘ (Tmʳ M) (Subʳ τ) (Subʳ σ) i
      Tmʳ (Raw.q-⟨⟩ σ M i) = M.q-⟨⟩ (Subʳ σ) (Tmʳ M) i
      Tmʳ Raw.true = M.true
      Tmʳ Raw.false = M.false
      Tmʳ (Raw.if B then T else F) = M.if_then_else_ (Tmʳ B) (Tmʳ T) (Tmʳ F)
      Tmʳ (Raw.true[] σ i) = M.true[] (Subʳ σ) i
      Tmʳ (Raw.false[] σ i) = M.false[] (Subʳ σ) i
      Tmʳ (Raw.if[] B T F σ i) =
        M.if[] (Tmʳ B) (Tmʳ T) (Tmʳ F) (Subʳ σ) i
      Tmʳ (Raw.pair M N) = M.pair (Tmʳ M) (Tmʳ N)
      Tmʳ (Raw.fst P) = M.fst (Tmʳ P)
      Tmʳ (Raw.snd P) = M.snd (Tmʳ P)
      Tmʳ (Raw.pair[] M N σ i) = M.pair[] (Tmʳ M) (Tmʳ N) (Subʳ σ) i
      Tmʳ (Raw.fst[] P σ i) = M.fst[] (Tmʳ P) (Subʳ σ) i
      Tmʳ (Raw.snd[] P σ i) = M.snd[] (Tmʳ P) (Subʳ σ) i
      Tmʳ (Raw.lam N) = M.lam (Tmʳ N)
      Tmʳ (Raw.app F M) = M.app (Tmʳ F) (Tmʳ M)
      Tmʳ (Raw.lam[] N σ i) = M.lam[] (Tmʳ N) (Subʳ σ) i
      Tmʳ (Raw.app[] F M σ i) = M.app[] (Tmʳ F) (Tmʳ M) (Subʳ σ) i
      Tmʳ (Raw.βif-true-rel T F i) = hom-path (M.βif-true (Tmʳ T) (Tmʳ F)) i
      Tmʳ (Raw.βif-true-left T F i) = left-endpoint (M.βif-true (Tmʳ T) (Tmʳ F)) i
      Tmʳ (Raw.βif-true-right T F i) = right-endpoint (M.βif-true (Tmʳ T) (Tmʳ F)) i
      Tmʳ (Raw.βif-false-rel T F i) = hom-path (M.βif-false (Tmʳ T) (Tmʳ F)) i
      Tmʳ (Raw.βif-false-left T F i) = left-endpoint (M.βif-false (Tmʳ T) (Tmʳ F)) i
      Tmʳ (Raw.βif-false-right T F i) = right-endpoint (M.βif-false (Tmʳ T) (Tmʳ F)) i
      Tmʳ (Raw.β×₁-rel M N i) = hom-path (M.β×₁ (Tmʳ M) (Tmʳ N)) i
      Tmʳ (Raw.β×₁-left M N i) = left-endpoint (M.β×₁ (Tmʳ M) (Tmʳ N)) i
      Tmʳ (Raw.β×₁-right M N i) = right-endpoint (M.β×₁ (Tmʳ M) (Tmʳ N)) i
      Tmʳ (Raw.β×₂-rel M N i) = hom-path (M.β×₂ (Tmʳ M) (Tmʳ N)) i
      Tmʳ (Raw.β×₂-left M N i) = left-endpoint (M.β×₂ (Tmʳ M) (Tmʳ N)) i
      Tmʳ (Raw.β×₂-right M N i) = right-endpoint (M.β×₂ (Tmʳ M) (Tmʳ N)) i
      Tmʳ (Raw.η×-rel P i) = hom-path (M.η× (Tmʳ P)) i
      Tmʳ (Raw.η×-left P i) = left-endpoint (M.η× (Tmʳ P)) i
      Tmʳ (Raw.η×-right P i) = right-endpoint (M.η× (Tmʳ P)) i
      Tmʳ (Raw.β⇒-rel N M i) = hom-path (M.β⇒ (Tmʳ N) (Tmʳ M)) i
      Tmʳ (Raw.β⇒-left N M i) = left-endpoint (M.β⇒ (Tmʳ N) (Tmʳ M)) i
      Tmʳ (Raw.β⇒-right N M i) = right-endpoint (M.β⇒ (Tmʳ N) (Tmʳ M)) i
      Tmʳ (Raw.η⇒-rel F i) = hom-path (M.η⇒ (Tmʳ F)) i
      Tmʳ (Raw.η⇒-left F i) = left-endpoint (M.η⇒ (Tmʳ F)) i
      Tmʳ (Raw.η⇒-right F i) = right-endpoint (M.η⇒ (Tmʳ F)) i

    Subᶠ : {Γ Δ : Raw.Ctx} → Subᴾ Γ Δ → ⌞ M.Sub (Ctxʳ Γ) (Ctxʳ Δ) ⌟
    Subᶠ = recᴾ (M.sub-local _ _) Subʳ

    Tmᶠ : {Γ : Raw.Ctx} {A : Raw.Ty} → Tmᴾ Γ A → ⌞ M.Tm (Ctxʳ Γ) (Tyʳ A) ⌟
    Tmᶠ = recᴾ (M.tm-local _ _) Tmʳ

    sorts : SortMorphism SyntaxModel 𝓜
    sorts = record
      { Tyᶠ = Tyʳ ; Ctxᶠ = Ctxʳ ; Boolᶠ = refl
      ; ×ᶠ = λ _ _ → refl ; ⇒ᶠ = λ _ _ → refl
      ; εᶠ = refl ; ▷ᶠ = λ _ _ → refl }

    sorts-isContr : isContr (SortMorphism SyntaxModel 𝓜)
    sorts-isContr = sorts , contract
      where
      contract : (s : SortMorphism SyntaxModel 𝓜) → sorts ≡ s
      contract s = path
        where
        open SortMorphism s

        ty : (A : Raw.Ty) → Tyʳ A ≡ Tyᶠ A
        ty Raw.Bool = sym Boolᶠ
        ty (A Raw.×ᵗʸ B) = cong₂ M._×ᵗʸ_ (ty A) (ty B) ∙ sym (×ᶠ A B)
        ty (A Raw.⇒ᵗʸ B) = cong₂ M._⇒ᵗʸ_ (ty A) (ty B) ∙ sym (⇒ᶠ A B)

        ctx : (Γ : Raw.Ctx) → Ctxʳ Γ ≡ Ctxᶠ Γ
        ctx Raw.ε = sym εᶠ
        ctx (Γ Raw.▷ A) = cong₂ M._▷_ (ctx Γ) (ty A) ∙ sym (▷ᶠ Γ A)

        path : sorts ≡ s
        SortMorphism.Tyᶠ (path i) = λ A → ty A i
        SortMorphism.Ctxᶠ (path i) = λ Γ → ctx Γ i
        SortMorphism.Boolᶠ (path i) j = Boolᶠ (~ i ∨ j)
        SortMorphism.×ᶠ (path i) A B j =
          compPath-filler (cong₂ M._×ᵗʸ_ (ty A) (ty B)) (sym (×ᶠ A B)) (~ j) i
        SortMorphism.⇒ᶠ (path i) A B j =
          compPath-filler (cong₂ M._⇒ᵗʸ_ (ty A) (ty B)) (sym (⇒ᶠ A B)) (~ j) i
        SortMorphism.εᶠ (path i) j = εᶠ (~ i ∨ j)
        SortMorphism.▷ᶠ (path i) Γ A j =
          compPath-filler (cong₂ M._▷_ (ctx Γ) (ty A)) (sym (▷ᶠ Γ A)) (~ j) i

    recursor : MorphismOver SyntaxModel 𝓜 sorts
    MorphismOver.Subᶠ recursor = Subᶠ
    MorphismOver.Tmᶠ recursor = Tmᶠ
    MorphismOver.idᶠ recursor = refl
    MorphismOver.∘ᶠ recursor = recᴾ-unique₂ (M.sub-local _ _)
      (λ τ σ → Subᶠ (τ ∘ᴾ σ)) (λ τ σ → Subᶠ τ M.∘ Subᶠ σ) (λ _ _ → refl)
    MorphismOver.ε-subᶠ recursor = refl
    MorphismOver.pᶠ recursor = refl
    MorphismOver.qᶠ recursor = refl
    MorphismOver.⟨⟩ᶠ recursor = recᴾ-uniqueP₂ (M.sub-local _ _)
      (λ σ t → Subᶠ ⟨ σ , t ⟩ᴾ) (λ σ t → M.⟨ Subᶠ σ , Tmᶠ t ⟩) (λ _ _ → refl)
    MorphismOver.[]ᶠ recursor = recᴾ-unique₂ (M.tm-local _ _)
      (λ t σ → Tmᶠ (t [ σ ]Tmᴾ)) (λ t σ → Tmᶠ t M.[ Subᶠ σ ]Tm) (λ _ _ → refl)
    MorphismOver.trueᶠ recursor = refl
    MorphismOver.falseᶠ recursor = refl
    MorphismOver.ifᶠ recursor {Γ = Γ} = recᴾ-unique₃ (M.tm-local _ _)
      (λ b t u → Tmᶠ (ifᴾ b t u))
      (λ b t u → M.if subst (λ X → ⌞ M.Tm (Ctxʳ Γ) X ⌟) refl (Tmᶠ b) then Tmᶠ t else Tmᶠ u)
      (λ b t u → cong (λ x → M.if x then Tmʳ t else Tmʳ u) (sym (transportRefl (Tmʳ b))))
    MorphismOver.pairᶠ recursor = recᴾ-uniqueP₂ (M.tm-local _ _)
      (λ t u → Tmᶠ (pairᴾ t u)) (λ t u → M.pair (Tmᶠ t) (Tmᶠ u)) (λ _ _ → refl)
    MorphismOver.fstᶠ recursor {Γ = Γ} = recᴾ-unique (M.tm-local _ _)
      (λ t → Tmᶠ (fstᴾ t)) (λ t → M.fst (subst (λ X → ⌞ M.Tm (Ctxʳ Γ) X ⌟) refl (Tmᶠ t)))
      (λ t → cong M.fst (sym (transportRefl (Tmʳ t))))
    MorphismOver.sndᶠ recursor {Γ = Γ} = recᴾ-unique (M.tm-local _ _)
      (λ t → Tmᶠ (sndᴾ t)) (λ t → M.snd (subst (λ X → ⌞ M.Tm (Ctxʳ Γ) X ⌟) refl (Tmᶠ t)))
      (λ t → cong M.snd (sym (transportRefl (Tmʳ t))))
    MorphismOver.lamᶠ recursor {B = B} = recᴾ-uniqueP (M.tm-local _ _)
      (λ t → Tmᶠ (lamᴾ t))
      (λ t → M.lam (subst (λ Δ → ⌞ M.Tm Δ (Tyʳ B) ⌟) refl (Tmᶠ t)))
      (λ t → cong M.lam (sym (transportRefl (Tmʳ t))))
    MorphismOver.appᶠ recursor {Γ = Γ} = recᴾ-unique₂ (M.tm-local _ _)
      (λ t u → Tmᶠ (appᴾ t u))
      (λ t u → M.app (subst (λ X → ⌞ M.Tm (Ctxʳ Γ) X ⌟) refl (Tmᶠ t)) (Tmᶠ u))
      (λ t u → cong (λ x → M.app x (Tmʳ u)) (sym (transportRefl (Tmʳ t))))

    module Uniqueness (f : MorphismOver SyntaxModel 𝓜 sorts) where
      private
        module R = MorphismOver recursor
        module F = MorphismOver f

      SubEq : {Γ Δ : Raw.Ctx} → Subᴾ Γ Δ → Type ℓM
      SubEq σ = Subᶠ σ ≡ F.Subᶠ σ

      TmEq : {Γ : Raw.Ctx} {A : Raw.Ty} → Tmᴾ Γ A → Type ℓM
      TmEq t = Tmᶠ t ≡ F.Tmᶠ t

      sub-path : {Γ Δ : Raw.Ctx} {σ τ : Subᴾ Γ Δ} (p : σ ≡ τ)
        (u : SubEq σ) (v : SubEq τ) → PathP (λ i → SubEq (p i)) u v
      sub-path p u v = isProp→PathP (λ i → M.sub-set _ _ _ _) u v

      tm-path : {Γ : Raw.Ctx} {A : Raw.Ty} {t u : Tmᴾ Γ A} (p : t ≡ u)
        (v : TmEq t) (w : TmEq u) → PathP (λ i → TmEq (p i)) v w
      tm-path p v w = isProp→PathP (λ i → M.tm-set _ _ _ _) v w

      tm-hom : {Γ : Raw.Ctx} {A : Raw.Ty} {t u : Tmᴾ Γ A} (h : t ≤ u)
        (v : TmEq t) (w : TmEq u) → TmEq ⊢ v ≤[ h ] w
      tm-hom h v w = HomP-thin-≡ {f = Tmᶠ} {g = F.Tmᶠ} (M.tm-thin _ _) h v w

      ∘-eq : {Γ Δ Θ : Raw.Ctx} {τ : Subᴾ Θ Δ} {σ : Subᴾ Γ Θ}
        → SubEq τ → SubEq σ → SubEq (τ ∘ᴾ σ)
      ∘-eq {τ = τ} {σ} p q = R.∘ᶠ τ σ ∙ cong₂ M._∘_ p q ∙ sym (F.∘ᶠ τ σ)

      ⟨⟩-eq : {Γ Δ : Raw.Ctx} {A : Raw.Ty} {σ : Subᴾ Γ Δ} {t : Tmᴾ Γ A}
        → SubEq σ → TmEq t → SubEq ⟨ σ , t ⟩ᴾ
      ⟨⟩-eq {σ = σ} {t} p q = R.⟨⟩ᶠ σ t ∙ cong₂ M.⟨_,_⟩ p q ∙ sym (F.⟨⟩ᶠ σ t)

      []-eq : {Γ Δ : Raw.Ctx} {A : Raw.Ty} {t : Tmᴾ Δ A} {σ : Subᴾ Γ Δ}
        → TmEq t → SubEq σ → TmEq (t [ σ ]Tmᴾ)
      []-eq {t = t} {σ} p q = R.[]ᶠ t σ ∙ cong₂ M._[_]Tm p q ∙ sym (F.[]ᶠ t σ)

      if-eq : {Γ : Raw.Ctx} {A : Raw.Ty} {b : Tmᴾ Γ Raw.Bool} {t u : Tmᴾ Γ A}
        → TmEq b → TmEq t → TmEq u → TmEq (ifᴾ b t u)
      if-eq {Γ} {b = b} {t} {u} p q r = R.ifᶠ b t u
        ∙ (λ i → M.if subst (λ X → ⌞ M.Tm (Ctxʳ Γ) X ⌟) refl (p i) then q i else r i)
        ∙ sym (F.ifᶠ b t u)

      pair-eq : {Γ : Raw.Ctx} {A B : Raw.Ty} {t : Tmᴾ Γ A} {u : Tmᴾ Γ B}
        → TmEq t → TmEq u → TmEq (pairᴾ t u)
      pair-eq {t = t} {u} p q = R.pairᶠ t u ∙ cong₂ M.pair p q ∙ sym (F.pairᶠ t u)

      fst-eq : {Γ : Raw.Ctx} {A B : Raw.Ty} {t : Tmᴾ Γ (A Raw.×ᵗʸ B)}
        → TmEq t → TmEq (fstᴾ t)
      fst-eq {Γ} {t = t} p = R.fstᶠ t
        ∙ cong (λ x → M.fst (subst (λ X → ⌞ M.Tm (Ctxʳ Γ) X ⌟) refl x)) p ∙ sym (F.fstᶠ t)

      snd-eq : {Γ : Raw.Ctx} {A B : Raw.Ty} {t : Tmᴾ Γ (A Raw.×ᵗʸ B)}
        → TmEq t → TmEq (sndᴾ t)
      snd-eq {Γ} {t = t} p = R.sndᶠ t
        ∙ cong (λ x → M.snd (subst (λ X → ⌞ M.Tm (Ctxʳ Γ) X ⌟) refl x)) p ∙ sym (F.sndᶠ t)

      lam-eq : {Γ : Raw.Ctx} {A B : Raw.Ty} {t : Tmᴾ (Γ Raw.▷ A) B}
        → TmEq t → TmEq (lamᴾ t)
      lam-eq {B = B} {t} p = R.lamᶠ t
        ∙ cong (λ x → M.lam (subst (λ Δ → ⌞ M.Tm Δ (Tyʳ B) ⌟) refl x)) p ∙ sym (F.lamᶠ t)

      app-eq : {Γ : Raw.Ctx} {A B : Raw.Ty} {t : Tmᴾ Γ (A Raw.⇒ᵗʸ B)} {u : Tmᴾ Γ A}
        → TmEq t → TmEq u → TmEq (appᴾ t u)
      app-eq {Γ} {t = t} {u} p q = R.appᶠ t u
        ∙ cong₂ (λ x y → M.app (subst (λ X → ⌞ M.Tm (Ctxʳ Γ) X ⌟) refl x) y) p q
        ∙ sym (F.appᶠ t u)

      mutual
        sub-raw-unique : {Γ Δ : Raw.Ctx} (σ : Raw.Sub Γ Δ) → SubEq (ηSubᴾ σ)
        sub-raw-unique Raw.id = sym F.idᶠ
        sub-raw-unique (τ Raw.∘ σ) = ∘-eq (sub-raw-unique τ) (sub-raw-unique σ)
        sub-raw-unique Raw.ε-sub = sym F.ε-subᶠ
        sub-raw-unique Raw.p = sym F.pᶠ
        sub-raw-unique Raw.⟨ σ , t ⟩ = ⟨⟩-eq (sub-raw-unique σ) (tm-raw-unique t)

        sub-raw-unique (Raw.εη σ i) =
          sub-path (cong ηSubᴾ (Raw.εη σ))
            (sub-raw-unique σ)
            (sym F.ε-subᶠ) i
        sub-raw-unique (Raw.id-left σ i) =
          sub-path (cong ηSubᴾ (Raw.id-left σ))
            (∘-eq (sym F.idᶠ) (sub-raw-unique σ))
            (sub-raw-unique σ) i
        sub-raw-unique (Raw.id-right σ i) =
          sub-path (cong ηSubᴾ (Raw.id-right σ))
            (∘-eq (sub-raw-unique σ) (sym F.idᶠ))
            (sub-raw-unique σ) i
        sub-raw-unique (Raw.∘-assoc ρ τ σ i) =
          sub-path (cong ηSubᴾ (Raw.∘-assoc ρ τ σ))
            (∘-eq (∘-eq (sub-raw-unique ρ) (sub-raw-unique τ)) (sub-raw-unique σ))
            (∘-eq (sub-raw-unique ρ) (∘-eq (sub-raw-unique τ) (sub-raw-unique σ))) i
        sub-raw-unique (Raw.p-⟨⟩ σ t i) =
          sub-path (cong ηSubᴾ (Raw.p-⟨⟩ σ t))
            (∘-eq (sym F.pᶠ) (⟨⟩-eq (sub-raw-unique σ) (tm-raw-unique t)))
            (sub-raw-unique σ) i
        sub-raw-unique (Raw.▷η i) =
          sub-path (cong ηSubᴾ Raw.▷η)
            (⟨⟩-eq (sym F.pᶠ) (sym F.qᶠ))
            (sym F.idᶠ) i
        sub-raw-unique (Raw.⟨⟩-∘ σ t ρ i) =
          sub-path (cong ηSubᴾ (Raw.⟨⟩-∘ σ t ρ))
            (∘-eq (⟨⟩-eq (sub-raw-unique σ) (tm-raw-unique t)) (sub-raw-unique ρ))
            (⟨⟩-eq (∘-eq (sub-raw-unique σ) (sub-raw-unique ρ)) ([]-eq (tm-raw-unique t) (sub-raw-unique ρ))) i

        tm-raw-unique : {Γ : Raw.Ctx} {A : Raw.Ty} (t : Raw.Tm Γ A) → TmEq (ηTmᴾ t)
        tm-raw-unique Raw.qᶜ = sym F.qᶠ
        tm-raw-unique (Raw.substTmᶜ t σ) = []-eq (tm-raw-unique t) (sub-raw-unique σ)
        tm-raw-unique Raw.true = sym F.trueᶠ
        tm-raw-unique Raw.false = sym F.falseᶠ
        tm-raw-unique (Raw.if b then t else u) = if-eq (tm-raw-unique b) (tm-raw-unique t) (tm-raw-unique u)
        tm-raw-unique (Raw.pair t u) = pair-eq (tm-raw-unique t) (tm-raw-unique u)
        tm-raw-unique (Raw.fst t) = fst-eq (tm-raw-unique t)
        tm-raw-unique (Raw.snd t) = snd-eq (tm-raw-unique t)
        tm-raw-unique (Raw.lam t) = lam-eq (tm-raw-unique t)
        tm-raw-unique (Raw.app t u) = app-eq (tm-raw-unique t) (tm-raw-unique u)
        tm-raw-unique (Raw.Tm-id t i) =
          tm-path (cong ηTmᴾ (Raw.Tm-id t))
            ([]-eq (tm-raw-unique t) (sym F.idᶠ))
            (tm-raw-unique t) i
        tm-raw-unique (Raw.Tm-∘ t τ σ i) =
          tm-path (cong ηTmᴾ (Raw.Tm-∘ t τ σ))
            ([]-eq ([]-eq (tm-raw-unique t) (sub-raw-unique τ)) (sub-raw-unique σ))
            ([]-eq (tm-raw-unique t) (∘-eq (sub-raw-unique τ) (sub-raw-unique σ))) i
        tm-raw-unique (Raw.q-⟨⟩ σ t i) =
          tm-path (cong ηTmᴾ (Raw.q-⟨⟩ σ t))
            ([]-eq (sym F.qᶠ) (⟨⟩-eq (sub-raw-unique σ) (tm-raw-unique t)))
            (tm-raw-unique t) i
        tm-raw-unique (Raw.true[] σ i) =
          tm-path (cong ηTmᴾ (Raw.true[] σ))
            ([]-eq (sym F.trueᶠ) (sub-raw-unique σ))
            (sym F.trueᶠ) i
        tm-raw-unique (Raw.false[] σ i) =
          tm-path (cong ηTmᴾ (Raw.false[] σ))
            ([]-eq (sym F.falseᶠ) (sub-raw-unique σ))
            (sym F.falseᶠ) i
        tm-raw-unique (Raw.if[] b t u σ i) =
          tm-path (cong ηTmᴾ (Raw.if[] b t u σ))
            ([]-eq (if-eq (tm-raw-unique b) (tm-raw-unique t) (tm-raw-unique u)) (sub-raw-unique σ))
            (if-eq
              ([]-eq (tm-raw-unique b) (sub-raw-unique σ))
              ([]-eq (tm-raw-unique t) (sub-raw-unique σ)) ([]-eq (tm-raw-unique u) (sub-raw-unique σ))) i
        tm-raw-unique (Raw.pair[] t u σ i) =
          tm-path (cong ηTmᴾ (Raw.pair[] t u σ))
            ([]-eq (pair-eq (tm-raw-unique t) (tm-raw-unique u)) (sub-raw-unique σ))
            (pair-eq ([]-eq (tm-raw-unique t) (sub-raw-unique σ)) ([]-eq (tm-raw-unique u) (sub-raw-unique σ))) i
        tm-raw-unique (Raw.fst[] t σ i) =
          tm-path (cong ηTmᴾ (Raw.fst[] t σ))
            ([]-eq (fst-eq (tm-raw-unique t)) (sub-raw-unique σ))
            (fst-eq ([]-eq (tm-raw-unique t) (sub-raw-unique σ))) i
        tm-raw-unique (Raw.snd[] t σ i) =
          tm-path (cong ηTmᴾ (Raw.snd[] t σ))
            ([]-eq (snd-eq (tm-raw-unique t)) (sub-raw-unique σ))
            (snd-eq ([]-eq (tm-raw-unique t) (sub-raw-unique σ))) i
        tm-raw-unique (Raw.lam[] t σ i) =
          tm-path (cong ηTmᴾ (Raw.lam[] t σ))
            ([]-eq (lam-eq (tm-raw-unique t)) (sub-raw-unique σ))
            (lam-eq ([]-eq (tm-raw-unique t) (⟨⟩-eq (∘-eq (sub-raw-unique σ) (sym F.pᶠ)) (sym F.qᶠ)))) i
        tm-raw-unique (Raw.app[] t u σ i) =
          tm-path (cong ηTmᴾ (Raw.app[] t u σ))
            ([]-eq (app-eq (tm-raw-unique t) (tm-raw-unique u)) (sub-raw-unique σ))
            (app-eq ([]-eq (tm-raw-unique t) (sub-raw-unique σ)) ([]-eq (tm-raw-unique u) (sub-raw-unique σ))) i
        tm-raw-unique (Raw.βif-true-rel t u i) =
          fst (tm-hom (hom-map ηTmᴾ (Raw.βif-true t u))
            (if-eq (sym F.trueᶠ) (tm-raw-unique t) (tm-raw-unique u))
            (tm-raw-unique t)) i
        tm-raw-unique (Raw.βif-true-left t u i) =
          fst (snd (tm-hom (hom-map ηTmᴾ (Raw.βif-true t u))
            (if-eq (sym F.trueᶠ) (tm-raw-unique t) (tm-raw-unique u))
            (tm-raw-unique t))) i
        tm-raw-unique (Raw.βif-true-right t u i) =
          snd (snd (tm-hom (hom-map ηTmᴾ (Raw.βif-true t u))
            (if-eq (sym F.trueᶠ) (tm-raw-unique t) (tm-raw-unique u))
            (tm-raw-unique t))) i
        tm-raw-unique (Raw.βif-false-rel t u i) =
          fst (tm-hom (hom-map ηTmᴾ (Raw.βif-false t u))
            (if-eq (sym F.falseᶠ) (tm-raw-unique t) (tm-raw-unique u))
            (tm-raw-unique u)) i
        tm-raw-unique (Raw.βif-false-left t u i) =
          fst (snd (tm-hom (hom-map ηTmᴾ (Raw.βif-false t u))
            (if-eq (sym F.falseᶠ) (tm-raw-unique t) (tm-raw-unique u))
            (tm-raw-unique u))) i
        tm-raw-unique (Raw.βif-false-right t u i) =
          snd (snd (tm-hom (hom-map ηTmᴾ (Raw.βif-false t u))
            (if-eq (sym F.falseᶠ) (tm-raw-unique t) (tm-raw-unique u))
            (tm-raw-unique u))) i
        tm-raw-unique (Raw.β×₁-rel t u i) =
          fst (tm-hom (hom-map ηTmᴾ (Raw.β×₁ t u))
            (fst-eq (pair-eq (tm-raw-unique t) (tm-raw-unique u)))
            (tm-raw-unique t)) i
        tm-raw-unique (Raw.β×₁-left t u i) =
          fst (snd (tm-hom (hom-map ηTmᴾ (Raw.β×₁ t u))
            (fst-eq (pair-eq (tm-raw-unique t) (tm-raw-unique u)))
            (tm-raw-unique t))) i
        tm-raw-unique (Raw.β×₁-right t u i) =
          snd (snd (tm-hom (hom-map ηTmᴾ (Raw.β×₁ t u))
            (fst-eq (pair-eq (tm-raw-unique t) (tm-raw-unique u)))
            (tm-raw-unique t))) i
        tm-raw-unique (Raw.β×₂-rel t u i) =
          fst (tm-hom (hom-map ηTmᴾ (Raw.β×₂ t u))
            (snd-eq (pair-eq (tm-raw-unique t) (tm-raw-unique u)))
            (tm-raw-unique u)) i
        tm-raw-unique (Raw.β×₂-left t u i) =
          fst (snd (tm-hom (hom-map ηTmᴾ (Raw.β×₂ t u))
            (snd-eq (pair-eq (tm-raw-unique t) (tm-raw-unique u)))
            (tm-raw-unique u))) i
        tm-raw-unique (Raw.β×₂-right t u i) =
          snd (snd (tm-hom (hom-map ηTmᴾ (Raw.β×₂ t u))
            (snd-eq (pair-eq (tm-raw-unique t) (tm-raw-unique u)))
            (tm-raw-unique u))) i
        tm-raw-unique (Raw.η×-rel t i) =
          fst (tm-hom (hom-map ηTmᴾ (Raw.η× t))
            (pair-eq (fst-eq (tm-raw-unique t)) (snd-eq (tm-raw-unique t)))
            (tm-raw-unique t)) i
        tm-raw-unique (Raw.η×-left t i) =
          fst (snd (tm-hom (hom-map ηTmᴾ (Raw.η× t))
            (pair-eq (fst-eq (tm-raw-unique t)) (snd-eq (tm-raw-unique t)))
            (tm-raw-unique t))) i
        tm-raw-unique (Raw.η×-right t i) =
          snd (snd (tm-hom (hom-map ηTmᴾ (Raw.η× t))
            (pair-eq (fst-eq (tm-raw-unique t)) (snd-eq (tm-raw-unique t)))
            (tm-raw-unique t))) i
        tm-raw-unique (Raw.β⇒-rel t u i) =
          fst (tm-hom (hom-map ηTmᴾ (Raw.β⇒ t u))
            (app-eq (lam-eq (tm-raw-unique t)) (tm-raw-unique u))
            ([]-eq (tm-raw-unique t) (⟨⟩-eq (sym F.idᶠ) (tm-raw-unique u)))) i
        tm-raw-unique (Raw.β⇒-left t u i) =
          fst (snd (tm-hom (hom-map ηTmᴾ (Raw.β⇒ t u))
            (app-eq (lam-eq (tm-raw-unique t)) (tm-raw-unique u))
            ([]-eq (tm-raw-unique t) (⟨⟩-eq (sym F.idᶠ) (tm-raw-unique u))))) i
        tm-raw-unique (Raw.β⇒-right t u i) =
          snd (snd (tm-hom (hom-map ηTmᴾ (Raw.β⇒ t u))
            (app-eq (lam-eq (tm-raw-unique t)) (tm-raw-unique u))
            ([]-eq (tm-raw-unique t) (⟨⟩-eq (sym F.idᶠ) (tm-raw-unique u))))) i
        tm-raw-unique (Raw.η⇒-rel t i) =
          fst (tm-hom (hom-map ηTmᴾ (Raw.η⇒ t))
            (lam-eq (app-eq ([]-eq (tm-raw-unique t) (sym F.pᶠ)) (sym F.qᶠ)))
            (tm-raw-unique t)) i
        tm-raw-unique (Raw.η⇒-left t i) =
          fst (snd (tm-hom (hom-map ηTmᴾ (Raw.η⇒ t))
            (lam-eq (app-eq ([]-eq (tm-raw-unique t) (sym F.pᶠ)) (sym F.qᶠ)))
            (tm-raw-unique t))) i
        tm-raw-unique (Raw.η⇒-right t i) =
          snd (snd (tm-hom (hom-map ηTmᴾ (Raw.η⇒ t))
            (lam-eq (app-eq ([]-eq (tm-raw-unique t) (sym F.pᶠ)) (sym F.qᶠ)))
            (tm-raw-unique t))) i

      sub-unique : {Γ Δ : Raw.Ctx} (σ : Subᴾ Γ Δ) → Subᶠ σ ≡ F.Subᶠ σ
      sub-unique = recᴾ-unique (M.sub-local _ _) Subᶠ F.Subᶠ sub-raw-unique

      tm-unique : {Γ : Raw.Ctx} {A : Raw.Ty} (t : Tmᴾ Γ A) → Tmᶠ t ≡ F.Tmᶠ t
      tm-unique = recᴾ-unique (M.tm-local _ _) Tmᶠ F.Tmᶠ tm-raw-unique

    morphisms-over-isContr : isContr (MorphismOver SyntaxModel 𝓜 sorts)
    morphisms-over-isContr = recursor , λ f →
      morphismOver-path M.sub-set M.tm-set
        (Uniqueness.sub-unique f) (Uniqueness.tm-unique f)

  syntax-isInitial′ : isContr (SimpleMorphism SyntaxModel 𝓜)
  syntax-isInitial′ = morphisms-isContr sorts-isContr morphisms-over-isContr

syntax-isInitial : (ℓS ℓM : Level) → isInitialDirected SyntaxModel ℓS ℓM
syntax-isInitial ℓS ℓM = syntax-isInitial′
