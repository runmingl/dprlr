module DPRLR.Object.Syntax.Initiality.Raw where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import DPRLR.Simplicial.Hom
open import DPRLR.Object.Model.Model using (SimpleDirectedCwF)
open import DPRLR.Object.Model.Morphism.Base
open import DPRLR.Object.Model.Morphism.Properties
open import DPRLR.Object.Model.DisplayedModel
open import DPRLR.Object.Syntax.Raw.Model
open import DPRLR.Object.Syntax.Raw.Displayed
import DPRLR.Object.Syntax.Raw.Base as R

module _ {ℓS ℓM : Level} (𝓜 : SimpleDirectedCwF ℓS ℓM) where
  private
    module M = SimpleDirectedCwF 𝓜

    recursion = syntax-elim-displayed (constantDisplayed M.cwf)
    open DisplayedSection recursion renaming
      (Ctxˢ to Ctxʳ ; Tyˢ to Tyʳ ; Subˢ to Subʳ ; Tmˢ to Tmʳ)

    raw-sorts : SortMorphism RawSyntaxCwF M.cwf
    raw-sorts = record
      { Tyᶠ = Tyʳ ; Ctxᶠ = Ctxʳ ; Boolᶠ = refl
      ; ×ᶠ = λ _ _ → refl ; ⇒ᶠ = λ _ _ → refl
      ; εᶠ = refl ; ▷ᶠ = λ _ _ → refl }

    raw-sorts-isContr : isContr (SortMorphism RawSyntaxCwF M.cwf)
    raw-sorts-isContr = raw-sorts , contract
      where
      contract : (s : SortMorphism RawSyntaxCwF M.cwf) → raw-sorts ≡ s
      contract s = path
        where
        open SortMorphism s

        ty : (A : R.Ty) → Tyʳ A ≡ Tyᶠ A
        ty R.Bool = sym Boolᶠ
        ty (A R.×ᵗʸ B) = cong₂ M._×ᵗʸ_ (ty A) (ty B) ∙ sym (×ᶠ A B)
        ty (A R.⇒ᵗʸ B) = cong₂ M._⇒ᵗʸ_ (ty A) (ty B) ∙ sym (⇒ᶠ A B)

        ctx : (Γ : R.Ctx) → Ctxʳ Γ ≡ Ctxᶠ Γ
        ctx R.ε = sym εᶠ
        ctx (Γ R.▷ A) = cong₂ M._▷_ (ctx Γ) (ty A) ∙ sym (▷ᶠ Γ A)

        path : raw-sorts ≡ s
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

    module Uniqueness (f : MorphismOver RawSyntaxCwF M.cwf raw-sorts) where
      private
        module F = MorphismOver f
      open F using (Subᶠ ; Tmᶠ)

      SubEq : {Γ Δ : R.Ctx} → R.Sub Γ Δ → Type ℓM
      SubEq σ = Subʳ σ ≡ Subᶠ σ

      TmEq : {Γ : R.Ctx} {A : R.Ty} → R.Tm Γ A → Type ℓM
      TmEq t = Tmʳ t ≡ Tmᶠ t

      sub-path : {Γ Δ : R.Ctx} {σ τ : R.Sub Γ Δ} (p : σ ≡ τ)
        {u : SubEq σ} {v : SubEq τ} → PathP (λ i → SubEq (p i)) u v
      sub-path p = isProp→PathP (λ i → M.sub-set _ _ _ _) _ _

      tm-path : {Γ : R.Ctx} {A : R.Ty} {t u : R.Tm Γ A} (p : t ≡ u)
        {v : TmEq t} {w : TmEq u} → PathP (λ i → TmEq (p i)) v w
      tm-path p = isProp→PathP (λ i → M.tm-set _ _ _ _) _ _

      tm-hom : {Γ : R.Ctx} {A : R.Ty} {t u : R.Tm Γ A} (h : t ≤ u)
        {v : TmEq t} {w : TmEq u} → TmEq ⊢ v ≤[ h ] w
      tm-hom h = HomP-thin-≡ {f = Tmʳ} {g = Tmᶠ} (M.tm-thin _ _) h _ _

      equality-displayed : DisplayedSimpleCwF ℓ-zero ℓM RawSyntaxCwF
      DisplayedSimpleCwF.Ctx∙ equality-displayed _ = Unit
      DisplayedSimpleCwF.Ty∙ equality-displayed _ = Unit
      DisplayedSimpleCwF.Sub∙ equality-displayed _ _ = SubEq
      DisplayedSimpleCwF.Tm∙ equality-displayed _ _ = TmEq
      DisplayedSimpleCwF.ε∙ equality-displayed = tt
      DisplayedSimpleCwF._▷∙_ equality-displayed _ _ = tt
      DisplayedSimpleCwF.Bool∙ equality-displayed = tt
      DisplayedSimpleCwF._×ᵗʸ∙_ equality-displayed _ _ = tt
      DisplayedSimpleCwF._⇒ᵗʸ∙_ equality-displayed _ _ = tt
      DisplayedSimpleCwF.id∙ equality-displayed = sym F.idᶠ
      DisplayedSimpleCwF._∘∙_ equality-displayed {σ = σ} {τ = τ} p q =
        cong₂ M._∘_ p q ∙ sym (F.∘ᶠ τ σ)
      DisplayedSimpleCwF.ε-sub∙ equality-displayed = sym F.ε-subᶠ
      DisplayedSimpleCwF.p∙ equality-displayed = sym F.pᶠ
      DisplayedSimpleCwF.q∙ equality-displayed = sym F.qᶠ
      DisplayedSimpleCwF.⟨_,_⟩∙ equality-displayed {σ = σ} {M = t} p q =
        cong₂ M.⟨_,_⟩ p q ∙ sym (F.⟨⟩ᶠ σ t)
      DisplayedSimpleCwF._[_]Tm∙ equality-displayed {M = t} {σ = σ} p q =
        cong₂ M._[_]Tm p q ∙ sym (F.[]ᶠ t σ)
      DisplayedSimpleCwF.true∙ equality-displayed = sym F.trueᶠ
      DisplayedSimpleCwF.false∙ equality-displayed = sym F.falseᶠ
      DisplayedSimpleCwF.if∙ equality-displayed {B = b} {T = t} {F = u} p q r =
        (λ i → M.if p i then q i else r i)
        ∙ cong (λ x → M.if x then Tmᶠ t else Tmᶠ u) (sym (transportRefl (Tmᶠ b)))
        ∙ sym (F.ifᶠ b t u)
      DisplayedSimpleCwF.pair∙ equality-displayed {M = t} {N = u} p q =
        cong₂ M.pair p q ∙ sym (F.pairᶠ t u)
      DisplayedSimpleCwF.fst∙ equality-displayed {P = t} p =
        cong M.fst (p ∙ sym (transportRefl (Tmᶠ t))) ∙ sym (F.fstᶠ t)
      DisplayedSimpleCwF.snd∙ equality-displayed {P = t} p =
        cong M.snd (p ∙ sym (transportRefl (Tmᶠ t))) ∙ sym (F.sndᶠ t)
      DisplayedSimpleCwF.lam∙ equality-displayed {N = t} p =
        cong M.lam (p ∙ sym (transportRefl (Tmᶠ t))) ∙ sym (F.lamᶠ t)
      DisplayedSimpleCwF.app∙ equality-displayed {F = t} {M = u} p q =
        cong₂ M.app (p ∙ sym (transportRefl (Tmᶠ t))) q ∙ sym (F.appᶠ t u)

      DisplayedSimpleCwF.id-left∙ equality-displayed {σ = σ} _ = sub-path (R.id-left σ)
      DisplayedSimpleCwF.id-right∙ equality-displayed {σ = σ} _ = sub-path (R.id-right σ)
      DisplayedSimpleCwF.∘-assoc∙ equality-displayed {σ = σ} {τ = τ} {ρ = ρ} _ _ _ = sub-path (R.∘-assoc ρ τ σ)
      DisplayedSimpleCwF.εη∙ equality-displayed {σ = σ} _ = sub-path (R.εη σ)
      DisplayedSimpleCwF.p-⟨⟩∙ equality-displayed {σ = σ} {M = t} _ _ = sub-path (R.p-⟨⟩ σ t)
      DisplayedSimpleCwF.▷η∙ equality-displayed = sub-path R.▷η
      DisplayedSimpleCwF.⟨⟩-∘∙ equality-displayed {σ = σ} {M = t} {ρ = ρ} _ _ _ = sub-path (R.⟨⟩-∘ σ t ρ)
      DisplayedSimpleCwF.Tm-id∙ equality-displayed {M = t} _ = tm-path (R.Tm-id t)
      DisplayedSimpleCwF.Tm-∘∙ equality-displayed {M = t} {τ = τ} {σ = σ} _ _ _ = tm-path (R.Tm-∘ t τ σ)
      DisplayedSimpleCwF.q-⟨⟩∙ equality-displayed {σ = σ} {M = t} _ _ = tm-path (R.q-⟨⟩ σ t)
      DisplayedSimpleCwF.true[]∙ equality-displayed {σ = σ} _ = tm-path (R.true[] σ)
      DisplayedSimpleCwF.false[]∙ equality-displayed {σ = σ} _ = tm-path (R.false[] σ)
      DisplayedSimpleCwF.if[]∙ equality-displayed {B = b} {T = t} {F = u} {σ = σ} _ _ _ _ = tm-path (R.if[] b t u σ)
      DisplayedSimpleCwF.pair[]∙ equality-displayed {M = t} {N = u} {σ = σ} _ _ _ = tm-path (R.pair[] t u σ)
      DisplayedSimpleCwF.fst[]∙ equality-displayed {P = t} {σ = σ} _ _ = tm-path (R.fst[] t σ)
      DisplayedSimpleCwF.snd[]∙ equality-displayed {P = t} {σ = σ} _ _ = tm-path (R.snd[] t σ)
      DisplayedSimpleCwF.lam[]∙ equality-displayed {N = t} {σ = σ} _ _ = tm-path (R.lam[] t σ)
      DisplayedSimpleCwF.app[]∙ equality-displayed {F = t} {M = u} {σ = σ} _ _ _ = tm-path (R.app[] t u σ)
      DisplayedSimpleCwF.βif-true∙ equality-displayed {T = t} {F = u} _ _ = tm-hom (R.βif-true t u)
      DisplayedSimpleCwF.βif-false∙ equality-displayed {T = t} {F = u} _ _ = tm-hom (R.βif-false t u)
      DisplayedSimpleCwF.β×₁∙ equality-displayed {M = t} {N = u} _ _ = tm-hom (R.β×₁ t u)
      DisplayedSimpleCwF.β×₂∙ equality-displayed {M = t} {N = u} _ _ = tm-hom (R.β×₂ t u)
      DisplayedSimpleCwF.η×∙ equality-displayed {P = t} _ = tm-hom (R.η× t)
      DisplayedSimpleCwF.β⇒∙ equality-displayed {N = t} {M = u} _ _ = tm-hom (R.β⇒ t u)
      DisplayedSimpleCwF.η⇒∙ equality-displayed {F = t} _ = tm-hom (R.η⇒ t)

      sub-unique : {Γ Δ : R.Ctx} (σ : R.Sub Γ Δ) → Subʳ σ ≡ Subᶠ σ
      sub-unique = DisplayedSection.Subˢ (syntax-elim-displayed equality-displayed)

      tm-unique : {Γ : R.Ctx} {A : R.Ty} (t : R.Tm Γ A) → Tmʳ t ≡ Tmᶠ t
      tm-unique = DisplayedSection.Tmˢ (syntax-elim-displayed equality-displayed)

    recursor : MorphismOver RawSyntaxCwF M.cwf raw-sorts
    recursor = record
      { Subᶠ = Subʳ ; Tmᶠ = Tmʳ
      ; idᶠ = refl ; ∘ᶠ = λ _ _ → refl
      ; ε-subᶠ = refl ; pᶠ = refl ; qᶠ = refl
      ; ⟨⟩ᶠ = λ _ _ → refl ; []ᶠ = λ _ _ → refl
      ; trueᶠ = refl ; falseᶠ = refl
      ; ifᶠ = λ b t u → cong (λ x → M.if x then Tmʳ t else Tmʳ u) (sym (transportRefl (Tmʳ b)))
      ; pairᶠ = λ _ _ → refl
      ; fstᶠ = λ t → cong M.fst (sym (transportRefl (Tmʳ t)))
      ; sndᶠ = λ t → cong M.snd (sym (transportRefl (Tmʳ t)))
      ; lamᶠ = λ t → cong M.lam (sym (transportRefl (Tmʳ t)))
      ; appᶠ = λ t u → cong (λ x → M.app x (Tmʳ u)) (sym (transportRefl (Tmʳ t)))
      }

    raw-morphisms-isContr : isContr (MorphismOver RawSyntaxCwF M.cwf raw-sorts)
    raw-morphisms-isContr = recursor , λ f →
      morphismOver-path M.sub-set M.tm-set
        (Uniqueness.sub-unique f) (Uniqueness.tm-unique f)

  raw-syntax-isInitial : isContr (SimpleMorphism RawSyntaxCwF M.cwf)
  raw-syntax-isInitial = morphisms-isContr raw-sorts-isContr raw-morphisms-isContr
