module DPRLR.Object.Model.Morphism.Properties where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import Cubical.Foundations.HLevels
  using (isOfHLevelPathP' ; isContrΣ' ; isOfHLevelRetract)
open import Cubical.Data.Sigma using (fst ; _,_)

open import DPRLR.Object.Model.Model using (SimpleCwF)
open import DPRLR.Object.Model.Morphism.Base using
  (SortMorphism ; MorphismOver ; SimpleMorphism ; simple-morphism)

module _ {ℓCS ℓC ℓMS ℓM : Level}
  {𝓒 : SimpleCwF ℓCS ℓC} {𝓜 : SimpleCwF ℓMS ℓM} where
  private
    module C = SimpleCwF 𝓒
    module M = SimpleCwF 𝓜

  morphismOver-path : (sub-set : (Γ Δ : M.Ctx) → isSet (M.Sub Γ Δ))
    → (tm-set : (Γ : M.Ctx) (A : M.Ty) → isSet (M.Tm Γ A))
    → {s : SortMorphism 𝓒 𝓜} {f g : MorphismOver 𝓒 𝓜 s}
    → ({Γ Δ : C.Ctx} (σ : C.Sub Γ Δ) → MorphismOver.Subᶠ f σ ≡ MorphismOver.Subᶠ g σ)
    → ({Γ : C.Ctx} {A : C.Ty} (t : C.Tm Γ A) → MorphismOver.Tmᶠ f t ≡ MorphismOver.Tmᶠ g t)
    → f ≡ g
  morphismOver-path sub-set tm-set {s = s} {f = f} {g = g} sub-eq tm-eq i = record
    { Subᶠ = λ σ → sub-eq σ i
    ; Tmᶠ = λ t → tm-eq t i
    ; idᶠ = isProp→PathP (λ j → sub-set _ _ (sub-eq C.id j) _) F.idᶠ G.idᶠ i
    ; ∘ᶠ = λ τ σ → isProp→PathP
        (λ j → sub-set _ _ (sub-eq (τ C.∘ σ) j) (sub-eq τ j M.∘ sub-eq σ j))
        (F.∘ᶠ τ σ) (G.∘ᶠ τ σ) i
    ; ε-subᶠ = isProp→PathP
        (λ j → isOfHLevelPathP' 1 (sub-set _ _) (sub-eq C.ε-sub j) _) F.ε-subᶠ G.ε-subᶠ i
    ; pᶠ = isProp→PathP
        (λ j → isOfHLevelPathP' 1 (sub-set _ _) (sub-eq C.p j) _) F.pᶠ G.pᶠ i
    ; qᶠ = isProp→PathP
        (λ j → isOfHLevelPathP' 1 (tm-set _ _) (tm-eq C.q j) _) F.qᶠ G.qᶠ i
    ; ⟨⟩ᶠ = λ σ t → isProp→PathP
        (λ j → isOfHLevelPathP' 1 (sub-set _ _) (sub-eq C.⟨ σ , t ⟩ j)
          M.⟨ sub-eq σ j , tm-eq t j ⟩) (F.⟨⟩ᶠ σ t) (G.⟨⟩ᶠ σ t) i
    ; []ᶠ = λ t σ → isProp→PathP
        (λ j → tm-set _ _ (tm-eq (t C.[ σ ]Tm) j) (tm-eq t j M.[ sub-eq σ j ]Tm))
        (F.[]ᶠ t σ) (G.[]ᶠ t σ) i
    ; trueᶠ = isProp→PathP
        (λ j → isOfHLevelPathP' 1 (tm-set _ _) (tm-eq C.true j) _) F.trueᶠ G.trueᶠ i
    ; falseᶠ = isProp→PathP
        (λ j → isOfHLevelPathP' 1 (tm-set _ _) (tm-eq C.false j) _) F.falseᶠ G.falseᶠ i
    ; ifᶠ = λ b t u → isProp→PathP
        (λ j → tm-set _ _ (tm-eq (C.if b then t else u) j)
          (M.if subst (M.Tm _) S.Boolᶠ (tm-eq b j) then tm-eq t j else tm-eq u j))
        (F.ifᶠ b t u) (G.ifᶠ b t u) i
    ; pairᶠ = λ t u → isProp→PathP
        (λ j → isOfHLevelPathP' 1 (tm-set _ _) (tm-eq (C.pair t u) j)
          (M.pair (tm-eq t j) (tm-eq u j))) (F.pairᶠ t u) (G.pairᶠ t u) i
    ; fstᶠ = λ t → isProp→PathP
        (λ j → tm-set _ _ (tm-eq (C.fst t) j)
          (M.fst (subst (M.Tm _) (S.×ᶠ _ _) (tm-eq t j)))) (F.fstᶠ t) (G.fstᶠ t) i
    ; sndᶠ = λ t → isProp→PathP
        (λ j → tm-set _ _ (tm-eq (C.snd t) j)
          (M.snd (subst (M.Tm _) (S.×ᶠ _ _) (tm-eq t j)))) (F.sndᶠ t) (G.sndᶠ t) i
    ; lamᶠ = λ t → isProp→PathP
        (λ j → isOfHLevelPathP' 1 (tm-set _ _) (tm-eq (C.lam t) j)
          (M.lam (subst (λ Δ → M.Tm Δ _) (S.▷ᶠ _ _) (tm-eq t j)))) (F.lamᶠ t) (G.lamᶠ t) i
    ; appᶠ = λ t u → isProp→PathP
        (λ j → tm-set _ _ (tm-eq (C.app t u) j)
          (M.app (subst (M.Tm _) (S.⇒ᶠ _ _) (tm-eq t j)) (tm-eq u j))) (F.appᶠ t u) (G.appᶠ t u) i
    }
    where
    module S = SortMorphism s
    module F = MorphismOver f
    module G = MorphismOver g

  morphisms-isContr : (sorts : isContr (SortMorphism 𝓒 𝓜))
    → isContr (MorphismOver 𝓒 𝓜 (sorts .fst))
    → isContr (SimpleMorphism 𝓒 𝓜)
  morphisms-isContr sorts carriers =
    isOfHLevelRetract 0
      (λ f → SimpleMorphism.sorts f , SimpleMorphism.over f)
      (λ { (s , f) → simple-morphism s f })
      (λ _ → refl) (isContrΣ' sorts carriers)
