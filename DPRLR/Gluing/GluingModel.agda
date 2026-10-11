open import Cubical.Foundations.Prelude using (Level ; ℓ-suc ; ℓ-max ; _,_ ; cong)

open import DPRLR.Object.Model.Model
open import DPRLR.Object.Model.Morphism.Base using (SimpleMorphism)

module DPRLR.Gluing.GluingModel {ℓS ℓM : Level} (𝓜 : SimpleCwF ℓS ℓM) where
  open import DPRLR.Gluing.LogicalRelations.Judgment 𝓜 public
    using (GluCtx ; GluSub ; GluSub-isPreorder ; GluTy ; GluTm ; GluTm-isPreorder)

  open import DPRLR.Gluing.LogicalRelations.Substitution 𝓜 public
    using
      ( εᵍ
      ; ε-subᵍ ; εηᵍ
      ; idᵍ ; _∘ᵍ_ ; id-leftᵍ ; id-rightᵍ ; ∘-assocᵍ
      ; _[_]Tmᵍ ; Tm-idᵍ ; Tm-∘ᵍ
      ; _▷ᵍ_ ; pᵍ ; qᵍ ; ⟨_,_⟩ᵍ ; p-⟨⟩ᵍ ; q-⟨⟩ᵍ
      ; ▷ηᵍ ; ⟨⟩-∘ᵍ
      )

  open import DPRLR.Gluing.LogicalRelations.Product 𝓜 public
    using
      ( PROD ; PAIR ; FST ; SND
      ; PAIR[] ; FST[] ; SND[]
      ; PROD-preserves-β₁ ; PROD-preserves-β₂ ; PROD-preserves-η
      )

  open import DPRLR.Gluing.LogicalRelations.Function 𝓜 public
    using
      ( FUN ; APP ; LAM
      ; APP[] ; LAM[]
      ; FUN-preserves-β ; FUN-preserves-η
      )

  open import DPRLR.Gluing.LogicalRelations.Bool 𝓜 public
    using
      ( BOOL ; TRUE ; FALSE ; TRUE[] ; FALSE[]
      ; IF ; IF[] ; IF-preserves-β-true ; IF-preserves-β-false
      )

  GluingCwF : SimpleCwF (ℓ-max ℓS (ℓ-suc ℓM)) ℓM
  SimpleCwF.Ctx GluingCwF = GluCtx
  SimpleCwF.Ty GluingCwF = GluTy
  SimpleCwF.Sub GluingCwF Γ Δ = GluSub Γ Δ , GluSub-isPreorder Γ Δ
  SimpleCwF.Tm GluingCwF Γ A = GluTm Γ A , GluTm-isPreorder Γ A
  SimpleCwF.id GluingCwF {Γ = Γ} = idᵍ Γ
  SimpleCwF._∘_ GluingCwF = _∘ᵍ_
  SimpleCwF.id-left GluingCwF = id-leftᵍ
  SimpleCwF.id-right GluingCwF = id-rightᵍ
  SimpleCwF.∘-assoc GluingCwF = ∘-assocᵍ
  SimpleCwF._[_]Tm GluingCwF = _[_]Tmᵍ
  SimpleCwF.Tm-id GluingCwF = Tm-idᵍ
  SimpleCwF.Tm-∘ GluingCwF = Tm-∘ᵍ
  SimpleCwF.ε GluingCwF = εᵍ
  SimpleCwF.ε-sub GluingCwF = ε-subᵍ
  SimpleCwF.εη GluingCwF = εηᵍ
  SimpleCwF._▷_ GluingCwF = _▷ᵍ_
  SimpleCwF.p GluingCwF {A = A} = pᵍ {A = A}
  SimpleCwF.q GluingCwF {Γ = Γ} {A = A} = qᵍ {Γ = Γ} {A = A}
  SimpleCwF.⟨_,_⟩ GluingCwF = ⟨_,_⟩ᵍ
  SimpleCwF.p-⟨⟩ GluingCwF = p-⟨⟩ᵍ
  SimpleCwF.q-⟨⟩ GluingCwF = q-⟨⟩ᵍ
  SimpleCwF.▷η GluingCwF {Γ = Γ} {A = A} = ▷ηᵍ {Γ = Γ} {A = A}
  SimpleCwF.⟨⟩-∘ GluingCwF = ⟨⟩-∘ᵍ
  SimpleCwF.Bool GluingCwF = BOOL
  SimpleCwF.true GluingCwF = TRUE
  SimpleCwF.false GluingCwF = FALSE
  SimpleCwF.if_then_else_ GluingCwF = IF
  SimpleCwF.true[] GluingCwF = TRUE[]
  SimpleCwF.false[] GluingCwF = FALSE[]
  SimpleCwF.if[] GluingCwF = IF[]
  SimpleCwF.βif-true GluingCwF = IF-preserves-β-true
  SimpleCwF.βif-false GluingCwF = IF-preserves-β-false
  SimpleCwF._×ᵗʸ_ GluingCwF = PROD
  SimpleCwF.pair GluingCwF = PAIR
  SimpleCwF.fst GluingCwF {A = A} {B = B} = FST {A = A} {B = B}
  SimpleCwF.snd GluingCwF {A = A} {B = B} = SND {A = A} {B = B}
  SimpleCwF.pair[] GluingCwF = PAIR[]
  SimpleCwF.fst[] GluingCwF {A = A} {B = B} = FST[] {A = A} {B = B}
  SimpleCwF.snd[] GluingCwF {A = A} {B = B} = SND[] {A = A} {B = B}
  SimpleCwF._⇒ᵗʸ_ GluingCwF = FUN
  SimpleCwF.lam GluingCwF {A = A} = LAM {A = A}
  SimpleCwF.app GluingCwF = APP
  SimpleCwF.lam[] GluingCwF {A = A} = LAM[] {A = A}
  SimpleCwF.app[] GluingCwF = APP[]
  SimpleCwF.β⇒ GluingCwF = FUN-preserves-β
  SimpleCwF.η⇒ GluingCwF {A = A} {B = B} = FUN-preserves-η {A = A} {B = B}
  SimpleCwF.β×₁ GluingCwF = PROD-preserves-β₁
  SimpleCwF.β×₂ GluingCwF = PROD-preserves-β₂
  SimpleCwF.η× GluingCwF {A = A} {B = B} = PROD-preserves-η {A = A} {B = B}

  projectGluingMorphism : {ℓAS ℓA : Level} {𝓐 : SimpleCwF ℓAS ℓA}
    → SimpleMorphism 𝓐 GluingCwF → SimpleMorphism 𝓐 𝓜
  projectGluingMorphism f = record
    { sorts = record
      { Tyᶠ = λ A → GluTy.A° (F.Tyᶠ A) ; Ctxᶠ = λ Γ → GluCtx.Γ° (F.Ctxᶠ Γ)
      ; Boolᶠ = cong GluTy.A° F.Boolᶠ ; ×ᶠ = λ A B → cong GluTy.A° (F.×ᶠ A B)
      ; ⇒ᶠ = λ A B → cong GluTy.A° (F.⇒ᶠ A B)
      ; εᶠ = cong GluCtx.Γ° F.εᶠ ; ▷ᶠ = λ Γ A → cong GluCtx.Γ° (F.▷ᶠ Γ A) }
    ; over = record
      { Subᶠ = λ σ → GluSub.σ° (F.Subᶠ σ) ; Tmᶠ = λ t → GluTm.M° (F.Tmᶠ t)
      ; idᶠ = cong GluSub.σ° F.idᶠ ; ∘ᶠ = λ τ σ → cong GluSub.σ° (F.∘ᶠ τ σ)
      ; ε-subᶠ = λ i → GluSub.σ° (F.ε-subᶠ i)
      ; pᶠ = λ i → GluSub.σ° (F.pᶠ i) ; qᶠ = λ i → GluTm.M° (F.qᶠ i)
      ; ⟨⟩ᶠ = λ σ t i → GluSub.σ° (F.⟨⟩ᶠ σ t i)
      ; []ᶠ = λ t σ → cong GluTm.M° (F.[]ᶠ t σ)
      ; trueᶠ = λ i → GluTm.M° (F.trueᶠ i) ; falseᶠ = λ i → GluTm.M° (F.falseᶠ i)
      ; ifᶠ = λ b t u → cong GluTm.M° (F.ifᶠ b t u)
      ; pairᶠ = λ t u i → GluTm.M° (F.pairᶠ t u i)
      ; fstᶠ = λ t → cong GluTm.M° (F.fstᶠ t)
      ; sndᶠ = λ t → cong GluTm.M° (F.sndᶠ t)
      ; lamᶠ = λ t i → GluTm.M° (F.lamᶠ t i)
      ; appᶠ = λ t u → cong GluTm.M° (F.appᶠ t u)
      }
    }
    where module F = SimpleMorphism f
