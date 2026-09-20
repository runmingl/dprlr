module DPRLR.Gluing.GluingModel where

open import Cubical.Foundations.Prelude using (Level ; ℓ-suc ; ℓ-max)

open import DPRLR.Object.Model.Model public
  using (SimpleCwF ; SimpleDirectedCwF)

open import DPRLR.Gluing.LogicalRelations.Judgment public
  using
    ( GluCtx ; Γ° ; Γ∙
    ; GluSub ; σ° ; σ∙
    ; GluTy ; A° ; A∙ ; cA
    ; GluTm ; M° ; M∙
    )

open import DPRLR.Gluing.LogicalRelations.Substitution public
  using
    ( εᵍ
    ; ε-subᵍ ; εηᵍ
    ; idᵍ ; _∘ᵍ_ ; id-leftᵍ ; id-rightᵍ ; ∘-assocᵍ
    ; _[_]Tmᵍ ; Tm-idᵍ ; Tm-∘ᵍ
    ; _▷ᵍ_ ; pᵍ ; qᵍ ; ⟨_,_⟩ᵍ ; liftᵍ ; p-⟨⟩ᵍ ; q-⟨⟩ᵍ
    ; ▷ηᵍ ; ⟨⟩-∘ᵍ
    )

open import DPRLR.Gluing.LogicalRelations.Product public
  using
    ( PROD ; PAIR ; FST ; SND
    ; PAIR[] ; FST[] ; SND[]
    ; PROD-preserves-β₁ ; PROD-preserves-β₂ ; PROD-preserves-η
    )

open import DPRLR.Gluing.LogicalRelations.Function public
  using
    ( FUN ; APP ; LAM
    ; APP[] ; LAM[]
    ; FUN-preserves-β ; FUN-preserves-η
    )

open import DPRLR.Gluing.LogicalRelations.Bool public
  using
    ( BOOL ; TRUE ; FALSE ; TRUE[] ; FALSE[]
    ; IF ; IF[] ; IF-preserves-β-true ; IF-preserves-β-false
    )

module _ {ℓS ℓM : Level} (𝓜 : SimpleDirectedCwF ℓS ℓM) where

  GluingCwF : SimpleCwF (ℓ-max ℓS (ℓ-suc ℓM)) ℓM
  SimpleCwF.Ctx GluingCwF = GluCtx 𝓜
  SimpleCwF.Ty GluingCwF = GluTy 𝓜
  SimpleCwF.Sub GluingCwF = GluSub 𝓜
  SimpleCwF.Tm GluingCwF = GluTm 𝓜
  SimpleCwF.id GluingCwF {Γ = Γ} = idᵍ 𝓜 Γ
  SimpleCwF._∘_ GluingCwF = _∘ᵍ_ 𝓜
  SimpleCwF.id-left GluingCwF = id-leftᵍ 𝓜
  SimpleCwF.id-right GluingCwF = id-rightᵍ 𝓜
  SimpleCwF.∘-assoc GluingCwF = ∘-assocᵍ 𝓜
  SimpleCwF._[_]Tm GluingCwF = _[_]Tmᵍ 𝓜
  SimpleCwF.Tm-id GluingCwF = Tm-idᵍ 𝓜
  SimpleCwF.Tm-∘ GluingCwF = Tm-∘ᵍ 𝓜
  SimpleCwF.ε GluingCwF = εᵍ 𝓜
  SimpleCwF.ε-sub GluingCwF = ε-subᵍ 𝓜
  SimpleCwF.εη GluingCwF = εηᵍ 𝓜
  SimpleCwF._▷_ GluingCwF = _▷ᵍ_ 𝓜
  SimpleCwF.p GluingCwF {Γ = Γ} {A = A} =
    pᵍ 𝓜 {Γ = Γ} {A = A}
  SimpleCwF.q GluingCwF {Γ = Γ} {A = A} =
    qᵍ 𝓜 {Γ = Γ} {A = A}
  SimpleCwF.⟨_,_⟩ GluingCwF = ⟨_,_⟩ᵍ 𝓜
  SimpleCwF.p-⟨⟩ GluingCwF {Γ = Γ} {Δ = Δ} {A = A} σ M =
    p-⟨⟩ᵍ 𝓜 {Γ = Γ} {Δ = Δ} {A = A} σ M
  SimpleCwF.q-⟨⟩ GluingCwF {Γ = Γ} {Δ = Δ} {A = A} σ M =
    q-⟨⟩ᵍ 𝓜 {Γ = Γ} {Δ = Δ} {A = A} σ M
  SimpleCwF.▷η GluingCwF {Γ = Γ} {A = A} =
    ▷ηᵍ 𝓜 {Γ = Γ} {A = A}
  SimpleCwF.⟨⟩-∘ GluingCwF = ⟨⟩-∘ᵍ 𝓜
  SimpleCwF.Bool GluingCwF = BOOL 𝓜
  SimpleCwF.true GluingCwF = TRUE 𝓜
  SimpleCwF.false GluingCwF = FALSE 𝓜
  SimpleCwF.if_then_else_ GluingCwF = IF 𝓜
  SimpleCwF.true[] GluingCwF = TRUE[] 𝓜
  SimpleCwF.false[] GluingCwF = FALSE[] 𝓜
  SimpleCwF.if[] GluingCwF = IF[] 𝓜
  SimpleCwF.βif-true GluingCwF = IF-preserves-β-true 𝓜
  SimpleCwF.βif-false GluingCwF = IF-preserves-β-false 𝓜
  SimpleCwF._×ᵗʸ_ GluingCwF = PROD 𝓜
  SimpleCwF.pair GluingCwF = PAIR 𝓜
  SimpleCwF.fst GluingCwF {Γ = Γ} {A = A} {B = B} P =
    FST 𝓜 {Γ = Γ} {A = A} {B = B} P
  SimpleCwF.snd GluingCwF {Γ = Γ} {A = A} {B = B} P =
    SND 𝓜 {Γ = Γ} {A = A} {B = B} P
  SimpleCwF.pair[] GluingCwF = PAIR[] 𝓜
  SimpleCwF.fst[] GluingCwF {Γ = Γ} {Δ = Δ} {A = A} {B = B} P σ =
    FST[] 𝓜 {Γ = Γ} {Δ = Δ} {A = A} {B = B} P σ
  SimpleCwF.snd[] GluingCwF {Γ = Γ} {Δ = Δ} {A = A} {B = B} P σ =
    SND[] 𝓜 {Γ = Γ} {Δ = Δ} {A = A} {B = B} P σ
  SimpleCwF._⇒ᵗʸ_ GluingCwF = FUN 𝓜
  SimpleCwF.lam GluingCwF {Γ = Γ} {A = A} {B = B} N =
    LAM 𝓜 {Γ = Γ} {A = A} {B = B} N
  SimpleCwF.app GluingCwF = APP 𝓜
  SimpleCwF.lam[] GluingCwF {Γ = Γ} {Δ = Δ} {A = A} {B = B} N σ =
    LAM[] 𝓜 {Γ = Γ} {Δ = Δ} {A = A} {B = B} N σ
  SimpleCwF.app[] GluingCwF = APP[] 𝓜
  SimpleCwF.β⇒ GluingCwF = FUN-preserves-β 𝓜
  SimpleCwF.η⇒ GluingCwF {Γ = Γ} {A = A} {B = B} F =
    FUN-preserves-η 𝓜 {Γ = Γ} {A = A} {B = B} F
  SimpleCwF.β×₁ GluingCwF {Γ = Γ} {A = A} {B = B} M N =
    PROD-preserves-β₁ 𝓜 {Γ = Γ} {A = A} {B = B} M N
  SimpleCwF.β×₂ GluingCwF {Γ = Γ} {A = A} {B = B} M N =
    PROD-preserves-β₂ 𝓜 {Γ = Γ} {A = A} {B = B} M N
  SimpleCwF.η× GluingCwF {Γ = Γ} {A = A} {B = B} P =
    PROD-preserves-η 𝓜 {Γ = Γ} {A = A} {B = B} P
