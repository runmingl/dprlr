module DPRLR.Object.Syntax.Localized.Model where

open import Cubical.Foundations.Prelude

open import DPRLR.Object.Model.Model using
  (SimpleCwF ; SimpleDirectedCwF)
open import DPRLR.Object.Syntax.Localized.Base
import DPRLR.Object.Syntax.Raw.Base as Raw

LocalizedSyntaxCwF : SimpleCwF ℓ-zero ℓ-zero
SimpleCwF.Ctx LocalizedSyntaxCwF = Raw.Ctx
SimpleCwF.Ty LocalizedSyntaxCwF = Raw.Ty
SimpleCwF.Sub LocalizedSyntaxCwF = Subᴾ
SimpleCwF.Tm LocalizedSyntaxCwF = Tmᴾ
SimpleCwF.id LocalizedSyntaxCwF = idᴾ
SimpleCwF._∘_ LocalizedSyntaxCwF = _∘ᴾ_
SimpleCwF.id-left LocalizedSyntaxCwF = id-leftᴾ
SimpleCwF.id-right LocalizedSyntaxCwF = id-rightᴾ
SimpleCwF.∘-assoc LocalizedSyntaxCwF = ∘-assocᴾ
SimpleCwF._[_]Tm LocalizedSyntaxCwF = _[_]Tmᴾ
SimpleCwF.Tm-id LocalizedSyntaxCwF = Tmᴾ-id
SimpleCwF.Tm-∘ LocalizedSyntaxCwF = Tmᴾ-∘
SimpleCwF.ε LocalizedSyntaxCwF = Raw.ε
SimpleCwF.ε-sub LocalizedSyntaxCwF = ε-subᴾ
SimpleCwF.εη LocalizedSyntaxCwF = εηᴾ
SimpleCwF._▷_ LocalizedSyntaxCwF = Raw._▷_
SimpleCwF.p LocalizedSyntaxCwF = pᴾ
SimpleCwF.q LocalizedSyntaxCwF = qᴾ
SimpleCwF.⟨_,_⟩ LocalizedSyntaxCwF = ⟨_,_⟩ᴾ
SimpleCwF.p-⟨⟩ LocalizedSyntaxCwF = p-⟨⟩ᴾ
SimpleCwF.q-⟨⟩ LocalizedSyntaxCwF = q-⟨⟩ᴾ
SimpleCwF.▷η LocalizedSyntaxCwF = ▷ηᴾ
SimpleCwF.⟨⟩-∘ LocalizedSyntaxCwF = ⟨⟩-∘ᴾ
SimpleCwF.Bool LocalizedSyntaxCwF = Raw.Bool
SimpleCwF.true LocalizedSyntaxCwF = trueᴾ
SimpleCwF.false LocalizedSyntaxCwF = falseᴾ
SimpleCwF.if_then_else_ LocalizedSyntaxCwF = ifᴾ
SimpleCwF.true[] LocalizedSyntaxCwF = true[]ᴾ
SimpleCwF.false[] LocalizedSyntaxCwF = false[]ᴾ
SimpleCwF.if[] LocalizedSyntaxCwF = if[]ᴾ
SimpleCwF.βif-true LocalizedSyntaxCwF = βif-trueᴾ
SimpleCwF.βif-false LocalizedSyntaxCwF = βif-falseᴾ
SimpleCwF._×ᵗʸ_ LocalizedSyntaxCwF = Raw._×ᵗʸ_
SimpleCwF.pair LocalizedSyntaxCwF = pairᴾ
SimpleCwF.fst LocalizedSyntaxCwF = fstᴾ
SimpleCwF.snd LocalizedSyntaxCwF = sndᴾ
SimpleCwF.pair[] LocalizedSyntaxCwF = pair[]ᴾ
SimpleCwF.fst[] LocalizedSyntaxCwF = fst[]ᴾ
SimpleCwF.snd[] LocalizedSyntaxCwF = snd[]ᴾ
SimpleCwF._⇒ᵗʸ_ LocalizedSyntaxCwF = Raw._⇒ᵗʸ_
SimpleCwF.lam LocalizedSyntaxCwF = lamᴾ
SimpleCwF.app LocalizedSyntaxCwF = appᴾ
SimpleCwF.lam[] LocalizedSyntaxCwF = lam[]ᴾ
SimpleCwF.app[] LocalizedSyntaxCwF = app[]ᴾ
SimpleCwF.β⇒ LocalizedSyntaxCwF = β⇒ᴾ
SimpleCwF.η⇒ LocalizedSyntaxCwF = η⇒ᴾ
SimpleCwF.β×₁ LocalizedSyntaxCwF = β×₁ᴾ
SimpleCwF.β×₂ LocalizedSyntaxCwF = β×₂ᴾ
SimpleCwF.η× LocalizedSyntaxCwF = η×ᴾ

LocalizedSyntaxModel : SimpleDirectedCwF ℓ-zero ℓ-zero
SimpleDirectedCwF.cwf LocalizedSyntaxModel = LocalizedSyntaxCwF
SimpleDirectedCwF.sub-set LocalizedSyntaxModel Γ Δ = Subᴾ-isSet
SimpleDirectedCwF.sub-thin LocalizedSyntaxModel Γ Δ = Subᴾ-isThin
SimpleDirectedCwF.sub-segal LocalizedSyntaxModel Γ Δ = Subᴾ-isSegal
SimpleDirectedCwF.tm-set LocalizedSyntaxModel Γ A = Tmᴾ-isSet
SimpleDirectedCwF.tm-thin LocalizedSyntaxModel Γ A = Tmᴾ-isThin
SimpleDirectedCwF.tm-segal LocalizedSyntaxModel Γ A = Tmᴾ-isSegal
