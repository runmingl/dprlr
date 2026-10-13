module DPRLR.Object.Syntax.Model where

open import Cubical.Foundations.Prelude

open import DPRLR.Object.Model.Model
open import DPRLR.Object.Syntax.Localized
import DPRLR.Object.Syntax.Raw as Raw

SyntaxModel : SimpleCwF ℓ-zero ℓ-zero
SyntaxModel .SimpleCwF.Ctx = Raw.Ctx
SyntaxModel .SimpleCwF.Ty = Raw.Ty
SyntaxModel .SimpleCwF.Sub Γ Δ = Subᴾ Γ Δ , Subᴾ-isPreorder
SyntaxModel .SimpleCwF.Tm Γ A = Tmᴾ Γ A , Tmᴾ-isPreorder
SyntaxModel .SimpleCwF.id = idᴾ
SyntaxModel .SimpleCwF._∘_ = _∘ᴾ_
SyntaxModel .SimpleCwF.id-left = id-leftᴾ
SyntaxModel .SimpleCwF.id-right = id-rightᴾ
SyntaxModel .SimpleCwF.∘-assoc = ∘-assocᴾ
SyntaxModel .SimpleCwF._[_]Tm = _[_]Tmᴾ
SyntaxModel .SimpleCwF.Tm-id = Tmᴾ-id
SyntaxModel .SimpleCwF.Tm-∘ = Tmᴾ-∘
SyntaxModel .SimpleCwF.ε = Raw.ε
SyntaxModel .SimpleCwF.ε-sub = ε-subᴾ
SyntaxModel .SimpleCwF.εη = εηᴾ
SyntaxModel .SimpleCwF._▷_ = Raw._▷_
SyntaxModel .SimpleCwF.p = pᴾ
SyntaxModel .SimpleCwF.q = qᴾ
SyntaxModel .SimpleCwF.⟨_,_⟩ = ⟨_,_⟩ᴾ
SyntaxModel .SimpleCwF.p-⟨⟩ = p-⟨⟩ᴾ
SyntaxModel .SimpleCwF.q-⟨⟩ = q-⟨⟩ᴾ
SyntaxModel .SimpleCwF.▷η = ▷ηᴾ
SyntaxModel .SimpleCwF.⟨⟩-∘ = ⟨⟩-∘ᴾ
SyntaxModel .SimpleCwF.Bool = Raw.Bool
SyntaxModel .SimpleCwF.true = trueᴾ
SyntaxModel .SimpleCwF.false = falseᴾ
SyntaxModel .SimpleCwF.if_then_else_ = ifᴾ
SyntaxModel .SimpleCwF.true[] = true[]ᴾ
SyntaxModel .SimpleCwF.false[] = false[]ᴾ
SyntaxModel .SimpleCwF.if[] = if[]ᴾ
SyntaxModel .SimpleCwF.βif-true = βif-trueᴾ
SyntaxModel .SimpleCwF.βif-false = βif-falseᴾ
SyntaxModel .SimpleCwF._×ᵗʸ_ = Raw._×ᵗʸ_
SyntaxModel .SimpleCwF.pair = pairᴾ
SyntaxModel .SimpleCwF.fst = fstᴾ
SyntaxModel .SimpleCwF.snd = sndᴾ
SyntaxModel .SimpleCwF.pair[] = pair[]ᴾ
SyntaxModel .SimpleCwF.fst[] = fst[]ᴾ
SyntaxModel .SimpleCwF.snd[] = snd[]ᴾ
SyntaxModel .SimpleCwF._⇒ᵗʸ_ = Raw._⇒ᵗʸ_
SyntaxModel .SimpleCwF.lam = lamᴾ
SyntaxModel .SimpleCwF.app = appᴾ
SyntaxModel .SimpleCwF.lam[] = lam[]ᴾ
SyntaxModel .SimpleCwF.app[] = app[]ᴾ
SyntaxModel .SimpleCwF.β⇒ = β⇒ᴾ
SyntaxModel .SimpleCwF.η⇒ = η⇒ᴾ
SyntaxModel .SimpleCwF.β×₁ = β×₁ᴾ
SyntaxModel .SimpleCwF.β×₂ = β×₂ᴾ
SyntaxModel .SimpleCwF.η× = η×ᴾ
