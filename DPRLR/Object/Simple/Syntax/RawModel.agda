module DPRLR.Object.Simple.Syntax.RawModel where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)

open import DPRLR.Object.Simple.Model using (SimpleCwF)
open import DPRLR.Object.Simple.Syntax.Base

RawSyntaxCwF : SimpleCwF ℓ-zero
SimpleCwF.Ctx RawSyntaxCwF = Ctx
SimpleCwF.Ty RawSyntaxCwF = Ty
SimpleCwF.Sub RawSyntaxCwF = Sub
SimpleCwF.Tm RawSyntaxCwF = Tm
SimpleCwF.id RawSyntaxCwF = id
SimpleCwF._∘_ RawSyntaxCwF = _∘_
SimpleCwF.id-left RawSyntaxCwF = id-left
SimpleCwF.id-right RawSyntaxCwF = id-right
SimpleCwF.∘-assoc RawSyntaxCwF = ∘-assoc
SimpleCwF._[_]Tm RawSyntaxCwF = _[_]Tm
SimpleCwF.Tm-id RawSyntaxCwF = Tm-id
SimpleCwF.Tm-∘ RawSyntaxCwF = Tm-∘
SimpleCwF.ε RawSyntaxCwF = ε
SimpleCwF.ε-sub RawSyntaxCwF = ε-sub
SimpleCwF.εη RawSyntaxCwF = εη
SimpleCwF._▷_ RawSyntaxCwF = _▷_
SimpleCwF.p RawSyntaxCwF = p
SimpleCwF.q RawSyntaxCwF = q
SimpleCwF.⟨_,_⟩ RawSyntaxCwF = ⟨_,_⟩
SimpleCwF.p-⟨⟩ RawSyntaxCwF = p-⟨⟩
SimpleCwF.q-⟨⟩ RawSyntaxCwF = q-⟨⟩
SimpleCwF.▷η RawSyntaxCwF = ▷η
SimpleCwF.⟨⟩-∘ RawSyntaxCwF = ⟨⟩-∘
SimpleCwF.Bool RawSyntaxCwF = Bool
SimpleCwF.true RawSyntaxCwF = true
SimpleCwF.false RawSyntaxCwF = false
SimpleCwF.if_then_else_ RawSyntaxCwF = if_then_else_
SimpleCwF.true[] RawSyntaxCwF = true[]
SimpleCwF.false[] RawSyntaxCwF = false[]
SimpleCwF.if[] RawSyntaxCwF = if[]
SimpleCwF.βif-true RawSyntaxCwF = βif-true
SimpleCwF.βif-false RawSyntaxCwF = βif-false
SimpleCwF._×ᵗʸ_ RawSyntaxCwF = _×ᵗʸ_
SimpleCwF.pair RawSyntaxCwF = pair
SimpleCwF.fst RawSyntaxCwF = fst
SimpleCwF.snd RawSyntaxCwF = snd
SimpleCwF.pair[] RawSyntaxCwF = pair[]
SimpleCwF.fst[] RawSyntaxCwF = fst[]
SimpleCwF.snd[] RawSyntaxCwF = snd[]
SimpleCwF._⇒ᵗʸ_ RawSyntaxCwF = _⇒ᵗʸ_
SimpleCwF.lam RawSyntaxCwF = lam
SimpleCwF.app RawSyntaxCwF = app
SimpleCwF.lam[] RawSyntaxCwF = lam[]
SimpleCwF.app[] RawSyntaxCwF = app[]
SimpleCwF.β⇒ RawSyntaxCwF = β⇒
SimpleCwF.η⇒ RawSyntaxCwF = η⇒
SimpleCwF.β×₁ RawSyntaxCwF = β×₁
SimpleCwF.β×₂ RawSyntaxCwF = β×₂
SimpleCwF.η× RawSyntaxCwF = η×
