open import Cubical.Foundations.Prelude using (Level)

open import DPRLR.Object.Model.Model

module DPRLR.Gluing.Base {ℓS ℓM : Level} (𝓜 : SimpleCwF ℓS ℓM) where
  open SimpleCwF 𝓜 public
    using (_≤⟨_⟩_ ; _∎≤)
    renaming
      ( Ctx to Ctxₘ ; Ty to Tyₘ ; Sub to Subₘ ; Tm to Tmₘ
      ; id to idₘ ; _∘_ to _∘ₘ_ ; id-left to id-leftₘ ; id-right to id-rightₘ
      ; ∘-assoc to ∘-assocₘ
      ; _[_]Tm to _[_]Tmₘ ; Tm-id to Tm-idₘ ; Tm-∘ to Tm-∘ₘ
      ; ε to εₘ ; ε-sub to ε-subₘ ; εη to εηₘ
      ; _▷_ to _▷ₘ_ ; p to pₘ ; q to qₘ ; ⟨_,_⟩ to ⟨_,_⟩ₘ
      ; p-⟨⟩ to p-⟨⟩ₘ ; q-⟨⟩ to q-⟨⟩ₘ ; ▷η to ▷ηₘ ; ⟨⟩-∘ to ⟨⟩-∘ₘ
      ; Bool to Boolₘ ; true to trueₘ ; false to falseₘ ; if_then_else_ to ifₘ_then_else_
      ; true[] to true[]ₘ ; false[] to false[]ₘ ; if[] to if[]ₘ
      ; βif-true to βif-trueₘ ; βif-false to βif-falseₘ
      ; _×ᵗʸ_ to _×ₘ_ ; pair to pairₘ ; fst to fstₘ ; snd to sndₘ
      ; pair[] to pair[]ₘ ; fst[] to fst[]ₘ ; snd[] to snd[]ₘ
      ; β×₁ to β×₁ₘ ; β×₂ to β×₂ₘ ; η× to η×ₘ
      ; _⇒ᵗʸ_ to _⇒ₘ_ ; lam to lamₘ ; app to appₘ ; lam[] to lam[]ₘ ; app[] to app[]ₘ
      ; β⇒ to β⇒ₘ ; η⇒ to η⇒ₘ ; β⇒-subst to β⇒-substₘ
      ; sub-set to sub-setₘ ; tm-set to tm-setₘ ; tm-thin to tm-thinₘ ; tm-segal to tm-segalₘ
      ; sub-local to sub-localₘ ; tm-local to tm-localₘ
      )
