module DPRLR.README where

{-
  Paper guide to the mechanization.

  Checked with Agda 2.8.0 and Cubical 0.9.
-}

{- Section 2 — Modeling Reduction in Syntax ----------------------------- -}

{- Definition 2.1 — Directed intervals and inequality types. -}
import DPRLR.Simplicial.Interval using (𝟚 ; 𝟎 ; 𝟏)
import DPRLR.Simplicial.Hom using (_≤_ ; hom-refl)

{- Lemma 2.2 — Directed function extensionality. -}
import DPRLR.Simplicial.Function using
  (hom-funExt⁻ ; hom-funExt ; hom-funExt⁻≃)

{- Section 2.1 — Judgmental reduction as directed structure. -}
import DPRLR.Simplicial.Hom using (hom-map)
import DPRLR.Object.Model.Model using (SimpleCwF)
import DPRLR.Object.Model.Morphism.Base using (SimpleMorphism)
import DPRLR.Simplicial.Hom using (isThin)
import DPRLR.Simplicial.Segal using (isSegal ; segal-compose)

{- Section 2.2.1 — Directed higher inductive types.
   Raw contains the point, equality, and directed inequality constructors. -}
import DPRLR.Object.Syntax.Raw using
  ( Ty ; Ctx ; Sub ; Tm
  ; Bool ; _×ᵗʸ_ ; _⇒ᵗʸ_ ; ε ; _▷_
  ; id ; _∘_ ; ε-sub ; p ; q ; ⟨_,_⟩ ; _[_]Tm
  ; true ; false ; if_then_else_ ; pair ; fst ; snd ; lam ; app
  ; true[] ; false[] ; if[] ; pair[] ; fst[] ; snd[] ; lam[] ; app[]
  ; βif-true ; βif-false ; β×₁ ; β×₂ ; η× ; β⇒ ; η⇒
  )

{- Definition 2.3 — Dependent inequality types. -}
import DPRLR.Simplicial.Hom using (_⊢_≤[_]_)

{- Section 2.3 — The reflective subuniverse of preorders.
   Shapes and path transitivity describe the Segal condition; the
   localization maps then construct the preorder reflector. -}
import DPRLR.Simplicial.Shapes using (Λ² ; Δ² ; ι-horn)
import DPRLR.Simplicial.PathTransitive using
  (isPathTransitive ; isSegal≡isPathTransitive)
import DPRLR.Simplicial.PreorderLocalization using
  ( isPreorder ; Preorder
  ; isPreorder→isSet ; isPreorder→isThin ; isPreorder→isSegal
  ; isSetThinSegal→isPreorder
  ; Fᴾ ; ∥_∥ᴾ ; ηᴾ ; ∥∥ᴾ-isPreorder
  )

{- Lemma 2.5 — Universal property of localization. -}
import DPRLR.Simplicial.PreorderLocalization using (ηᴾ-universal)

{- Theorem 2.6 — Initiality of the localized syntax.
   Localized contains every substitution and term operation, equation,
   and directed reduction. Model packages this syntactic model as a CwF, which is initial. -}
import DPRLR.Object.Syntax.Localized using
  ( Subᴾ ; Tmᴾ
  ; idᴾ ; _∘ᴾ_ ; ε-subᴾ ; pᴾ ; qᴾ ; ⟨_,_⟩ᴾ ; _[_]Tmᴾ
  ; trueᴾ ; falseᴾ ; ifᴾ
  ; pairᴾ ; fstᴾ ; sndᴾ ; lamᴾ ; appᴾ
  ; id-leftᴾ ; id-rightᴾ ; ∘-assocᴾ ; εηᴾ
  ; p-⟨⟩ᴾ ; q-⟨⟩ᴾ ; ▷ηᴾ ; ⟨⟩-∘ᴾ ; Tmᴾ-id ; Tmᴾ-∘
  ; true[]ᴾ ; false[]ᴾ ; if[]ᴾ
  ; pair[]ᴾ ; fst[]ᴾ ; snd[]ᴾ ; lam[]ᴾ ; app[]ᴾ
  ; βif-trueᴾ ; βif-falseᴾ ; β×₁ᴾ ; β×₂ᴾ ; η×ᴾ ; β⇒ᴾ ; η⇒ᴾ
  )
import DPRLR.Object.Syntax.Model using (SyntaxModel)
import DPRLR.Object.Syntax.Initiality using (syntax-isInitial)

{- Section 3 — Logical Relations Model ---------------------------------- -}

{- Section 3.1 — Semantics of the judgmental structure.
   Judgment contains the final refined glued records used by the model. -}
import DPRLR.Gluing.LogicalRelations.Judgment using
  (GluCtx ; GluSub ; GluTy ; GluTm)

{- Section 3.2 — Semantics of product. -}
import DPRLR.Gluing.LogicalRelations.Product using
  (PROD ; FST ; SND ; FST[] ; SND[])

{- Definition 3.1 — Contravariant families. -}
import DPRLR.Simplicial.Contravariant using (isContravariant)

{- Definition 3.2 — Contravariant transport. -}
import DPRLR.Simplicial.Contravariant using (contrav-transport)

{- Lemma 3.3 — Functoriality of contravariant transport. -}
import DPRLR.Simplicial.Contravariant using
  (contravariant-transport-refl ; contravariant-transport-compose)

{- Lemma 3.4 — Universal property of contravariant transport. -}
import DPRLR.Simplicial.Contravariant using
  (contravariant-universal≃)

{- Lemma 3.5 — Preorder total spaces of contravariant families. -}
import DPRLR.Simplicial.Contravariant using (contravariant-total-isPreorder)

{- Corollary 3.6 — Glued substitutions and terms are preorders. -}
import DPRLR.Gluing.LogicalRelations.Judgment using
  (GluSub-isPreorder ; GluTm-isPreorder)

{- Lemma 3.7 — Inequalities at Σ-types. -}
import DPRLR.Simplicial.Product using (HomΣ≃)

{- Section 3.2.2 — Glued semantics for pair. -}
import DPRLR.Gluing.LogicalRelations.Product using
  (PAIR ; PAIR[])

{- Lemma 3.8 — Contravariance under reindexing. -}
import DPRLR.Simplicial.Contravariant using (contravariant-reindex)

{- Lemma 3.9 — Contravariance under products. -}
import DPRLR.Simplicial.Contravariant using (contravariant-×)

{- Section 3.2.3 — Glued terms respect the directed product quotient. -}
import DPRLR.Gluing.LogicalRelations.Product using
  (PROD-preserves-β₁ ; PROD-preserves-β₂)

{- Section 3.2.4 — The product η-reduction is validated too. -}
import DPRLR.Gluing.LogicalRelations.Product using (PROD-preserves-η)

{- Section 3.3 — Semantics of functions. -}
import DPRLR.Gluing.LogicalRelations.Function using (FUN)

{- Lemma 3.10 — Contravariance under dependent products. -}
import DPRLR.Simplicial.Contravariant using (contravariant-Π)

{- Section 3.3.1 — Glued substitution structure. -}
import DPRLR.Gluing.LogicalRelations.Substitution using
  (εᵍ ; ε-subᵍ ; εηᵍ ; idᵍ ; _∘ᵍ_ ; id-leftᵍ ; id-rightᵍ
  ; _[_]Tmᵍ ; Tm-idᵍ ; Tm-∘ᵍ ; _▷ᵍ_ ; pᵍ ; qᵍ ; ⟨_,_⟩ᵍ
  ; p-⟨⟩ᵍ ; q-⟨⟩ᵍ ; ▷ηᵍ ; ⟨⟩-∘ᵍ)

{- Section 3.3.2 — Glued semantics for lambda and application. -}
import DPRLR.Gluing.LogicalRelations.Function using
  (APP ; LAM ; APP[] ; LAM[])

{- Section 3.3.3 — Glued functions respect the directed quotient. -}
import DPRLR.Gluing.LogicalRelations.Function using
  (FUN-preserves-β ; FUN-preserves-η)

{- Section 3.4 — Semantics of Booleans and canonicity. -}
import DPRLR.Gluing.LogicalRelations.Bool using
  (BOOL ; TRUE ; FALSE ; IF ; TRUE[] ; FALSE[] ; IF[]
  ; IF-preserves-β-true ; IF-preserves-β-false)

{- Lemma 3.11 — Representable contravariant families. -}
import DPRLR.Simplicial.Contravariant using
  (representable-isContravariant)

{- Section 3.4.1 — Canonicity via the fundamental theorem of logical relations.
   GluingModel packages the structure used by FTLR. -}
import DPRLR.Gluing.GluingModel using (GluingCwF)
import DPRLR.Gluing.FTLR using (ftlr-section ; bool-canonicityᴾ)

{- Section 4 — Universes and Dependency --------------------------------- -}

{- Definition 4.1 — Discrete types. -}
import DPRLR.Simplicial.Discrete using
  (isDiscrete ; hom→path)

{- Axiom 4.3 — Boolean discreteness.
   This is a postulate of the synthetic simplicial layer. -}
import DPRLR.Simplicial.Discrete using (Bool₂-isDiscrete)

{- Section 5 — Binary Logical Relations and Parametricity --------------- -}

{- Lemma 5.1 — Binary contravariance.
   Only the implication from contravariance of the binary family to
   contravariance of its one-variable slices is mechanized. -}
import DPRLR.Simplicial.BinaryContravariant using (binary-contravariance)
