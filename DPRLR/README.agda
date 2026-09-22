module DPRLR.README where

{-
  This file is a curated guide to the formalization, ordered by the
  presentation in the paper.

  The formalization is checked against Agda v2.8.0 with cubical library v0.9.
  It covers the simply typed directed syntax via localization, unary gluing model, 
  boolean canonicity theorem, and the basic binary contravariance lemma.
-}

{-
  Section 2. Basic simplicial type theory used to model reduction.
-}
{-
    Section 2 and Definition 2.1.
    The directed interval has endpoints 𝟎 and 𝟏 and induces inequality types.
-}
import DPRLR.Simplicial.Interval using
  ( 𝟚
  ; 𝟎
  ; 𝟏
  )
import DPRLR.Simplicial.Hom using
  ( _≤_
  ; hom-refl
  ; path→hom
  )

{-
    Lemma 2.2.
    Inequalities between functions are equivalent to pointwise inequalities.
-}
import DPRLR.Simplicial.Function using
  ( hom-happly
  ; hom-funExt
  ; hom-happly≃
  )

{-
    Section 2.1.
    Inequalities are functorial: a map sends inequalities in the domain to
    inequalities in the codomain.
-}
import DPRLR.Simplicial.Hom using
  ( hom-map 
  )

{-
  Section 2.2. The simply typed object language and its initial directed CwF.
-}
{-
    Section 2.2.
    A model is a simply typed CwF with booleans, products, functions, and
    directed beta/eta reductions. In a directed model, substitution and term
    types are both set, thin, and Segal.
-}
import DPRLR.Object.Model.Model using
  ( SimpleCwF
  ; SimpleDirectedCwF
  )

{-
    Section 2.2.1.
    The raw directed HIT contains types, contexts, substitutions, terms, and
    the directed computation laws.
-}
import DPRLR.Object.Syntax.Raw.Base using
  ( Ty
  ; Ctx
  ; Sub
  ; Tm
  ; Bool
  ; _×ᵗʸ_
  ; _⇒ᵗʸ_
  ; ε
  ; _▷_
  ; id
  ; _∘_
  ; ε-sub
  ; p
  ; q
  ; ⟨_,_⟩
  ; _[_]Tm
  ; true
  ; false
  ; if_then_else_
  ; pair
  ; fst
  ; snd
  ; lam
  ; app
  ; true[]
  ; false[]
  ; if[]
  ; pair[]
  ; fst[]
  ; snd[]
  ; lam[]
  ; app[]
  ; βif-true
  ; βif-false
  ; β×₁
  ; β×₂
  ; η×
  ; β⇒
  ; η⇒
  )

{-
    Section 2.2.
    The raw constructors form a simply typed CwF before applying the reflector.
-}
import DPRLR.Object.Syntax.Raw.Model using
  ( RawSyntaxCwF
  )

{-
    Section 2.2.2.
    Thinness says that parallel inequalities form propositions.
-}
import DPRLR.Simplicial.Hom using
  ( isThin
  )

{-
    Section 2.2.3.
    Segal types have contractible spaces of composites, hence composable inequalities.
-}
import DPRLR.Simplicial.Segal using
  ( isSegal
  ; segal-compose
  )

{-
    Section 2.2.2, Section 2.2.3, and Appendix A.
    The localization reflector produces types that are set, thin, and Segal.
-}
import DPRLR.Simplicial.Shapes using
  ( Δ²
  ; Λ²₁
  ; spine₂
  )
import DPRLR.Simplicial.PreorderLocalization using
  ( Fᴾ
  ; ∥_∥ᴾ
  ; ηᴾ
  ; rec
  ; rec-unique
  ; ηᴾ-universal
  ; isPreorderP
  ; isPreorder→isSet
  ; isPreorder→isThin
  ; isPreorder→isSegal
  ; isSetThinSegal→isPreorder
  )

{-
    Section 2.2.2, Section 2.2.3, and Appendix A.
    Raw substitutions and terms are reflected into the set, thin, Segal
    subuniverse.
-}
import DPRLR.Object.Syntax.Localized.Base using
  ( Subᴾ
  ; Tmᴾ
  ; ηSubᴾ
  ; ηTmᴾ
  ; Subᴾ-isSet
  ; Subᴾ-isThin
  ; Subᴾ-isSegal
  ; Tmᴾ-isSet
  ; Tmᴾ-isThin
  ; Tmᴾ-isSegal
  )

{-
    Section 2.2.
    The reflected syntax inherits all CwF operations and directed computation laws.
-}
import DPRLR.Object.Syntax.Localized.Base using
  ( idᴾ
  ; _∘ᴾ_
  ; ε-subᴾ
  ; pᴾ
  ; qᴾ
  ; ⟨_,_⟩ᴾ
  ; _[_]Tmᴾ
  ; trueᴾ
  ; falseᴾ
  ; ifᴾ
  ; pairᴾ
  ; fstᴾ
  ; sndᴾ
  ; lamᴾ
  ; appᴾ
  ; true[]ᴾ
  ; false[]ᴾ
  ; if[]ᴾ
  ; pair[]ᴾ
  ; fst[]ᴾ
  ; snd[]ᴾ
  ; lam[]ᴾ
  ; app[]ᴾ
  ; βif-trueᴾ
  ; βif-falseᴾ
  ; β×₁ᴾ
  ; β×₂ᴾ
  ; η×ᴾ
  ; β⇒ᴾ
  ; η⇒ᴾ
  )

{-
    Section 2.2.
    The localized syntax is packaged as the directed syntactic model.
-}
import DPRLR.Object.Syntax.Localized.Model using
  ( LocalizedSyntaxCwF
  ; LocalizedSyntaxModel
  )

import DPRLR.Object.Model.Morphism.Base using
  ( SimpleMorphism
  ; isInitialDirected
  )

import DPRLR.Object.Syntax.Initiality.Raw using
  ( raw-syntax-isInitial
  )

import DPRLR.Object.Syntax.Initiality.Localized using
  ( localized-syntax-isInitial
  )

{-
    Definition 2.3.
    Dependent inequality types compare elements over an inequality in the base.
-}
import DPRLR.Simplicial.Hom using
  ( _⊢_≤[_]_
  )

{-
  Sections 3.2--3.4 and Section 4.2. Simplicial structure used by gluing.
-}
{-
    Definition 3.1.
    A contravariant family has a contractible space of lifts along every inequality.
-}
import DPRLR.Simplicial.Contravariant using
  ( isContravariant
  )

{-
    Definition 3.2.
    Contravariant transport moves evidence backwards along reductions.
-}
import DPRLR.Simplicial.Contravariant using
  ( contrav-transport
  ; contravariant-lift-hom
  )

{-
    Lemma 3.3 and Lemma 3.4.
    Contravariant transport is functorial and satisfies its universal property.
    The second half of Lemma 3.3 requires more simplicial primitives, which we 
    don't develop in this formalization.
-}
import DPRLR.Simplicial.Contravariant using
  ( contravariant-transport-refl
  ; contravariant-universal≃
  )

{-
    Lemma 3.5.
    Inequalities at products and Σ-types are constructed componentwise.
-}
import DPRLR.Simplicial.Product using
  ( HomP×
  ; HomPΣ
  ; Σ≤
  )

{-
    Lemma 3.6.
    Representable families are contravariant.
-}
import DPRLR.Simplicial.Contravariant using
  ( representable-isContravariant
  )

import DPRLR.Simplicial.Contravariant using
  ( contravariant-total-isSegal
  ; contravariant-total-isThin
  )

{-
    Section 4.2.
    Definition 4.1
    Example 4.2
    Discrete types identify inequalities with ordinary paths.
    Note that Bool₂-isDiscrete is a postulate because it is an axiom
    in simplicial type theory, e.g. 
    - Axiom 7 in Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz. 2026. 
        Directed univalence in simplicial homotopy type theory.
    - Axiom 4 in Daniel Gratzer, Jonathan Weinberger, and Ulrik Buchholtz. 2026. 
        The ∞-category of ∞-categories in simplicial type theory. 
-}
import DPRLR.Simplicial.Discrete using
  ( isDiscrete
  ; hom→path
  ; hom-to-isContr
  ; Bool₂-isDiscrete
  )

{-
    Section 3 and Section 4.2.1.
    Lemma 4.3
    Contravariant families are closed under the type formers used in gluing.
-}
import DPRLR.Simplicial.Contravariant using
  ( contravariant-fiber-isDiscrete
  ; contravariant-reindex
  ; contravariant-discrete
  ; contravariant-Σ
  ; contravariant-Σ-discrete
  ; contravariant-×
  ; contravariant-Π
  )

{-
  Section 3 and Appendix B. Unary gluing and boolean canonicity.
-}
{-
    Section 3.1.
    Glued contexts, substitutions, types, terms, and term inequalities refine
    the base CwF.
-}
import DPRLR.Gluing.LogicalRelations.Judgment using
  ( GluCtx
  ; GluSub
  ; GluTy
  ; GluTm
  ; _≤ᵍ_
  ; ≤ᵍ≃≤
  )

{-
    Section 3.1, Section 3.3 and Appendix B.2.
    The gluing model validates substitution and context-extension structure.
-}
import DPRLR.Gluing.LogicalRelations.Substitution using
  ( εᵍ
  ; ε-subᵍ
  ; εηᵍ
  ; idᵍ
  ; _∘ᵍ_
  ; id-leftᵍ
  ; id-rightᵍ
  ; _[_]Tmᵍ
  ; Tm-idᵍ
  ; Tm-∘ᵍ
  ; _▷ᵍ_
  ; pᵍ
  ; qᵍ
  ; ⟨_,_⟩ᵍ
  ; p-⟨⟩ᵍ
  ; q-⟨⟩ᵍ
  ; ▷ηᵍ
  ; ⟨⟩-∘ᵍ
  )

{-
    Section 3.2.
    Products in the gluing model.
-}
import DPRLR.Gluing.LogicalRelations.Product using
  ( PROD
  ; PAIR
  ; FST
  ; SND
  ; PAIR[]
  ; FST[]
  ; SND[]
  ; PROD-preserves-β₁
  ; PROD-preserves-β₂
  ; PROD-preserves-η
  )

{-
    Section 3.3.
    Functions in the gluing model.
-}
import DPRLR.Gluing.LogicalRelations.Function using
  ( FUN
  ; APP
  ; LAM
  ; APP[]
  ; LAM[]
  ; FUN-preserves-β
  ; FUN-preserves-η
  )

{-
    Section 3.4.
    The boolean predicate states that a closed boolean reduces to a canonical boolean.
-}
import DPRLR.Gluing.LogicalRelations.Bool using
  ( BOOL
  ; TRUE
  ; FALSE
  ; IF
  ; TRUE[]
  ; FALSE[]
  ; IF[]
  ; IF-preserves-β-true
  ; IF-preserves-β-false
  )

{-
    Section 3.
    The gluing clauses assemble into a simply typed CwF.
-}
import DPRLR.Gluing.GluingModel using
  ( GluingCwF
  )

{-
    Section 3.4.
    The gluing model is repackaged as a displayed model over the syntax.
-}
import DPRLR.Gluing.DisplayedModel using
  ( CTX
  ; TY
  ; SUB
  ; TM
  ; BOOLᴰ
  ; PRODᴰ
  ; FUNᴰ
  ; GluingDisplayed
  ; GluingDisplayedDirected
  ; GluingDirectedModel
  )

{-
    Section 3.4.
    The fundamental theorem is the displayed section obtained from the syntax eliminator.
-}
import DPRLR.Gluing.FTLR using
  ( ftlr-section
  )

{-
    Section 3.4.
    Boolean canonicity extracts a canonical boolean and a reduction from the fundamental theorem.
-}
import DPRLR.Gluing.FTLR using
  ( bool-canonicityᴾ
  )

{-
  Section 5. Binary logical relations and parametricity.
-}
{-
    Lemma 5.1.
    A contravariant binary relation has contravariant one-variable slices.
    This only proves the forward direction of Lemma 5.1. The backward direction
    requires more simplicial primitives.
-}
import DPRLR.Simplicial.BinaryContravariant using
  ( SlicesContravariant
  ; binary-contravariance
  )
