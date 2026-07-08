module DPRLR.Object.Simple.InitialModel where

open import Cubical.Foundations.Prelude using (ℓ-zero)

open import DPRLR.Object.Simple.Model using
  (SimpleCwF ; SimpleDirectedStructure ; SimpleDirectedCwF)
open import DPRLR.Object.Simple.Syntax.LocalizedModel

SyntaxCwF : SimpleCwF ℓ-zero
SyntaxCwF = LocalizedSyntaxCwF

SyntaxDirected : SimpleDirectedStructure SyntaxCwF
SyntaxDirected = LocalizedSyntaxDirected

SyntaxModel : SimpleDirectedCwF ℓ-zero
SyntaxModel = LocalizedSyntaxModel
