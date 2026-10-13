# Artifact evaluation instructions

This artifact accompanies the paper on _Directed proof-relevant logical relations in simplicial HoTT_. It contains a
Cubical Agda mechanization of the simply typed directed syntax, unary gluing model, and Boolean canonicity theorem. The
Agda logos in the paper identify the definitions and theorems indexed below. [DPRLR/README.agda](DPRLR/README.agda) follows the same
order and imports the relevant definitions and proofs at each logo.

## Installation and sanity check

Use [Agda 2.8.0](https://agda.readthedocs.io/en/v2.8.0/getting-started/installation.html) with the
[Cubical library 0.9](https://github.com/agda/cubical/releases/tag/v0.9). Run the following command from root to build the mechanization:

```sh
agda --no-allow-unsolved-metas --build-library
```

Successful exit without errors is the typechecking criterion. It should take about a minute or two.

## Paper-to-mechanization map

Each group corresponds to one Agda logo in the paper, in the same order as the import groups in `README.agda`. The first column labels each group; blank cells continue the same group.

| Paper reference | Paper notation | Mechanization notation | Comment |
| --- | --- | --- | --- |
| **Definition 2.1 — Inequality types** | 𝟚 | [`𝟚`](DPRLR/Simplicial/Interval.agda) |  |
|  | $\mathsf{i0}$ | [`𝟎`](DPRLR/Simplicial/Interval.agda) |  |
|  | $\mathsf{i1}$ | [`𝟏`](DPRLR/Simplicial/Interval.agda) |  |
|  | $x \leq_A y$ | [`_≤_`](DPRLR/Simplicial/Hom.agda) |  |
|  | $\mathrm{id}_x : x \leq_A x$ | [`hom-refl`](DPRLR/Simplicial/Hom.agda) |  |
| **Lemma 2.2 — Directed function extensionality** | canonical map $(f \leq g) \to ((x:A) \to f\,x \leq g\,x)$ | [`hom-funExt⁻`](DPRLR/Simplicial/Function.agda) |  |
|  | inverse map | [`hom-funExt`](DPRLR/Simplicial/Function.agda) |  |
|  | equivalence $(f \leq g) \simeq ((x:A) \to f\,x \leq g\,x)$ | [`hom-funExt⁻≃`](DPRLR/Simplicial/Function.agda) |  |
| **Section 2.1 — Judgmental reduction as directed structure** | $\mathrm{mono}_f$ | [`hom-map`](DPRLR/Simplicial/Hom.agda) | Figure 1 requires $\mathsf{Sub}$ and $\mathsf{Tm}$ to land in $\mathcal U_p$; the corresponding fields of `SimpleCwF` take values in `Preorder`. |
|  | $\mathsf{DirectedCwF}$ (Figure 1) | [`SimpleCwF`](DPRLR/Object/Model/Model.agda) |  |
|  | directed CwF morphism | [`SimpleMorphism`](DPRLR/Object/Model/Morphism/Base.agda) |  |
|  | $\mathrm{isThin}(X)$ | [`isThin`](DPRLR/Simplicial/Hom.agda) |  |
|  | $\mathrm{isSegal}(X)$ | [`isSegal`](DPRLR/Simplicial/Segal.agda) |  |
|  | $f\cdot g$ | [`segal-compose`](DPRLR/Simplicial/Segal.agda) |  |
| **Section 2.2.1 — Directed higher inductive types** | $\mathsf{Ty}$ | [`Ty`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{Ctx}$ | [`Ctx`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{Sub}$ | [`Sub`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{Tm}$ | [`Tm`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{Bool}$ | [`Bool`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\times$ | [`_×ᵗʸ_`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\Rightarrow$ | [`_⇒ᵗʸ_`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\cdot$ | [`ε`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\Gamma\triangleright A$ | [`_▷_`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{id}$ | [`id`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\circ$ | [`_∘_`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\epsilon_\Gamma$ | [`ε-sub`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{p}$ | [`p`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{q}$ | [`q`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $(\sigma,M)$ | [`⟨_,_⟩`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $M[\sigma]$ | [`_[_]Tm`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{true}$ | [`true`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{false}$ | [`false`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{if}$ | [`if_then_else_`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{pair},\mathsf{fst},\mathsf{snd}$ | [`pair`, `fst`, `snd`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{lam},\mathsf{app}$ | [`lam`, `app`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{true}[\sigma]=\mathsf{true}$ | [`true[]`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{false}[\sigma]=\mathsf{false}$ | [`false[]`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $(\mathsf{if}\,C\,T\,F\,B)[\sigma]=\mathsf{if}\,C[\sigma]\,T[\sigma]\,F[\sigma]\,B[\sigma]$ | [`if[]`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{pair}(M,N)[\sigma]=\mathsf{pair}(M[\sigma],N[\sigma])$ | [`pair[]`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{fst}(P)[\sigma]=\mathsf{fst}(P[\sigma])$ | [`fst[]`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{snd}(P)[\sigma]=\mathsf{snd}(P[\sigma])$ | [`snd[]`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{lam}(N)[\sigma]=\mathsf{lam}(N[(\sigma\circ\mathsf p,\mathsf q)])$ | [`lam[]`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{app}(F,M)[\sigma]=\mathsf{app}(F[\sigma],M[\sigma])$ | [`app[]`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{Bool}_{\mathsf{true}}:\mathsf{if}\,C\,T\,F\,\mathsf{true}\leq T$ | [`βif-true`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\mathsf{Bool}_{\mathsf{false}}:\mathsf{if}\,C\,T\,F\,\mathsf{false}\leq F$ | [`βif-false`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\times_{\beta_1},\times_{\beta_2},\times_\eta$ | [`β×₁`, `β×₂`, `η×`](DPRLR/Object/Syntax/Raw.agda) |  |
|  | $\Rightarrow_\beta,\Rightarrow_\eta$ | [`β⇒`, `η⇒`](DPRLR/Object/Syntax/Raw.agda) |  |
| **Definition 2.3 — Dependent inequality types** | $u \leq_{Q(h)} v$ | [`_⊢_≤[_]_`](DPRLR/Simplicial/Hom.agda) |  |
| **Section 2.3 — Reflective subuniverse of preorders** | $\Lambda^2_1$ | [`Λ²`](DPRLR/Simplicial/Shapes.agda) | The paper's horn-locality definition of the Segal condition is called `isPathTransitive` here. The mechanization's `isSegal` uses contractible types of square-based composites; `isSegal≡isPathTransitive` proves the two definitions equivalent. |
|  | $\Delta^2$ | [`Δ²`](DPRLR/Simplicial/Shapes.agda) |  |
|  | $\iota$ | [`ι-horn`](DPRLR/Simplicial/Shapes.agda) |  |
|  | path transitivity | [`isPathTransitive`](DPRLR/Simplicial/PathTransitive.agda) |  |
|  | equivalence with the Segal condition | [`isSegal≡isPathTransitive`](DPRLR/Simplicial/PathTransitive.agda) |  |
|  | $\mathrm{isPreorder}(X)$ | [`isPreorder`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
|  | $\mathcal U_p$ | [`Preorder`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
|  | $X:\mathcal U_p\;\Rightarrow\;\mathrm{isSet}(X)$ | [`isPreorder→isSet`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
|  | $X:\mathcal U_p\;\Rightarrow\;\mathrm{isThin}(X)$ | [`isPreorder→isThin`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
|  | $X:\mathcal U_p\;\Rightarrow\;\mathrm{isSegal}(X)$ | [`isPreorder→isSegal`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
|  | $\mathrm{isSet}(X)\land\mathrm{isThin}(X)\land\mathrm{isSegal}(X)\;\Rightarrow\;X:\mathcal U_p$ | [`isSetThinSegal→isPreorder`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
|  | $\mathcal F_p$ | [`Fᴾ`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
|  | $\mathsf P X$ | [`∥_∥ᴾ`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
|  | $\eta_X$ | [`ηᴾ`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
|  | $\mathsf P X:\mathcal U_p$ | [`∥∥ᴾ-isPreorder`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
| **Lemma 2.5 — Universal property of localization** | $(-\circ\eta_X):(\mathsf P X\to Y)\simeq(X\to Y)$ | [`ηᴾ-universal`](DPRLR/Simplicial/PreorderLocalization.agda) |  |
| **Theorem 2.6 — Initiality of the localized syntax** | $\mathsf{Sub}\,\Gamma\,\Delta$ | [`Subᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{Tm}\,\Gamma\,A$ | [`Tmᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{id}$ | [`idᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\circ$ | [`_∘ᴾ_`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\epsilon_\Gamma$ | [`ε-subᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{p}$ | [`pᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{q}$ | [`qᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $(\sigma,M)$ | [`⟨_,_⟩ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $M[\sigma]$ | [`_[_]Tmᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{true}$ | [`trueᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{false}$ | [`falseᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{if}\,C\,T\,F\,B$ | [`ifᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{pair}$ | [`pairᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{fst}$ | [`fstᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{snd}$ | [`sndᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{lam}$ | [`lamᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{app}$ | [`appᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{id}\circ\sigma=\sigma$ | [`id-leftᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\sigma\circ\mathsf{id}=\sigma$ | [`id-rightᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $(\rho\circ\tau)\circ\sigma=\rho\circ(\tau\circ\sigma)$ | [`∘-assocᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\sigma=\epsilon_\Gamma$ for $\sigma:\mathsf{Sub}\,\Gamma\,\cdot$ | [`εηᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{p}\circ(\sigma,M)=\sigma$ | [`p-⟨⟩ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{q}[(\sigma,M)]=M$ | [`q-⟨⟩ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $(\mathsf{p},\mathsf{q})=\mathsf{id}$ | [`▷ηᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $(\sigma,M)\circ\rho=(\sigma\circ\rho,M[\rho])$ | [`⟨⟩-∘ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $M[\mathsf{id}]=M$ | [`Tmᴾ-id`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $M[\tau][\sigma]=M[\tau\circ\sigma]$ | [`Tmᴾ-∘`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{true}[\sigma]=\mathsf{true}$ | [`true[]ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{false}[\sigma]=\mathsf{false}$ | [`false[]ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $(\mathsf{if}\,C\,T\,F\,B)[\sigma]=\mathsf{if}\,C[\sigma]\,T[\sigma]\,F[\sigma]\,B[\sigma]$ | [`if[]ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{pair}(M,N)[\sigma]=\mathsf{pair}(M[\sigma],N[\sigma])$ | [`pair[]ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{fst}(P)[\sigma]=\mathsf{fst}(P[\sigma])$ | [`fst[]ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{snd}(P)[\sigma]=\mathsf{snd}(P[\sigma])$ | [`snd[]ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{lam}(N)[\sigma]=\mathsf{lam}(N[(\sigma\circ\mathsf p,\mathsf q)])$ | [`lam[]ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{app}(F,M)[\sigma]=\mathsf{app}(F[\sigma],M[\sigma])$ | [`app[]ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{Bool}_{\mathsf{true}}:\mathsf{if}\,C\,T\,F\,\mathsf{true}\leq T$ | [`βif-trueᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathsf{Bool}_{\mathsf{false}}:\mathsf{if}\,C\,T\,F\,\mathsf{false}\leq F$ | [`βif-falseᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\times_{\beta_1}:\mathsf{fst}(\mathsf{pair}(M,N))\leq M$ | [`β×₁ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\times_{\beta_2}:\mathsf{snd}(\mathsf{pair}(M,N))\leq N$ | [`β×₂ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\times_\eta:\mathsf{pair}(\mathsf{fst}(P),\mathsf{snd}(P))\leq P$ | [`η×ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\Rightarrow_\beta:\mathsf{app}(\mathsf{lam}(N),M)\leq N[(\mathsf{id},M)]$ | [`β⇒ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\Rightarrow_\eta:\mathsf{lam}(\mathsf{app}(F[\mathsf p],\mathsf q))\leq F$ | [`η⇒ᴾ`](DPRLR/Object/Syntax/Localized.agda) |  |
|  | $\mathcal I$ | [`SyntaxModel`](DPRLR/Object/Syntax/Model.agda) |  |
|  | initiality of $\mathcal I$ | [`syntax-isInitial`](DPRLR/Object/Syntax/Initiality.agda) |  |
| **Section 3.1 — Semantics of the judgmental structure** | $\mathsf{CTX}$ | [`GluCtx`](DPRLR/Gluing/LogicalRelations/Judgment.agda) |  |
|  | $\mathsf{SUB}$ | [`GluSub`](DPRLR/Gluing/LogicalRelations/Judgment.agda) |  |
|  | $\mathsf{TY}$ | [`GluTy`](DPRLR/Gluing/LogicalRelations/Judgment.agda) |  |
|  | $\mathsf{TM}$ | [`GluTm`](DPRLR/Gluing/LogicalRelations/Judgment.agda) |  |
| **Section 3.2 — Semantics of product** | $\mathsf{PROD}$ | [`PROD`](DPRLR/Gluing/LogicalRelations/Product.agda) |  |
|  | $\mathsf{FST}$ | [`FST`](DPRLR/Gluing/LogicalRelations/Product.agda) |  |
|  | $\mathsf{SND}$ | [`SND`](DPRLR/Gluing/LogicalRelations/Product.agda) |  |
|  | substitution laws for $\mathsf{FST},\mathsf{SND}$ | [`FST[]`, `SND[]`](DPRLR/Gluing/LogicalRelations/Product.agda) |  |
| **Definition 3.1 — Contravariant families** | $\mathrm{isContrav}(C)$ | [`isContravariant`](DPRLR/Simplicial/Contravariant.agda) |  |
| **Definition 3.2 — Contravariant transport** | $f^*v$ | [`contrav-transport`](DPRLR/Simplicial/Contravariant.agda) |  |
| **Lemma 3.3 — Functoriality of contravariant transport** | $(\mathrm{id}_x)^*v=v$ | [`contravariant-transport-refl`](DPRLR/Simplicial/Contravariant.agda) |  |
|  | $(f\cdot g)^*w=f^*(g^*w)$ | [`contravariant-transport-compose`](DPRLR/Simplicial/Contravariant.agda) |  |
| **Lemma 3.4 — Universal property of contravariant transport** | $(u \leq_{C(f)} v) \simeq (u=f^*v)$ | [`contravariant-universal≃`](DPRLR/Simplicial/Contravariant.agda) |  |
| **Lemma 3.5 — Preorder total spaces of contravariant families** | $\sum_{x:X} C(x) : \mathcal U_p$ | [`contravariant-total-isPreorder`](DPRLR/Simplicial/Contravariant.agda) |  |
| **Corollary 3.6 — Glued substitutions and terms are preorders** | $\mathsf{SUB}\,\Gamma\,\Delta:\mathcal U_p$ | [`GluSub-isPreorder`](DPRLR/Gluing/LogicalRelations/Judgment.agda) |  |
|  | $\mathsf{TM}\,\Gamma\,A:\mathcal U_p$ | [`GluTm-isPreorder`](DPRLR/Gluing/LogicalRelations/Judgment.agda) |  |
| **Lemma 3.7 — Inequalities at $\Sigma$-types** | $\bigl(\sum_{h:x\leq_A y}u\leq_{B(h)}v\bigr)\simeq((x,u)\leq_{\Sigma B}(y,v))$ | [`HomΣ≃`](DPRLR/Simplicial/Product.agda) |  |
| **Section 3.2.2 — Glued semantics for product and pair** | $\mathsf{PAIR}$ | [`PAIR`](DPRLR/Gluing/LogicalRelations/Product.agda) |  |
|  | substitution law for $\mathsf{PAIR}$ | [`PAIR[]`](DPRLR/Gluing/LogicalRelations/Product.agda) |  |
| **Lemma 3.8 — Contravariance under reindexing** | $C\circ g$ | [`contravariant-reindex`](DPRLR/Simplicial/Contravariant.agda) |  |
| **Lemma 3.9 — Contravariance under products** | $x\mapsto C(x)\times D(x)$ | [`contravariant-×`](DPRLR/Simplicial/Contravariant.agda) |  |
| **Section 3.2.3 — Glued terms respect the directed product quotient** | $\mathsf{FST}(\mathsf{PAIR}(M,N))\leq M$ | [`PROD-preserves-β₁`](DPRLR/Gluing/LogicalRelations/Product.agda) |  |
|  | $\mathsf{SND}(\mathsf{PAIR}(M,N))\leq N$ | [`PROD-preserves-β₂`](DPRLR/Gluing/LogicalRelations/Product.agda) |  |
| **Section 3.2.4 — Product $\eta$ reduction** | $\mathsf{PAIR}(\mathsf{FST}(P),\mathsf{SND}(P))\leq P$ | [`PROD-preserves-η`](DPRLR/Gluing/LogicalRelations/Product.agda) |  |
| **Section 3.3 — Semantics of functions** | $\mathsf{FUN}$ | [`FUN`](DPRLR/Gluing/LogicalRelations/Function.agda) |  |
| **Lemma 3.10 — Contravariance under dependent products** | $x\mapsto\prod_y C(x,y)$ | [`contravariant-Π`](DPRLR/Simplicial/Contravariant.agda) |  |
| **Section 3.3.1 — Glued substitution structure** | $\cdot$ | [`εᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\epsilon_\Gamma$ | [`ε-subᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\sigma=\epsilon_\Gamma$ for $\sigma:\mathsf{SUB}\,\Gamma\,\cdot$ | [`εηᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\mathsf{ID}$ | [`idᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\circ$ | [`_∘ᵍ_`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\mathsf{ID}\circ\sigma=\sigma$ | [`id-leftᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\sigma\circ\mathsf{ID}=\sigma$ | [`id-rightᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $M[\sigma]$ | [`_[_]Tmᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $M[\mathsf{ID}]=M$ | [`Tm-idᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $M[\tau][\sigma]=M[\tau\circ\sigma]$ | [`Tm-∘ᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\Gamma\triangleright A$ | [`_▷ᵍ_`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\mathsf p$ | [`pᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\mathsf q$ | [`qᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $(\sigma,M)$ | [`⟨_,_⟩ᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\mathsf p\circ(\sigma,M)=\sigma$ | [`p-⟨⟩ᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $\mathsf q[(\sigma,M)]=M$ | [`q-⟨⟩ᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $(\mathsf p,\mathsf q)=\mathsf{ID}$ | [`▷ηᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
|  | $(\sigma,M)\circ\rho=(\sigma\circ\rho,M[\rho])$ | [`⟨⟩-∘ᵍ`](DPRLR/Gluing/LogicalRelations/Substitution.agda) |  |
| **Section 3.3.2 — Glued semantics for lambda and application** | $\mathsf{APP},\mathsf{LAM}$ | [`APP`, `LAM`](DPRLR/Gluing/LogicalRelations/Function.agda) |  |
|  | their substitution laws | [`APP[]`, `LAM[]`](DPRLR/Gluing/LogicalRelations/Function.agda) |  |
| **Section 3.3.3 — Glued functions respect the directed quotient** | function $\beta$ reduction | [`FUN-preserves-β`](DPRLR/Gluing/LogicalRelations/Function.agda) |  |
|  | function $\eta$ reduction | [`FUN-preserves-η`](DPRLR/Gluing/LogicalRelations/Function.agda) |  |
| **Section 3.4 — Semantics of Booleans and canonicity** | $\mathsf{BOOL}$ | [`BOOL`](DPRLR/Gluing/LogicalRelations/Bool.agda) |  |
|  | $\mathsf{TRUE}$ | [`TRUE`](DPRLR/Gluing/LogicalRelations/Bool.agda) |  |
|  | $\mathsf{FALSE}$ | [`FALSE`](DPRLR/Gluing/LogicalRelations/Bool.agda) |  |
|  | $\mathsf{IF}$ | [`IF`](DPRLR/Gluing/LogicalRelations/Bool.agda) |  |
|  | substitution laws for $\mathsf{TRUE},\mathsf{FALSE},\mathsf{IF}$ | [`TRUE[]`, `FALSE[]`, `IF[]`](DPRLR/Gluing/LogicalRelations/Bool.agda) |  |
|  | Boolean $\beta$ reductions | [`IF-preserves-β-true`](DPRLR/Gluing/LogicalRelations/Bool.agda), [`IF-preserves-β-false`](DPRLR/Gluing/LogicalRelations/Bool.agda) | 
| **Lemma 3.11 — Representable contravariant families** | $x\mapsto x\leq_X a$ | [`representable-isContravariant`](DPRLR/Simplicial/Contravariant.agda) |  |
| **Section 3.4.1 — Canonicity via the fundamental theorem** | gluing model $\mathcal G$ | [`GluingCwF`](DPRLR/Gluing/GluingModel.agda) |  |
|  | section $\iota:\mathcal I\to\mathcal G$ | [`ftlr-section`](DPRLR/Gluing/FTLR.agda) |  |
|  | $\sum_{b:\{0,1\}}M\leq\ulcorner b\urcorner$ | [`bool-canonicityᴾ`](DPRLR/Gluing/FTLR.agda) |  |
| **Definition 4.1 — Discrete types** | $\mathrm{isDiscrete}(X)$ | [`isDiscrete`](DPRLR/Simplicial/Discrete.agda) |  |
|  | inverse to $x=_X y\to x\leq_X y$ | [`hom→path`](DPRLR/Simplicial/Discrete.agda) |  |
| **Axiom 4.3 — Boolean discreteness** | $\mathrm{isDiscrete}(\{0,1\})$ | [`Bool₂-isDiscrete`](DPRLR/Simplicial/Discrete.agda) |  |
| **Lemma 5.1 — Binary contravariance** | $\mathrm{isContrav}(R)$ implies contravariance of both slices | [`binary-contravariance`](DPRLR/Simplicial/BinaryContravariant.agda) | Only the forward implication is mechanized: contravariance of the binary family implies contravariance of both slices. The converse requires additional simplicial infrastructure. |

## Axioms

1. **Directed interval (Definition 2.1).** [`Interval.agda`](DPRLR/Simplicial/Interval.agda) postulates the set 𝟚, its
   endpoints `𝟎` and `𝟏`, and a proposition-valued order `_≤₂_` satisfying reflexivity, transitivity, antisymmetry,
   totality, and the endpoint bounds. These postulates supply the additional directed interval structure assumed by the
   paper's simplicial setting, as is typical in extending HoTT to simplicial settings.

2. **Boolean discreteness (Axiom 4.3).** [`Bool₂-isDiscrete`](DPRLR/Simplicial/Discrete.agda) postulates that the
   meta-language Booleans are discrete. This is a standard axiom in simplical type theory. See paper for literature
   references on this axiom.
