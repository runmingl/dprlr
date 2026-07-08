module DPRLR.Gluing.Simple.Product where

open import Cubical.Foundations.Prelude hiding (Sub ; _▷_ ; fst ; snd)
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Contravariant
open import DPRLR.Simplicial.ProductExtensionality
open import DPRLR.Object.Simple.Model
open import DPRLR.Gluing.Simple.Judgment
open import DPRLR.Gluing.Simple.Substitution

module _ {ℓM : Level} (𝓜 : SimpleDirectedCwF ℓM) where

  open SimpleDirectedCwF 𝓜
    renaming
      ( Ctx to Ctxₘ
      ; Ty to Tyₘ
      ; Sub to Subₘ
      ; Tm to Tmₘ
      ; ε to εₘ
      ; _∘_ to _∘ₘ_
      ; _[_]Tm to _[_]Tmₘ
      ; Tm-∘ to Tm-∘ₘ
      ; _×ᵗʸ_ to _×ₘ_
      ; pair to pairₘ
      ; fst to fstₘ
      ; snd to sndₘ
      ; pair[] to pair[]ₘ
      ; fst[] to fst[]ₘ
      ; snd[] to snd[]ₘ
      ; β×₁ to β×₁ₘ
      ; β×₂ to β×₂ₘ
      ; η× to η×ₘ
      ; tm-set to tm-setₘ
      ; tm-thin to tm-thinₘ
      )

  PROD∙ :
    (A B : GluTy 𝓜)
    → Tmₘ εₘ (GluTy.A° A ×ₘ GluTy.A° B)
    → Type ℓM
  PROD∙ A B P =
    GluTy.A∙ A (fstₘ P)
    ×
    GluTy.A∙ B (sndₘ P)

  PROD-contravariant :
    (A B : GluTy 𝓜)
    → isContravariant (PROD∙ A B)
  PROD-contravariant A B =
    contravariant-×
      (contravariant-reindex fstₘ (GluTy.cA A))
      (contravariant-reindex sndₘ (GluTy.cA B))

  PROD :
    (A B : GluTy 𝓜)
    → GluTy 𝓜
  GluTy.A° (PROD A B) = GluTy.A° A ×ₘ GluTy.A° B
  GluTy.A∙ (PROD A B) = PROD∙ A B
  GluTy.cA (PROD A B) = PROD-contravariant A B

  PROD∙-subst-fst :
    (A B : GluTy 𝓜)
    {P Q : Tmₘ εₘ (GluTy.A° A ×ₘ GluTy.A° B)}
    (p : P ≡ Q)
    (P∙ : PROD∙ A B P)
    → fst (subst (PROD∙ A B) p P∙)
      ≡ subst (GluTy.A∙ A) (cong fstₘ p) (fst P∙)
  PROD∙-subst-fst A B {P = P} p =
    J
      (λ Q p →
        (P∙ : PROD∙ A B P)
        → fst (subst (PROD∙ A B) p P∙)
          ≡ subst (GluTy.A∙ A) (cong fstₘ p) (fst P∙))
      base
      p
    where
    base :
      (P∙ : PROD∙ A B P)
      → fst (subst (PROD∙ A B) refl P∙)
        ≡ subst (GluTy.A∙ A) (cong fstₘ refl) (fst P∙)
    base P∙ =
      cong fst (substRefl {B = PROD∙ A B} P∙)
      ∙ sym (substRefl {B = GluTy.A∙ A} (fst P∙))

  PROD∙-subst-snd :
    (A B : GluTy 𝓜)
    {P Q : Tmₘ εₘ (GluTy.A° A ×ₘ GluTy.A° B)}
    (p : P ≡ Q)
    (P∙ : PROD∙ A B P)
    → snd (subst (PROD∙ A B) p P∙)
      ≡ subst (GluTy.A∙ B) (cong sndₘ p) (snd P∙)
  PROD∙-subst-snd A B {P = P} p =
    J
      (λ Q p →
        (P∙ : PROD∙ A B P)
        → snd (subst (PROD∙ A B) p P∙)
          ≡ subst (GluTy.A∙ B) (cong sndₘ p) (snd P∙))
      base
      p
    where
    base :
      (P∙ : PROD∙ A B P)
      → snd (subst (PROD∙ A B) refl P∙)
        ≡ subst (GluTy.A∙ B) (cong sndₘ refl) (snd P∙)
    base P∙ =
      cong snd (substRefl {B = PROD∙ A B} P∙)
      ∙ sym (substRefl {B = GluTy.A∙ B} (snd P∙))

  pair-fst-hom :
    {Γ : GluCtx 𝓜}
    (A B : GluTy 𝓜)
    (M : GluTm 𝓜 Γ A)
    (N : GluTm 𝓜 Γ B)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    → fstₘ (pairₘ (GluTm.M° M) (GluTm.M° N) [ γ° ]Tmₘ)
      ≤ (GluTm.M° M [ γ° ]Tmₘ)
  pair-fst-hom A B M N γ° =
    subst
      (λ t → t ≤ (GluTm.M° M [ γ° ]Tmₘ))
      (fst[]ₘ (pairₘ (GluTm.M° M) (GluTm.M° N)) γ°)
      (hom-map (λ t → t [ γ° ]Tmₘ)
        (β×₁ₘ (GluTm.M° M) (GluTm.M° N)))

  pair-snd-hom :
    {Γ : GluCtx 𝓜}
    (A B : GluTy 𝓜)
    (M : GluTm 𝓜 Γ A)
    (N : GluTm 𝓜 Γ B)
    (γ° : Subₘ εₘ (GluCtx.Γ° Γ))
    → sndₘ (pairₘ (GluTm.M° M) (GluTm.M° N) [ γ° ]Tmₘ)
      ≤ (GluTm.M° N [ γ° ]Tmₘ)
  pair-snd-hom A B M N γ° =
    subst
      (λ t → t ≤ (GluTm.M° N [ γ° ]Tmₘ))
      (snd[]ₘ (pairₘ (GluTm.M° M) (GluTm.M° N)) γ°)
      (hom-map (λ t → t [ γ° ]Tmₘ)
        (β×₂ₘ (GluTm.M° M) (GluTm.M° N)))

  PAIR :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    → GluTm 𝓜 Γ A
    → GluTm 𝓜 Γ B
    → GluTm 𝓜 Γ (PROD A B)
  GluTm.M° (PAIR M N) = pairₘ (GluTm.M° M) (GluTm.M° N)
  GluTm.M∙ (PAIR {A = A} {B = B} M N) γ° γ∙ =
    contrav-transport
      (GluTy.cA A)
      (pair-fst-hom A B M N γ°)
      (GluTm.M∙ M γ° γ∙)
    ,
    contrav-transport
      (GluTy.cA B)
      (pair-snd-hom A B M N γ°)
      (GluTm.M∙ N γ° γ∙)

  PAIR[] :
    {Γ Δ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (M : GluTm 𝓜 Δ A)
    (N : GluTm 𝓜 Δ B)
    (σ : GluSub 𝓜 Γ Δ)
    → _[_]Tmᵍ 𝓜 (PAIR {A = A} {B = B} M N) σ
      ≡ PAIR {A = A} {B = B}
          (_[_]Tmᵍ 𝓜 M σ)
          (_[_]Tmᵍ 𝓜 N σ)
  GluTm.M° (PAIR[] M N σ i) =
    pair[]ₘ (GluTm.M° M) (GluTm.M° N) (GluSub.σ° σ) i
  GluTm.M∙ (PAIR[] {Γ = Γ} {Δ = Δ} {A = A} {B = B} M N σ i) γ° γ∙ =
    path i
    where
    M₀ = GluTm.M° M
    N₀ = GluTm.M° N
    σ₀ = GluSub.σ° σ

    σγ =
      σ₀ ∘ₘ γ°

    M∙σγ =
      GluTm.M∙ M σγ (GluSub.σ∙ σ γ° γ∙)

    N∙σγ =
      GluTm.M∙ N σγ (GluSub.σ∙ σ γ° γ∙)

    compPair :
      (pairₘ M₀ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ pairₘ M₀ N₀ [ σγ ]Tmₘ
    compPair =
      Tm-∘ₘ (pairₘ M₀ N₀) σ₀ γ°

    pairσγ :
      pairₘ M₀ N₀ [ σγ ]Tmₘ
      ≡ pairₘ (M₀ [ σγ ]Tmₘ) (N₀ [ σγ ]Tmₘ)
    pairσγ =
      pair[]ₘ M₀ N₀ σγ

    compM :
      (M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ M₀ [ σγ ]Tmₘ
    compM =
      Tm-∘ₘ M₀ σ₀ γ°

    compN :
      (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ N₀ [ σγ ]Tmₘ
    compN =
      Tm-∘ₘ N₀ σ₀ γ°

    M-path :
      M₀ [ σγ ]Tmₘ ≡ (M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    M-path =
      sym compM

    N-path :
      N₀ [ σγ ]Tmₘ ≡ (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    N-path =
      sym compN

    pair-components :
      pairₘ (M₀ [ σγ ]Tmₘ) (N₀ [ σγ ]Tmₘ)
      ≡ pairₘ ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
          ((N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    pair-components i =
      pairₘ (M-path i) (N-path i)

    pairTarget :
      pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ pairₘ ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
          ((N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    pairTarget =
      pair[]ₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) γ°

    rest-path :
      pairₘ M₀ N₀ [ σγ ]Tmₘ
      ≡ pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    rest-path =
      (pairσγ ∙ pair-components) ∙ sym pairTarget

    source-fst :
      fstₘ (pairₘ M₀ N₀ [ σγ ]Tmₘ)
      ≤ M₀ [ σγ ]Tmₘ
    source-fst =
      pair-fst-hom A B M N σγ

    source-snd :
      sndₘ (pairₘ M₀ N₀ [ σγ ]Tmₘ)
      ≤ N₀ [ σγ ]Tmₘ
    source-snd =
      pair-snd-hom A B M N σγ

    target-fst :
      fstₘ (pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
      ≤ (M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    target-fst =
      pair-fst-hom A B
        (_[_]Tmᵍ 𝓜 M σ)
        (_[_]Tmᵍ 𝓜 N σ)
        γ°

    target-snd :
      sndₘ (pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
      ≤ (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    target-snd =
      pair-snd-hom A B
        (_[_]Tmᵍ 𝓜 M σ)
        (_[_]Tmᵍ 𝓜 N σ)
        γ°

    middle :
      PROD∙ A B (pairₘ M₀ N₀ [ σγ ]Tmₘ)
    middle =
      contrav-transport (GluTy.cA A) source-fst M∙σγ
      ,
      contrav-transport (GluTy.cA B) source-snd N∙σγ

    actual :
      PROD∙ A B ((pairₘ M₀ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    actual =
      subst (PROD∙ A B) (sym compPair) middle

    M∙target :
      GluTy.A∙ A ((M₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    M∙target =
      subst (GluTy.A∙ A) M-path M∙σγ

    N∙target :
      GluTy.A∙ B ((N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    N∙target =
      subst (GluTy.A∙ B) N-path N∙σγ

    target :
      PROD∙ A B
        (pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    target =
      contrav-transport (GluTy.cA A) target-fst M∙target
      ,
      contrav-transport (GluTy.cA B) target-snd N∙target

    step₁ :
      PathP
        (λ i → PROD∙ A B (compPair i))
        actual
        middle
    step₁ i =
      subst-filler
        (PROD∙ A B)
        (sym compPair)
        middle
        (~ i)

    fst-hom-eq :
      subst
        (λ t →
          fstₘ (pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) ≤ t)
        (sym M-path)
        target-fst
      ≡ subst
          (λ s → s ≤ M₀ [ σγ ]Tmₘ)
          (cong fstₘ rest-path)
          source-fst
    fst-hom-eq =
      tm-thinₘ εₘ (GluTy.A° A)
        (fstₘ (pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ))
        (M₀ [ σγ ]Tmₘ)
        (subst
          (λ t →
            fstₘ (pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) ≤ t)
          (sym M-path)
          target-fst)
        (subst
          (λ s → s ≤ M₀ [ σγ ]Tmₘ)
          (cong fstₘ rest-path)
          source-fst)

    snd-hom-eq :
      subst
        (λ t →
          sndₘ (pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) ≤ t)
        (sym N-path)
        target-snd
      ≡ subst
          (λ s → s ≤ N₀ [ σγ ]Tmₘ)
          (cong sndₘ rest-path)
          source-snd
    snd-hom-eq =
      tm-thinₘ εₘ (GluTy.A° B)
        (sndₘ (pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ))
        (N₀ [ σγ ]Tmₘ)
        (subst
          (λ t →
            sndₘ (pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ) ≤ t)
          (sym N-path)
          target-snd)
        (subst
          (λ s → s ≤ N₀ [ σγ ]Tmₘ)
          (cong sndₘ rest-path)
          source-snd)

    step₂-fst :
      PathP
        (λ i → GluTy.A∙ A (fstₘ (rest-path i)))
        (fst middle)
        (fst target)
    step₂-fst =
      contravariant-transport-pathP
        (GluTy.cA A)
        (cong fstₘ rest-path)
        M-path
        source-fst
        target-fst
        M∙σγ
        fst-hom-eq

    step₂-snd :
      PathP
        (λ i → GluTy.A∙ B (sndₘ (rest-path i)))
        (snd middle)
        (snd target)
    step₂-snd =
      contravariant-transport-pathP
        (GluTy.cA B)
        (cong sndₘ rest-path)
        N-path
        source-snd
        target-snd
        N∙σγ
        snd-hom-eq

    step₂ :
      PathP
        (λ i → PROD∙ A B (rest-path i))
        middle
        target
    step₂ =
      ΣPathP (step₂-fst , step₂-snd)

    Q :
      (pairₘ M₀ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    Q =
      compPair ∙ rest-path

    R :
      (pairₘ M₀ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    R i =
      pair[]ₘ M₀ N₀ σ₀ i [ γ° ]Tmₘ

    Q≡R :
      Q ≡ R
    Q≡R =
      tm-setₘ εₘ (GluTy.A° A ×ₘ GluTy.A° B)
        ((pairₘ M₀ N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        (pairₘ (M₀ [ σ₀ ]Tmₘ) (N₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        Q
        R

    path-Q :
      PathP
        (λ i → PROD∙ A B (Q i))
        actual
        target
    path-Q =
      compPathP' {B = PROD∙ A B} step₁ step₂

    path :
      PathP
        (λ i → PROD∙ A B (R i))
        actual
        target
    path =
      subst
        (λ q →
          PathP
            (λ i → PROD∙ A B (q i))
            actual
            target)
        Q≡R
        path-Q

  FST :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    → GluTm 𝓜 Γ (PROD A B)
    → GluTm 𝓜 Γ A
  GluTm.M° (FST M) = fstₘ (GluTm.M° M)
  GluTm.M∙ (FST {A = A} M) γ° γ∙ =
    subst
      (GluTy.A∙ A)
      (sym (fst[]ₘ (GluTm.M° M) γ°))
      (fst (GluTm.M∙ M γ° γ∙))

  SND :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    → GluTm 𝓜 Γ (PROD A B)
    → GluTm 𝓜 Γ B
  GluTm.M° (SND M) = sndₘ (GluTm.M° M)
  GluTm.M∙ (SND {B = B} M) γ° γ∙ =
    subst
      (GluTy.A∙ B)
      (sym (snd[]ₘ (GluTm.M° M) γ°))
      (snd (GluTm.M∙ M γ° γ∙))

  FST[] :
    {Γ Δ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (P : GluTm 𝓜 Δ (PROD A B))
    (σ : GluSub 𝓜 Γ Δ)
    → _[_]Tmᵍ 𝓜 (FST {A = A} {B = B} P) σ
      ≡ FST {A = A} {B = B} (_[_]Tmᵍ 𝓜 P σ)
  GluTm.M° (FST[] P σ i) =
    fst[]ₘ (GluTm.M° P) (GluSub.σ° σ) i
  GluTm.M∙ (FST[] {Γ = Γ} {Δ = Δ} {A = A} {B = B} P σ i) γ° γ∙ =
    path i
    where
    P₀ = GluTm.M° P
    σ₀ = GluSub.σ° σ

    σγ =
      σ₀ ∘ₘ γ°

    P∙σγ =
      GluTm.M∙ P σγ (GluSub.σ∙ σ γ° γ∙)

    compP :
      (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ P₀ [ σγ ]Tmₘ
    compP =
      Tm-∘ₘ P₀ σ₀ γ°

    compFst :
      (fstₘ P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ fstₘ P₀ [ σγ ]Tmₘ
    compFst =
      Tm-∘ₘ (fstₘ P₀) σ₀ γ°

    fstσγ :
      fstₘ P₀ [ σγ ]Tmₘ ≡ fstₘ (P₀ [ σγ ]Tmₘ)
    fstσγ =
      fst[]ₘ P₀ σγ

    fstPσγ :
      fstₘ (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ fstₘ ((P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    fstPσγ =
      fst[]ₘ (P₀ [ σ₀ ]Tmₘ) γ°

    compP-fst :
      fstₘ (P₀ [ σγ ]Tmₘ)
      ≡ fstₘ ((P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    compP-fst =
      cong fstₘ (sym compP)

    middle :
      GluTy.A∙ A (fstₘ P₀ [ σγ ]Tmₘ)
    middle =
      subst (GluTy.A∙ A) (sym fstσγ) (fst P∙σγ)

    actual :
      GluTy.A∙ A ((fstₘ P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    actual =
      subst (GluTy.A∙ A) (sym compFst) middle

    right-middle :
      GluTy.A∙ A (fstₘ ((P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ))
    right-middle =
      subst (GluTy.A∙ A) compP-fst (fst P∙σγ)

    subst-fst :
      fst
        (subst
          (PROD∙ A B)
          (sym compP)
          P∙σγ)
      ≡ right-middle
    subst-fst =
      PROD∙-subst-fst A B (sym compP) P∙σγ

    target :
      GluTy.A∙ A (fstₘ (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    target =
      subst (GluTy.A∙ A)
        (sym fstPσγ)
        (fst
          (subst
            (PROD∙ A B)
            (sym compP)
            P∙σγ))

    step₁ :
      PathP
        (λ i → GluTy.A∙ A (compFst i))
        actual
        middle
    step₁ i =
      subst-filler
        (GluTy.A∙ A)
        (sym compFst)
        middle
        (~ i)

    step₂ :
      PathP
        (λ i → GluTy.A∙ A (fstσγ i))
        middle
        (fst P∙σγ)
    step₂ i =
      subst-filler
        (GluTy.A∙ A)
        (sym fstσγ)
        (fst P∙σγ)
        (~ i)

    step₁₂ :
      PathP
        (λ i → GluTy.A∙ A ((compFst ∙ fstσγ) i))
        actual
        (fst P∙σγ)
    step₁₂ =
      compPathP' {B = GluTy.A∙ A} step₁ step₂

    step₃ :
      PathP
        (λ i → GluTy.A∙ A (compP-fst i))
        (fst P∙σγ)
        right-middle
    step₃ =
      subst-filler (GluTy.A∙ A) compP-fst (fst P∙σγ)

    step₁₂₃ :
      PathP
        (λ i → GluTy.A∙ A (((compFst ∙ fstσγ) ∙ compP-fst) i))
        actual
        right-middle
    step₁₂₃ =
      compPathP' {B = GluTy.A∙ A} step₁₂ step₃

    step₄-base :
      PathP
        (λ i → GluTy.A∙ A (sym fstPσγ i))
        right-middle
        (subst (GluTy.A∙ A) (sym fstPσγ) right-middle)
    step₄-base =
      subst-filler (GluTy.A∙ A) (sym fstPσγ) right-middle

    step₄ :
      PathP
        (λ i → GluTy.A∙ A (sym fstPσγ i))
        right-middle
        target
    step₄ =
      subst
        (λ u →
          PathP
            (λ i → GluTy.A∙ A (sym fstPσγ i))
            right-middle
            u)
        (cong (subst (GluTy.A∙ A) (sym fstPσγ)) (sym subst-fst))
        step₄-base

    Q :
      (fstₘ P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ fstₘ (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    Q =
      (((compFst ∙ fstσγ) ∙ compP-fst) ∙ sym fstPσγ)

    R :
      (fstₘ P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ fstₘ (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    R i =
      fst[]ₘ P₀ σ₀ i [ γ° ]Tmₘ

    Q≡R :
      Q ≡ R
    Q≡R =
      tm-setₘ εₘ (GluTy.A° A)
        ((fstₘ P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        (fstₘ (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        Q
        R

    path-Q :
      PathP
        (λ i → GluTy.A∙ A (Q i))
        actual
        target
    path-Q =
      compPathP' {B = GluTy.A∙ A} step₁₂₃ step₄

    path :
      PathP
        (λ i → GluTy.A∙ A (R i))
        actual
        target
    path =
      subst
        (λ q →
          PathP
            (λ i → GluTy.A∙ A (q i))
            actual
            target)
        Q≡R
        path-Q

  SND[] :
    {Γ Δ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (P : GluTm 𝓜 Δ (PROD A B))
    (σ : GluSub 𝓜 Γ Δ)
    → _[_]Tmᵍ 𝓜 (SND {A = A} {B = B} P) σ
      ≡ SND {A = A} {B = B} (_[_]Tmᵍ 𝓜 P σ)
  GluTm.M° (SND[] P σ i) =
    snd[]ₘ (GluTm.M° P) (GluSub.σ° σ) i
  GluTm.M∙ (SND[] {Γ = Γ} {Δ = Δ} {A = A} {B = B} P σ i) γ° γ∙ =
    path i
    where
    P₀ = GluTm.M° P
    σ₀ = GluSub.σ° σ

    σγ =
      σ₀ ∘ₘ γ°

    P∙σγ =
      GluTm.M∙ P σγ (GluSub.σ∙ σ γ° γ∙)

    compP :
      (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ P₀ [ σγ ]Tmₘ
    compP =
      Tm-∘ₘ P₀ σ₀ γ°

    compSnd :
      (sndₘ P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ ≡ sndₘ P₀ [ σγ ]Tmₘ
    compSnd =
      Tm-∘ₘ (sndₘ P₀) σ₀ γ°

    sndσγ :
      sndₘ P₀ [ σγ ]Tmₘ ≡ sndₘ (P₀ [ σγ ]Tmₘ)
    sndσγ =
      snd[]ₘ P₀ σγ

    sndPσγ :
      sndₘ (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ sndₘ ((P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    sndPσγ =
      snd[]ₘ (P₀ [ σ₀ ]Tmₘ) γ°

    compP-snd :
      sndₘ (P₀ [ σγ ]Tmₘ)
      ≡ sndₘ ((P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    compP-snd =
      cong sndₘ (sym compP)

    middle :
      GluTy.A∙ B (sndₘ P₀ [ σγ ]Tmₘ)
    middle =
      subst (GluTy.A∙ B) (sym sndσγ) (snd P∙σγ)

    actual :
      GluTy.A∙ B ((sndₘ P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    actual =
      subst (GluTy.A∙ B) (sym compSnd) middle

    right-middle :
      GluTy.A∙ B (sndₘ ((P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ))
    right-middle =
      subst (GluTy.A∙ B) compP-snd (snd P∙σγ)

    subst-snd :
      snd
        (subst
          (PROD∙ A B)
          (sym compP)
          P∙σγ)
      ≡ right-middle
    subst-snd =
      PROD∙-subst-snd A B (sym compP) P∙σγ

    target :
      GluTy.A∙ B (sndₘ (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
    target =
      subst (GluTy.A∙ B)
        (sym sndPσγ)
        (snd
          (subst
            (PROD∙ A B)
            (sym compP)
            P∙σγ))

    step₁ :
      PathP
        (λ i → GluTy.A∙ B (compSnd i))
        actual
        middle
    step₁ i =
      subst-filler
        (GluTy.A∙ B)
        (sym compSnd)
        middle
        (~ i)

    step₂ :
      PathP
        (λ i → GluTy.A∙ B (sndσγ i))
        middle
        (snd P∙σγ)
    step₂ i =
      subst-filler
        (GluTy.A∙ B)
        (sym sndσγ)
        (snd P∙σγ)
        (~ i)

    step₁₂ :
      PathP
        (λ i → GluTy.A∙ B ((compSnd ∙ sndσγ) i))
        actual
        (snd P∙σγ)
    step₁₂ =
      compPathP' {B = GluTy.A∙ B} step₁ step₂

    step₃ :
      PathP
        (λ i → GluTy.A∙ B (compP-snd i))
        (snd P∙σγ)
        right-middle
    step₃ =
      subst-filler (GluTy.A∙ B) compP-snd (snd P∙σγ)

    step₁₂₃ :
      PathP
        (λ i → GluTy.A∙ B (((compSnd ∙ sndσγ) ∙ compP-snd) i))
        actual
        right-middle
    step₁₂₃ =
      compPathP' {B = GluTy.A∙ B} step₁₂ step₃

    step₄-base :
      PathP
        (λ i → GluTy.A∙ B (sym sndPσγ i))
        right-middle
        (subst (GluTy.A∙ B) (sym sndPσγ) right-middle)
    step₄-base =
      subst-filler (GluTy.A∙ B) (sym sndPσγ) right-middle

    step₄ :
      PathP
        (λ i → GluTy.A∙ B (sym sndPσγ i))
        right-middle
        target
    step₄ =
      subst
        (λ u →
          PathP
            (λ i → GluTy.A∙ B (sym sndPσγ i))
            right-middle
            u)
        (cong (subst (GluTy.A∙ B) (sym sndPσγ)) (sym subst-snd))
        step₄-base

    Q :
      (sndₘ P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ sndₘ (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    Q =
      (((compSnd ∙ sndσγ) ∙ compP-snd) ∙ sym sndPσγ)

    R :
      (sndₘ P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
      ≡ sndₘ (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ
    R i =
      snd[]ₘ P₀ σ₀ i [ γ° ]Tmₘ

    Q≡R :
      Q ≡ R
    Q≡R =
      tm-setₘ εₘ (GluTy.A° B)
        ((sndₘ P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        (sndₘ (P₀ [ σ₀ ]Tmₘ) [ γ° ]Tmₘ)
        Q
        R

    path-Q :
      PathP
        (λ i → GluTy.A∙ B (Q i))
        actual
        target
    path-Q =
      compPathP' {B = GluTy.A∙ B} step₁₂₃ step₄

    path :
      PathP
        (λ i → GluTy.A∙ B (R i))
        actual
        target
    path =
      subst
        (λ q →
          PathP
            (λ i → GluTy.A∙ B (q i))
            actual
            target)
        Q≡R
        path-Q

  private
    PROD-preserves-β₁-data :
      {Γ : GluCtx 𝓜}
      {A B : GluTy 𝓜}
      (M : GluTm 𝓜 Γ A)
      (N : GluTm 𝓜 Γ B)
      → _≤ᵍ_ 𝓜 {Γ = Γ} {A = A}
          (FST {A = A} {B = B} (PAIR {A = A} {B = B} M N)) M
    _≤ᵍ_.r° (PROD-preserves-β₁-data M N) =
      β×₁ₘ (GluTm.M° M) (GluTm.M° N)
    _≤ᵍ_.r∙ (PROD-preserves-β₁-data {A = A} {B = B} M N) γ° γ∙ =
      contravariant-universal-from
        (GluTy.cA A)
        (contravariant-transport-source-subst
          (GluTy.cA A)
          (sym (fst[]ₘ (pairₘ (GluTm.M° M) (GluTm.M° N)) γ°))
          (hom-map (λ t → t [ γ° ]Tmₘ)
            (β×₁ₘ (GluTm.M° M) (GluTm.M° N)))
          (GluTm.M∙ M γ° γ∙))

    PROD-preserves-β₂-data :
      {Γ : GluCtx 𝓜}
      {A B : GluTy 𝓜}
      (M : GluTm 𝓜 Γ A)
      (N : GluTm 𝓜 Γ B)
      → _≤ᵍ_ 𝓜 {Γ = Γ} {A = B}
          (SND {A = A} {B = B} (PAIR {A = A} {B = B} M N)) N
    _≤ᵍ_.r° (PROD-preserves-β₂-data M N) =
      β×₂ₘ (GluTm.M° M) (GluTm.M° N)
    _≤ᵍ_.r∙ (PROD-preserves-β₂-data {A = A} {B = B} M N) γ° γ∙ =
      contravariant-universal-from
        (GluTy.cA B)
        (contravariant-transport-source-subst
          (GluTy.cA B)
          (sym (snd[]ₘ (pairₘ (GluTm.M° M) (GluTm.M° N)) γ°))
          (hom-map (λ t → t [ γ° ]Tmₘ)
            (β×₂ₘ (GluTm.M° M) (GluTm.M° N)))
          (GluTm.M∙ N γ° γ∙))

    PROD-preserves-η-data :
      {Γ : GluCtx 𝓜}
      {A B : GluTy 𝓜}
      (P : GluTm 𝓜 Γ (PROD A B))
      → _≤ᵍ_ 𝓜 {Γ = Γ} {A = PROD A B}
          (PAIR {A = A} {B = B}
            (FST {A = A} {B = B} P)
            (SND {A = A} {B = B} P))
          P
    _≤ᵍ_.r° (PROD-preserves-η-data P) =
      η×ₘ (GluTm.M° P)
    _≤ᵍ_.r∙ (PROD-preserves-η-data {A = A} {B = B} P) γ° γ∙ =
      HomP×
        {C = λ Q → GluTy.A∙ A (fstₘ Q)}
        {D = λ Q → GluTy.A∙ B (sndₘ Q)}
        {x = pairₘ (fstₘ (GluTm.M° P)) (sndₘ (GluTm.M° P)) [ γ° ]Tmₘ}
        {y = GluTm.M° P [ γ° ]Tmₘ}
        {f = ηγ}
        {uC = fst PairP∙γ}
        {vC = fst P∙γ}
        {uD = snd PairP∙γ}
        {vD = snd P∙γ}
        (contravariant-universal-from
          (contravariant-reindex fstₘ (GluTy.cA A))
          first-eq)
        (contravariant-universal-from
          (contravariant-reindex sndₘ (GluTy.cA B))
          second-eq)
      where
      P∙γ = GluTm.M∙ P γ° γ∙
      PairP =
        PAIR {A = A} {B = B}
          (FST {A = A} {B = B} P)
          (SND {A = A} {B = B} P)
      PairP∙γ = GluTm.M∙ PairP γ° γ∙

      ηγ :
        (pairₘ (fstₘ (GluTm.M° P)) (sndₘ (GluTm.M° P)) [ γ° ]Tmₘ)
        ≤ (GluTm.M° P [ γ° ]Tmₘ)
      ηγ =
        hom-map (λ t → t [ γ° ]Tmₘ) (η×ₘ (GluTm.M° P))

      first-source =
        fstₘ
          (pairₘ (fstₘ (GluTm.M° P)) (sndₘ (GluTm.M° P)) [ γ° ]Tmₘ)

      first-β :
        first-source ≤ (fstₘ (GluTm.M° P) [ γ° ]Tmₘ)
      first-β =
        pair-fst-hom A B
          (FST {A = A} {B = B} P)
          (SND {A = A} {B = B} P)
          γ°

      first-β-to-η :
        first-source ≤ fstₘ (GluTm.M° P [ γ° ]Tmₘ)
      first-β-to-η =
        subst
          (λ t → first-source ≤ t)
          (fst[]ₘ (GluTm.M° P) γ°)
          first-β

      first-η :
        first-source ≤ fstₘ (GluTm.M° P [ γ° ]Tmₘ)
      first-η =
        hom-map fstₘ ηγ

      first-eq :
        fst PairP∙γ
        ≡
        contrav-transport
          (contravariant-reindex fstₘ (GluTy.cA A))
          ηγ
          (fst P∙γ)
      first-eq =
        contravariant-transport-target-subst
          (GluTy.cA A)
          (sym (fst[]ₘ (GluTm.M° P) γ°))
          first-β
          (fst P∙γ)
        ∙ cong
            (λ h → contrav-transport (GluTy.cA A) h (fst P∙γ))
            (tm-thinₘ εₘ (GluTy.A° A)
              first-source
              (fstₘ (GluTm.M° P [ γ° ]Tmₘ))
              first-β-to-η
              first-η)

      second-source =
        sndₘ
          (pairₘ (fstₘ (GluTm.M° P)) (sndₘ (GluTm.M° P)) [ γ° ]Tmₘ)

      second-β :
        second-source ≤ (sndₘ (GluTm.M° P) [ γ° ]Tmₘ)
      second-β =
        pair-snd-hom A B
          (FST {A = A} {B = B} P)
          (SND {A = A} {B = B} P)
          γ°

      second-β-to-η :
        second-source ≤ sndₘ (GluTm.M° P [ γ° ]Tmₘ)
      second-β-to-η =
        subst
          (λ t → second-source ≤ t)
          (snd[]ₘ (GluTm.M° P) γ°)
          second-β

      second-η :
        second-source ≤ sndₘ (GluTm.M° P [ γ° ]Tmₘ)
      second-η =
        hom-map sndₘ ηγ

      second-eq :
        snd PairP∙γ
        ≡
        contrav-transport
          (contravariant-reindex sndₘ (GluTy.cA B))
          ηγ
          (snd P∙γ)
      second-eq =
        contravariant-transport-target-subst
          (GluTy.cA B)
          (sym (snd[]ₘ (GluTm.M° P) γ°))
          second-β
          (snd P∙γ)
        ∙ cong
            (λ h → contrav-transport (GluTy.cA B) h (snd P∙γ))
            (tm-thinₘ εₘ (GluTy.A° B)
              second-source
              (sndₘ (GluTm.M° P [ γ° ]Tmₘ))
              second-β-to-η
              second-η)

  PROD-preserves-β₁ :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (M : GluTm 𝓜 Γ A)
    (N : GluTm 𝓜 Γ B)
    → FST {A = A} {B = B} (PAIR {A = A} {B = B} M N) ≤ M
  PROD-preserves-β₁ M N =
    ≤ᵍ→≤ 𝓜 (PROD-preserves-β₁-data M N)

  PROD-preserves-β₂ :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (M : GluTm 𝓜 Γ A)
    (N : GluTm 𝓜 Γ B)
    → SND {A = A} {B = B} (PAIR {A = A} {B = B} M N) ≤ N
  PROD-preserves-β₂ M N =
    ≤ᵍ→≤ 𝓜 (PROD-preserves-β₂-data M N)

  PROD-preserves-η :
    {Γ : GluCtx 𝓜}
    {A B : GluTy 𝓜}
    (P : GluTm 𝓜 Γ (PROD A B))
    → PAIR {A = A} {B = B}
        (FST {A = A} {B = B} P)
        (SND {A = A} {B = B} P)
      ≤ P
  PROD-preserves-η {A = A} {B = B} P =
    ≤ᵍ→≤ 𝓜 (PROD-preserves-η-data {A = A} {B = B} P)
