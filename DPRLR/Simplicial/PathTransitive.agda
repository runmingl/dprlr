module DPRLR.Simplicial.PathTransitive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool using (Bool ; false ; true)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Unit
open import Cubical.Functions.Fibration as Fibration using ()
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Localization using (isLocal)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

open import DPRLR.Simplicial.Interval
open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Shapes
  using (Δ² ; Δ²-ext ; Λ² ; bottom₂ ; right₂ ; diagonal₂ ; ι-horn ; Λ²-elim)
open import DPRLR.Simplicial.Segal using (isSegal ; Composite)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type ℓ
    B X : Type ℓ'
    C Y : Type ℓ''
    D Z : Type ℓ'''

isPathTransitive : Type ℓ → Type ℓ
isPathTransitive = isLocal {A = Unit} (const ι-horn)

-- RS17, Theorem 5.5
module _ where
  Extension : (i : X → Y) (u : X → A) → Type _
  Extension i u = fiber (_∘ i) u -- Σ[ v ∈ (Y → A) ] (v ∘ i ≡ u)

  -- RS17, Theorem 4.4
  extension-composition : (i : X → Y) (j : Y → Z) (u : X → A)
    → (Σ[ v ∈ Extension i u ] Extension j (v .fst)) ≃ Extension (j ∘ i) u
  extension-composition {Y = Y} {Z = Z} {A = A} i j u =
      (Σ[ v ∈ Extension i u ] Extension j (v .fst))
    ≃⟨ isoToEquiv rearrange ⟩
      (Σ[ t ∈ (Z → A) ] Σ[ v ∈ singl (t ∘ j) ] (v .fst ∘ i ≡ u))
    ≃⟨ Σ-cong-equiv-snd (λ t → Σ-contractFst (isContrSingl (t ∘ j))) ⟩
      Extension (j ∘ i) u
    ■
    where
    rearrange : Iso (Σ[ v ∈ Extension i u ] Extension j (v .fst))
      (Σ[ t ∈ (Z → A) ] Σ[ v ∈ singl (t ∘ j) ] (v .fst ∘ i ≡ u))
    Iso.fun rearrange ((v , p) , t , q) = t , (v , q) , p
    Iso.inv rearrange (t , (v , q) , p) = (v , p) , t , q
    Iso.rightInv rearrange _ = refl
    Iso.leftInv rearrange _ = refl

  -- RS17, Theorem 4.5
  --   X ───── j ─────→ Z
  --   │                │
  -- i │                │ inr
  --   ↓                ↓
  --   Y ─── inl ───→ Pushout i j
  extension-pushout : (i : X → Y) (j : X → Z) (u : Y → A)
    → Extension (inl {f = i} {g = j}) u ≃ Extension j (u ∘ i)
  extension-pushout {Y = Y} {A = A} i j u =
      Extension (inl {f = i} {g = j}) u
    ≃⟨ Σ-cong-equiv-fst (isoToEquiv eliminate) ⟩
      fiber (fst {B = λ v → Extension j (v ∘ i)}) u
    ≃⟨ Fibration.fiberEquiv (λ v → Extension j (v ∘ i)) u ⟩
      Extension j (u ∘ i)
    ■
    where
    eliminate : Iso (Pushout i j → A) (Σ[ v ∈ (Y → A) ] Extension j (v ∘ i))
    Iso.fun eliminate t = (t ∘ inl) , (t ∘ inr) , (λ r x → t (push x (~ r)))
    Iso.inv eliminate (v , w , p) (inl y) = v y
    Iso.inv eliminate (v , w , p) (inr z) = w z
    Iso.inv eliminate (v , w , p) (push x r) = p (~ r) x
    Iso.rightInv eliminate _ = refl
    Iso.leftInv eliminate t r (inl y) = t (inl y)
    Iso.leftInv eliminate t r (inr z) = t (inr z)
    Iso.leftInv eliminate t r (push x s) = t (push x s)

  endpoint : Bool → 𝟚
  endpoint false = 𝟎
  endpoint true = 𝟏

  --                     • 𝟏
  --                     ↑
  --                     │
  --   𝟎 • ─────────────→ •
  horn-endpoint : Bool → Λ²
  horn-endpoint false = inl 𝟎
  horn-endpoint true = inr 𝟏

  --                     •
  --                   ↗ ↑
  --                 /   │
  --               /     │
  --             • ────→ •
  ∂Δ² : Type₀
  ∂Δ² = Pushout horn-endpoint endpoint

  boundary-inclusion : ∂Δ² → Δ²
  boundary-inclusion (inl k) = ι-horn k
  boundary-inclusion (inr s) = diagonal₂ s
  boundary-inclusion (push false r) = Δ²-ext {s = bottom₂ 𝟎} {t = diagonal₂ 𝟎} refl refl r
  boundary-inclusion (push true r) = Δ²-ext {s = right₂ 𝟏} {t = diagonal₂ 𝟏} refl refl r

  private
    -- RS17, Definition 5.1.
    hom≃extension : (k : Λ² → A)
      → Hom A (k (inl 𝟎)) (k (inr 𝟏)) ≃ Extension endpoint (k ∘ horn-endpoint)
    hom≃extension {A = A} k = isoToEquiv identify
      where
      identify : Iso (Hom A (k (inl 𝟎)) (k (inr 𝟏)))
        (Extension endpoint (k ∘ horn-endpoint))
      Iso.fun identify (h , p , q) = h , funExt λ { false → p ; true → q }
      Iso.inv identify (h , p) = h , (λ r → p r false) , (λ r → p r true)
      Iso.rightInv identify (h , p) r .fst = h
      Iso.rightInv identify (h , p) r .snd s false = p s false
      Iso.rightInv identify (h , p) r .snd s true = p s true
      Iso.leftInv identify _ = refl

  diagonal≃boundary-extension : (k : Λ² → A)
    → Hom A (k (inl 𝟎)) (k (inr 𝟏)) ≃ Extension (inl {f = horn-endpoint} {g = endpoint}) k
  diagonal≃boundary-extension {A = A} k =
      Hom A (k (inl 𝟎)) (k (inr 𝟏))
    ≃⟨ hom≃extension k ⟩
      Extension endpoint (k ∘ horn-endpoint)
    ≃⟨ invEquiv (extension-pushout horn-endpoint endpoint k) ⟩
      Extension (inl {f = horn-endpoint} {g = endpoint}) k
    ■

  --                     z
  --                   ↗ ↑
  --                h /  │ g
  --                 / α │
  --                x ──→ y
  --                   f
  -- RS17, Definition 5.2.
  Triangle : (k : Λ² → A) → Hom A (k (inl 𝟎)) (k (inr 𝟏)) → Type _
  Triangle k h = Extension boundary-inclusion (diagonal≃boundary-extension k .fst h .fst)

  -- RS17, Definition 5.3.
  CompositeRS : (k : Λ² → A) → Type _
  CompositeRS {A = A} k = Σ[ h ∈ Hom A (k (inl 𝟎)) (k (inr 𝟏)) ] Triangle k h

  compositeRS≃horn-extension : (k : Λ² → A) → CompositeRS k ≃ Extension ι-horn k
  compositeRS≃horn-extension {A = A} k =
      CompositeRS k
    ≃⟨ Σ-cong-equiv-fst (diagonal≃boundary-extension k) ⟩
      (Σ[ b ∈ Extension (inl {f = horn-endpoint} {g = endpoint}) k ]
        Extension boundary-inclusion (b .fst))
    ≃⟨ extension-composition inl boundary-inclusion k ⟩
      Extension ι-horn k
    ■

  isSegalRS : Type ℓ → Type ℓ
  isSegalRS A = (k : Λ² → A) → isContr (CompositeRS k)

  segalRS→restrictionEquiv : isSegalRS A → isEquiv (λ (t : Δ² → A) → t ∘ ι-horn)
  segalRS→restrictionEquiv S .equiv-proof k =
    isOfHLevelRespectEquiv 0 (compositeRS≃horn-extension k) (S k)

  restrictionEquiv→segalRS : isEquiv (λ (t : Δ² → A) → t ∘ ι-horn) → isSegalRS A
  restrictionEquiv→segalRS e k =
    isOfHLevelRespectEquiv 0 (invEquiv (compositeRS≃horn-extension k)) (e .equiv-proof k)

  -- RS17, Theorem 5.5.
  isSegalRS≡isPathTransitive : isSegalRS A ≡ isPathTransitive A
  isSegalRS≡isPathTransitive = hPropExt (isPropΠ λ _ → isPropIsContr)
    (isPropΠ λ _ → isPropIsPathSplitEquiv _)
    (λ S _ → fromIsEquiv _ (segalRS→restrictionEquiv S))
    (λ P → restrictionEquiv→segalRS (toIsEquiv _ (P tt)))

-- This is effectively the proof content of RS17, Proposition 8.13 but 
-- phrased in a different theorem due to our choice of isSegal definition.
-- We chose the square based isSegal definition as opposed to RS17's triangle based
-- which makes our version of proposition 8.13 essentially trivial. But 
-- the proof content shifted to the proof here that our definition and their
-- definition coincide.
module _ where
  private
    fiber-square : {f : A → B} {g : C → D}
      (e : A ≃ C) (d : B ≃ D) → d .fst ∘ f ≡ g ∘ e .fst
      → (b : B) → fiber f b ≃ fiber g (d .fst b)
    fiber-square {f = f} {g = g} e d commutes b = compEquiv
      (Σ-cong-equiv-snd λ a → compEquiv (congEquiv d)
        (pathToEquiv (λ i → commutes i a ≡ d .fst b)))
      (Σ-cong-equiv-fst e)

    --   Pullback P Q A ─────────────────→ (Q → A)
    --         │                              │
    --         │                              │ _∘ snd
    --         ↓                              ↓
    --      (P → A) ─────── _∘ fst ─────→ (P × Q → A)
    Pullback : (P : Type ℓ') (Q : Type ℓ'') → Type ℓ → Type _
    Pullback P Q A = Σ[ f ∈ (P → A) ] Σ[ g ∈ (Q → A) ] ((p : P) (q : Q) → f p ≡ g q)

    pullback-diagonal : {P : Type ℓ'} {Q : Type ℓ''} → A → Pullback P Q A
    pullback-diagonal a = (λ _ → a) , (λ _ → a) , (λ _ _ → refl)

    pullback-diagonal-equiv-left : {P : Type ℓ'} {Q : Type ℓ''}
      → isContr P → isEquiv (pullback-diagonal {A = A} {P = P} {Q = Q})
    pullback-diagonal-equiv-left {A = A} {P = P} {Q = Q} c =
      isEquiv[equivFunA≃B∘f]→isEquiv[f] pullback-diagonal (fst , projection) constant
      where
      constant : isEquiv (λ (a : A) (_ : P) → a)
      constant = isoToIsEquiv constant-iso
        where
        constant-iso : Iso A (P → A)
        Iso.fun constant-iso a _ = a
        Iso.inv constant-iso f = f (c .fst)
        Iso.rightInv constant-iso f i p = f (c .snd p i)
        Iso.leftInv constant-iso _ = refl
        
      projection : isEquiv (fst {B = λ f → Σ[ g ∈ (Q → A) ] ((p : P) (q : Q) → f p ≡ g q)})
      projection = Σ-contractSnd (λ f →
        isContrRetract (λ { (g , h) → g , (λ i q p → h p q (~ i)) })
          (λ { (g , h) → g , (λ p q i → h (~ i) q p) }) (λ _ → refl)
          ((equivΠCod (λ _ → _ , constant)) .snd .equiv-proof (λ q p → f p))) .snd

    pullback-diagonal-equiv : {P : Type ℓ'} {Q : Type ℓ''}
      → isProp P → isProp Q → ∥ P ⊎ Q ∥₁
      → isEquiv (pullback-diagonal {A = A} {P = P} {Q = Q})
    pullback-diagonal-equiv {A = A} {P = P} {Q = Q} pP pQ = PT.rec (isPropIsEquiv _) λ
      { (Sum.inl p) → pullback-diagonal-equiv-left (p , pP p)
      ; (Sum.inr q) → isEquiv[equivFunA≃B∘f]→isEquiv[f] pullback-diagonal
          (isoToEquiv swap) (pullback-diagonal-equiv-left (q , pQ q)) }
      where
      swap : Iso (Pullback P Q A) (Pullback Q P A)
      Iso.fun swap (f , g , h) = g , f , (λ q p → sym (h p q))
      Iso.inv swap (g , f , h) = f , g , (λ p q → sym (h q p))
      Iso.rightInv swap _ = refl
      Iso.leftInv swap _ = refl

    --   (𝟎,𝟏) ─────────────→ (𝟏,𝟏)
    --      ↑     u         ↗     ↑
    --      │   s ≤₂ t    /       │
    --      │           /         │
    --      │         /   t ≤₂ s  │
    --      │       /       l     │
    --   (𝟎,𝟎) ─────────────→ (𝟏,𝟎)
    --             t ≤₂ s ∧ s ≤₂ t
    GluedTriangles : Type ℓ → Type ℓ
    GluedTriangles A = Σ[ l ∈ (Δ² → A) ] Σ[ u ∈ (Δ² → A) ]
      ((s t : 𝟚) (p : t ≤₂ s) (q : s ≤₂ t) → l (s , t , p) ≡ u (t , s , q))

    split : (𝟚 → 𝟚 → A) → GluedTriangles A
    split a = (λ t → a (t .fst) (t .snd .fst)) ,
      (λ t → a (t .snd .fst) (t .fst)) , (λ _ _ _ _ → refl)

    split-equiv : isEquiv (split {A = A})
    split-equiv {A = A} = compEquiv
      (equivΠCod λ s → equivΠCod λ t → pullback-diagonal ,
        pullback-diagonal-equiv (≤₂-isProp t s) (≤₂-isProp s t) (≤₂-total t s))
      (isoToEquiv rearrange) .snd
      where
      rearrange : Iso ((s t : 𝟚) → Pullback (t ≤₂ s) (s ≤₂ t) A) (GluedTriangles A)
      Iso.fun rearrange a =
        (λ t → a (t .fst) (t .snd .fst) .fst (t .snd .snd)) ,
        (λ t → a (t .snd .fst) (t .fst) .snd .fst (t .snd .snd)) ,
        (λ s t → a s t .snd .snd)
      Iso.inv rearrange (l , u , h) s t =
        (λ p → l (s , t , p)) , (λ q → u (t , s , q)) , h s t
      Iso.rightInv rearrange _ = refl
      Iso.leftInv rearrange _ = refl

    --   u(𝟏,𝟎) ───────────→ u(𝟏,𝟏) ≡ l(𝟏,𝟏)
    --      ↑     u         ↗     ↑
    --      │             /       │
    --      │           /         │
    --      │         /     l     │
    --   u(𝟎,𝟎) ≡ l(𝟎,𝟎) ────→ l(𝟏,𝟎)
    --         u ∘ diagonal₂ ≡ l ∘ diagonal₂
    Split : Type ℓ → Type ℓ
    Split A = Σ[ l ∈ (Δ² → A) ] Σ[ u ∈ (Δ² → A) ] (l ∘ diagonal₂ ≡ u ∘ diagonal₂)

    split-diagonal : (𝟚 → 𝟚 → A) → Split A
    split-diagonal a = (λ t → a (t .fst) (t .snd .fst)) ,
      (λ t → a (t .snd .fst) (t .fst)) , refl

    split-diagonal-equiv : isEquiv (split-diagonal {A = A})
    split-diagonal-equiv {A = A} = compEquiv (_ , split-equiv)
      (Σ-cong-equiv-snd λ l → Σ-cong-equiv-snd λ u → compEquiv
        (equivΠCod λ s → compEquiv
          (isoToEquiv (uncurry-diagonal l u s))
          (Π-contractDom (diagonal-fiber s)))
        (isoToEquiv (diagonal-path l u))) .snd
      where
      uncurry-diagonal : (l u : Δ² → A) (s : 𝟚) → Iso
        ((t : 𝟚) (p : t ≤₂ s) (q : s ≤₂ t) → l (s , t , p) ≡ u (t , s , q))
        (((t , p , q) : Σ[ t ∈ 𝟚 ] ((t ≤₂ s) × (s ≤₂ t))) →
          l (s , t , p) ≡ u (t , s , q))
      Iso.fun (uncurry-diagonal l u s) h (t , p , q) = h t p q
      Iso.inv (uncurry-diagonal l u s) h t p q = h (t , p , q)
      Iso.rightInv (uncurry-diagonal l u s) _ = refl
      Iso.leftInv (uncurry-diagonal l u s) _ = refl

      diagonal-path : (l u : Δ² → A) → Iso
        ((s : 𝟚) → l (diagonal₂ s) ≡ u (diagonal₂ s))
        (l ∘ diagonal₂ ≡ u ∘ diagonal₂)
      Iso.fun (diagonal-path l u) = funExt
      Iso.inv (diagonal-path l u) = funExt⁻
      Iso.rightInv (diagonal-path l u) _ = refl
      Iso.leftInv (diagonal-path l u) _ = refl

      diagonal-fiber : (s : 𝟚) → isContr (Σ[ t ∈ 𝟚 ] ((t ≤₂ s) × (s ≤₂ t)))
      diagonal-fiber s = (s , ≤₂-refl s , ≤₂-refl s) , λ { (t , p , q) →
        Σ≡Prop (λ t → isProp× (≤₂-isProp t s) (≤₂-isProp s t)) (≤₂-antisym q p) }

    -- RS17, proof of Proposition 8.13: 
    -- 𝟚 × 𝟚 is the pushout of two copies of Δ² 
    □²-elim : (𝟚 → 𝟚 → A) ≃
      (Σ[ l ∈ (Δ² → A) ] Σ[ u ∈ (Δ² → A) ] (l ∘ diagonal₂ ≡ u ∘ diagonal₂))
    □²-elim = split-diagonal , split-diagonal-equiv

    restrict : (Δ² → A) → (Σ[ f ∈ (𝟚 → A) ] Σ[ g ∈ (𝟚 → A) ] (f 𝟏 ≡ g 𝟎))
    restrict t = Iso.fun Λ²-elim (t ∘ ι-horn)

    --        z ── const z ─→ z
    --        ↑               ↑
    --        │               │ g
    --        │               │
    --        x ───── f ────→ y
    SquareFiller : (k : Σ[ f ∈ (𝟚 → A) ] Σ[ g ∈ (𝟚 → A) ] (f 𝟏 ≡ g 𝟎)) → Type _
    SquareFiller {A = A} k =
      Σ[ c ∈ (Σ[ a ∈ (𝟚 → 𝟚 → A) ] Σ[ z ∈ A ] ((λ s → a s 𝟏) ≡ const z)) ]
        (((λ s → c .fst s 𝟎) , (λ u → c .fst 𝟏 u) , refl) ≡ k)

    composite≃square-filler : (f : 𝟚 → A) (z : A) (g : f 𝟏 ≤ z)
      → Composite (f , refl , refl) g ≃ SquareFiller (f , hom-path g , sym (left-endpoint g))
    composite≃square-filler {A = A} f z g =
        Composite (f , refl , refl) g
      ≃⟨ isoToEquiv forget-left ⟩
        fiber (λ (q : (s : 𝟚) → f s ≤ z) → q 𝟏) g
      ≃⟨ isoToEquiv (invIso (fibers-total _ _ _)) ⟩
        fiber (λ { (z , q) → z , q 𝟏 }) (z , g)
      ≃⟨ isoToEquiv (invIso (fibers-total _ _ _)) ⟩
        fiber (λ { (f , z , q) → f , z , q 𝟏 }) (f , z , g)
      ≃⟨ fiber-square uncarry boundary-unpack commutes (f , z , g) ⟩
        SquareFiller (f , hom-path g , sym (left-endpoint g))
      ■
      where
      forget-left : Iso (Composite (f , refl , refl) g)
        (fiber (λ (q : (s : 𝟚) → f s ≤ z) → q 𝟏) g)
      Iso.fun forget-left (h , q , p , r) = q , r
      Iso.inv forget-left (q , r) = q 𝟎 , q , refl , r
      Iso.rightInv forget-left _ = refl
      Iso.leftInv forget-left (h , q , p , r) i = p i , q , (λ j → p (i ∧ j)) , r

      uncarry : (Σ[ f ∈ (𝟚 → A) ] Σ[ z ∈ A ] ((s : 𝟚) → f s ≤ z)) ≃
        (Σ[ a ∈ (𝟚 → 𝟚 → A) ] Σ[ z ∈ A ] ((λ s → a s 𝟏) ≡ const z))
      uncarry = compEquiv (isoToEquiv rearrange)
        (Σ-contractSnd (λ c → isContrSingl (λ s → c .fst s 𝟎)))
        where
        rearrange : Iso (Σ[ f ∈ (𝟚 → A) ] Σ[ z ∈ A ] ((s : 𝟚) → f s ≤ z))
          (Σ[ c ∈ (Σ[ a ∈ (𝟚 → 𝟚 → A) ] Σ[ z ∈ A ] ((λ s → a s 𝟏) ≡ const z)) ]
            Σ[ f ∈ (𝟚 → A) ] ((λ s → c .fst s 𝟎) ≡ f))
        Iso.fun rearrange (f , z , q) =
          (hom-path ∘ q , z , (λ i s → right-endpoint (q s) i)) ,
          f , (λ i s → left-endpoint (q s) i)
        Iso.inv rearrange ((a , z , p) , f , h) =
          f , z , (λ s → a s , (λ i → h i s) , (λ i → p i s))
        Iso.rightInv rearrange _ = refl
        Iso.leftInv rearrange _ = refl

      boundary-unpack : (Σ[ f ∈ (𝟚 → A) ] Σ[ z ∈ A ] (f 𝟏 ≤ z)) ≃
        (Σ[ f ∈ (𝟚 → A) ] Σ[ g ∈ (𝟚 → A) ] (f 𝟏 ≡ g 𝟎))
      boundary-unpack = compEquiv (isoToEquiv rearrange)
        (Σ-contractSnd (λ h → isContrSingl (h .snd .fst 𝟏)))
        where
        rearrange : Iso (Σ[ f ∈ (𝟚 → A) ] Σ[ z ∈ A ] (f 𝟏 ≤ z))
          (Σ[ h ∈ (Σ[ f ∈ (𝟚 → A) ] Σ[ g ∈ (𝟚 → A) ] (f 𝟏 ≡ g 𝟎)) ]
            Σ[ z ∈ A ] (h .snd .fst 𝟏 ≡ z))
        Iso.fun rearrange (f , z , g , p , q) = (f , g , sym p) , z , q
        Iso.inv rearrange ((f , g , p) , z , q) = f , z , g , sym p , q
        Iso.rightInv rearrange _ = refl
        Iso.leftInv rearrange _ = refl

      commutes : boundary-unpack .fst ∘ (λ { (f , z , q) → f , z , q 𝟏 }) ≡
        (λ c → restrict (λ t → c .fst (t .fst) (t .snd .fst))) ∘ uncarry .fst
      commutes i (f , z , q) = (λ s → left-endpoint (q s) (~ i)) , hom-path (q 𝟏) ,
        (λ j → left-endpoint (q 𝟏) (~ i ∧ ~ j))

    UpperFiller : (d : 𝟚 → A) → Type _
    UpperFiller {A = A} d =
      Σ[ c ∈ (Σ[ u ∈ (Δ² → A) ] Σ[ z ∈ A ] (u ∘ right₂ ≡ const z)) ]
        (d ≡ c .fst ∘ diagonal₂)

    upper-filler : (d : 𝟚 → A) → UpperFiller d
    upper-filler d = ((λ t → d (t .fst)) , d 𝟏 , refl) , refl

    --       z ─────────→ z
    --       ↑     u    ↗ ↑
    --       │        /   │
    --       │      / l   │
    --       x ─────────→ y
    square-filler≃triangles : (k : Σ[ f ∈ (𝟚 → A) ] Σ[ g ∈ (𝟚 → A) ] (f 𝟏 ≡ g 𝟎))
      → SquareFiller k ≃ (Σ[ t ∈ fiber restrict k ] UpperFiller (t .fst ∘ diagonal₂))
    square-filler≃triangles {A = A} k =
        SquareFiller k
      ≃⟨ isoToEquiv reassociate ⟩
        (Σ[ a ∈ (𝟚 → 𝟚 → A) ]
          (Σ[ z ∈ A ] ((λ s → a s 𝟏) ≡ const z)) ×
          (restrict (λ t → a (t .fst) (t .snd .fst)) ≡ k))
      ≃⟨ Σ-cong-equiv-fst □²-elim ⟩
        (Σ[ t ∈ Split A ] (Σ[ z ∈ A ] (t .snd .fst ∘ right₂ ≡ const z)) × (restrict (t .fst) ≡ k))
      ≃⟨ isoToEquiv regroup ⟩
        (Σ[ t ∈ fiber restrict k ] UpperFiller (t .fst ∘ diagonal₂))
      ■
      where
      reassociate : Iso (SquareFiller k)
        (Σ[ a ∈ (𝟚 → 𝟚 → A) ]
          (Σ[ z ∈ A ] ((λ s → a s 𝟏) ≡ const z)) ×
          (restrict (λ t → a (t .fst) (t .snd .fst)) ≡ k))
      Iso.fun reassociate ((a , z , p) , q) = a , (z , p) , q
      Iso.inv reassociate (a , (z , p) , q) = (a , z , p) , q
      Iso.rightInv reassociate _ = refl
      Iso.leftInv reassociate _ = refl
      regroup : Iso
        (Σ[ t ∈ Split A ] (Σ[ z ∈ A ] (t .snd .fst ∘ right₂ ≡ const z)) × (restrict (t .fst) ≡ k))
        (Σ[ t ∈ fiber restrict k ] UpperFiller (t .fst ∘ diagonal₂))
      Iso.fun regroup ((l , u , h) , (z , p) , q) = (l , q) , (u , z , p) , h
      Iso.inv regroup ((l , q) , (u , z , p) , h) = (l , u , h) , (z , p) , q
      Iso.rightInv regroup _ = refl
      Iso.leftInv regroup _ = refl

    upper-filler-isContr : isSegalRS A → (d : 𝟚 → A) → isContr (UpperFiller d)
    upper-filler-isContr {A = A} S d = isContrRetract
      (λ { (c , p) → c , sym p }) (λ { (c , p) → c , sym p }) (λ _ → refl)
      (diagonal-equiv .equiv-proof d)
      where
      degenerate : (𝟚 → A) → Σ[ u ∈ (Δ² → A) ] Σ[ z ∈ A ] (u ∘ right₂ ≡ const z)
      degenerate d = (λ t → d (t .fst)) , d 𝟏 , refl

      constant-boundary : (f : 𝟚 → A)
        → isContr (Σ[ g ∈ (𝟚 → A) ] Σ[ p ∈ (f 𝟏 ≡ g 𝟎) ] Σ[ z ∈ A ] (g ≡ const z))
      constant-boundary f = isContrRetract
        (λ { (g , p , z , q) → z , (g , sym q) , p })
        (λ { (z , (g , q) , p) → g , p , z , sym q }) (λ _ → refl)
        (isOfHLevelRespectEquiv 0 (invEquiv (Σ-cong-equiv-snd
          λ z → Σ-contractFst (isContrSingl (const z)))) (isContrSingl (f 𝟏)))

      bottom-equiv : isEquiv (λ (c : Σ[ u ∈ (Δ² → A) ] Σ[ z ∈ A ] (u ∘ right₂ ≡ const z))
        → c .fst ∘ bottom₂)
      bottom-equiv = compEquiv
        (Σ-cong-equiv-fst (compEquiv (_ , segalRS→restrictionEquiv S) (isoToEquiv Λ²-elim)))
        (compEquiv (isoToEquiv rearrange) (Σ-contractSnd constant-boundary)) .snd
        where
        rearrange : Iso
          (Σ[ k ∈ (Σ[ f ∈ (𝟚 → A) ] Σ[ g ∈ (𝟚 → A) ] (f 𝟏 ≡ g 𝟎)) ]
            Σ[ z ∈ A ] (k .snd .fst ≡ const z))
          (Σ[ f ∈ (𝟚 → A) ] Σ[ g ∈ (𝟚 → A) ] Σ[ p ∈ (f 𝟏 ≡ g 𝟎) ]
            Σ[ z ∈ A ] (g ≡ const z))
        Iso.fun rearrange ((f , g , p) , z , q) = f , g , p , z , q
        Iso.inv rearrange (f , g , p , z , q) = (f , g , p) , z , q
        Iso.rightInv rearrange _ = refl
        Iso.leftInv rearrange _ = refl

      diagonal-equiv : isEquiv (λ (c : Σ[ u ∈ (Δ² → A) ] Σ[ z ∈ A ] (u ∘ right₂ ≡ const z))
        → c .fst ∘ diagonal₂)
      diagonal-equiv = precomposesToId→Equiv _ degenerate refl
        (composesToId→Equiv _ degenerate refl bottom-equiv)

  segal→segalRS : isSegal A → isSegalRS A
  segal→segalRS S = restrictionEquiv→segalRS
    (isEquiv[equivFunA≃B∘f]→isEquiv[f] _ (isoToEquiv Λ²-elim) triangle-fillers)
    where
    triangle-fillers : isEquiv restrict
    triangle-fillers .equiv-proof (f , g , p) = isContrRetract
      (λ t → t , upper-filler (t .fst ∘ diagonal₂)) fst (λ _ → refl)
      (isOfHLevelRespectEquiv 0
        (compEquiv (composite≃square-filler f (g 𝟏) (g , sym p , refl))
          (square-filler≃triangles (f , g , p)))
        (S (f , refl , refl) (g , sym p , refl)))

  segalRS→segal : isSegalRS A → isSegal A
  segalRS→segal {A = A} S {z = z} (f , p , q) g =
    transport (λ i → (g : q i ≤ z) →
      isContr (Composite (f , (λ j → p (i ∧ j)) , (λ j → q (i ∧ j))) g))
      (normalized f z) g
    where
    square-fillers : (k : Σ[ f ∈ (𝟚 → A) ] Σ[ g ∈ (𝟚 → A) ] (f 𝟏 ≡ g 𝟎))
      → isContr (SquareFiller k)
    square-fillers k = isOfHLevelRespectEquiv 0 (invEquiv (square-filler≃triangles k))
      (isContrΣ
        (compEquiv (_ , segalRS→restrictionEquiv S) (isoToEquiv Λ²-elim) .snd .equiv-proof k)
        (λ t → upper-filler-isContr S (t .fst ∘ diagonal₂)))

    normalized : (f : 𝟚 → A) (z : A) (g : f 𝟏 ≤ z) → isContr (Composite (f , refl , refl) g)
    normalized f z g = isOfHLevelRespectEquiv 0 (invEquiv (composite≃square-filler f z g))
      (square-fillers (f , hom-path g , sym (left-endpoint g)))

  isSegal≡isSegalRS : isSegal A ≡ isSegalRS A
  isSegal≡isSegalRS = hPropExt
    (isPropImplicitΠ3 λ _ _ _ → isPropΠ2 λ _ _ → isPropIsContr)
    (isPropΠ λ _ → isPropIsContr)
    segal→segalRS segalRS→segal

isSegal≡isPathTransitive : isSegal A ≡ isPathTransitive A
isSegal≡isPathTransitive {A = A} =
  isSegal A          ≡⟨ isSegal≡isSegalRS ⟩
  isSegalRS A        ≡⟨ isSegalRS≡isPathTransitive ⟩
  isPathTransitive A ∎
