module DPRLR.Simplicial.PreorderLocalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Bool hiding (elim ; _≤_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization as Localization hiding (rec)
open import Cubical.HITs.Nullification hiding (rec ; elim ; toPathP⁻)
open import Cubical.HITs.Nullification.Properties using (toPathP⁻-sq)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.S1 hiding (rec ; elim)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Interval
open import DPRLR.Simplicial.Segal
open import DPRLR.Simplicial.Shapes using (Λ²₁ ; Δ² ; spine₂)

private
  variable
    ℓ ℓ' : Level
    X Y : Type ℓ

𝕊 : Type ℓ → Type ℓ
𝕊 X =
  Pushout {A = X × Bool}
    (λ (x , b) → x , (if b then 𝟏 else 𝟎))
    snd

𝕊map : {X : Type ℓ} {Y : Type ℓ'} → (X → Y) → 𝕊 X → 𝕊 Y
𝕊map f (inl (x , i)) = inl (f x , i)
𝕊map f (inr b) = inr b
𝕊map f (push (x , b) i) = push (f x , b) i

𝕊-cocone : Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
𝕊-cocone X Y =
  Σ (X × X) (λ (x , x') → Y → x ≤ x')

𝕊-elim : {X : Type ℓ} → (Y : Type ℓ') → Iso (𝕊 Y → X) (𝕊-cocone X Y)
Iso.fun (𝕊-elim Y) k =
  (k (inr false) , k (inr true))
  , λ y →
      (λ i → k (inl (y , i)))
      , cong k (push (y , false))
      , cong k (push (y , true))
Iso.inv (𝕊-elim Y) (_ , q) (inl (y , i)) =
  hom-path (q y) i
Iso.inv (𝕊-elim Y) ((x , x') , q) (inr false) = x
Iso.inv (𝕊-elim Y) ((x , x') , q) (inr true) = x'
Iso.inv (𝕊-elim Y) (_ , q) (push (y , false) i) =
  left-endpoint (q y) i
Iso.inv (𝕊-elim Y) (_ , q) (push (y , true) i) =
  right-endpoint (q y) i
Iso.rightInv (𝕊-elim Y) (_ , q) = refl
Iso.leftInv (𝕊-elim Y) k i (inl (y , j)) = k (inl (y , j))
Iso.leftInv (𝕊-elim Y) k i (inr false) = k (inr false)
Iso.leftInv (𝕊-elim Y) k i (inr true) = k (inr true)
Iso.leftInv (𝕊-elim Y) k i (push (y , false) j) = k (push (y , false) j)
Iso.leftInv (𝕊-elim Y) k i (push (y , true) j) = k (push (y , true) j)

𝕊-elim≃ : {X : Type ℓ} → (Y : Type ℓ') → (𝕊 Y → X) ≃ 𝕊-cocone X Y
𝕊-elim≃ Y = isoToEquiv (𝕊-elim Y)

isBoundarySeparated : Type ℓ → Type ℓ
isBoundarySeparated X =
  isLocal {A = Unit} (λ _ → 𝕊map (λ (_ : Bool) → tt)) X

isBoundarySeparated≡isThin :
  {X : Type ℓ}
  → isBoundarySeparated X ≡ isThin X
isBoundarySeparated≡isThin {X = X} =
  hPropExt
    (isPropΠ λ _ → isPropIsPathSplitEquiv _)
    (isPropΠ2 λ _ _ → isPropIsProp)
    isBoundarySeparated→isThin
    isThin→isBoundarySeparated
  where
  P Q : X × X → Type _
  P (x , x') = Unit → x ≤ x'
  Q (x , x') = Bool → x ≤ x'

  φ : (xx' : X × X) → P xx' → Q xx'
  φ _ q _ = q tt

  isBoundarySeparated→isThin : isBoundarySeparated X → isThin X
  isBoundarySeparated→isThin isBoundarySeparatedX x x' p p' =
    sym (funExt⁻ secφ false) ∙ funExt⁻ secφ true
    where
    totalφ-isEquiv : isEquiv (λ ((xx' , q) : Σ (X × X) P) → xx' , φ xx' q)
    totalφ-isEquiv = equivIsEquiv $
      𝕊-cocone X Unit ≃⟨ invEquiv (𝕊-elim≃ Unit) ⟩
      (𝕊 Unit → X)    ≃⟨ _ , toIsEquiv _ (isBoundarySeparatedX tt) ⟩
      (𝕊 Bool → X)    ≃⟨ 𝕊-elim≃ Bool ⟩
      𝕊-cocone X Bool ■

    φ≃ : P (x , x') ≃ Q (x , x')
    φ≃ = φ (x , x') , fiberEquiv P Q φ totalφ-isEquiv (x , x')

    secφ : φ (x , x') (invEq φ≃ (if_then p' else p)) ≡ (if_then p' else p)
    secφ = secEq φ≃ (if_then p' else p)

  isThin→isBoundarySeparated : isThin X → isBoundarySeparated X
  isThin→isBoundarySeparated isThinX _ =
    fromIsEquiv _ (subst isEquiv boundary-separationFun (equivIsEquiv boundary-separation))
    where
    φ-equiv : (xx' : X × X) → isEquiv (φ xx')
    φ-equiv (x , x') = isoToIsEquiv
      (isProp→Iso
        (isPropΠ λ _ → isThinX x x')
        (isPropΠ λ _ → isThinX x x')
        (φ (x , x'))
        (λ q _ → q false))

    boundary-separation : (𝕊 Unit → X) ≃ (𝕊 Bool → X)
    boundary-separation =
      (𝕊 Unit → X)    ≃⟨ 𝕊-elim≃ Unit ⟩
      𝕊-cocone X Unit ≃⟨ _ , totalEquiv P Q φ φ-equiv ⟩
      𝕊-cocone X Bool ≃⟨ invEquiv (𝕊-elim≃ Bool) ⟩
      (𝕊 Bool → X)    ■

    boundary-separationFun :
      equivFun boundary-separation ≡ (_∘ 𝕊map (λ (_ : Bool) → tt))
    boundary-separationFun = funExt λ _ → funExt λ
      { (inl (b , i)) → refl
      ; (inr false) → refl
      ; (inr true) → refl
      ; (push (b , false) i) → refl
      ; (push (b , true) i) → refl
      }

isS¹Null≡isSet : {X : Type ℓ} → isNull (const {B = Unit} S¹) X ≡ isSet X
isS¹Null≡isSet {X = X} =
  hPropExt isPropIsNull isPropIsSet isNull→isSet isSet→isNull
  where
  isNull→isSet : isNull (const {B = Unit} S¹) X → isSet X
  isNull→isSet nullX =
    isOfHLevelΩ→isOfHLevel 0 λ x → isContr→isProp (isContrLoop x)
    where
    const-isEquiv : isEquiv (const {A = X} {B = S¹})
    const-isEquiv = toIsEquiv _ (nullX tt)

    X≃ΣLoop : X ≃ (Σ[ x ∈ X ] (x ≡ x))
    X≃ΣLoop =
      compEquiv (const {A = X} {B = S¹} , const-isEquiv)
        (isoToEquiv IsoFunSpaceS¹)

    fst-isEquiv : isEquiv (fst {A = X} {B = λ x → x ≡ x})
    fst-isEquiv =
      precomposesToId→Equiv fst (equivFun X≃ΣLoop) refl (snd X≃ΣLoop)

    isContrLoop : (x : X) → isContr (x ≡ x)
    isContrLoop x =
      isOfHLevelRespectEquiv 0
        (invEquiv (fiberProjEquiv X (λ y → y ≡ y) x))
        (fst-isEquiv .equiv-proof x)

  isSet→isNull : isSet X → isNull (const {B = Unit} S¹) X
  isSet→isNull setX _ = fromIsEquiv _ const-isEquiv
    where
    loopContr : (y : X) → isContr (y ≡ y)
    loopContr y = refl , λ p → setX y y refl p

    e : X ≃ (S¹ → X)
    e =
      compEquiv (invEquiv (Σ-contractSnd loopContr))
        (invEquiv (isoToEquiv IsoFunSpaceS¹))

    e≡ : equivFun e ≡ const {A = X} {B = S¹}
    e≡ = funExt λ x → funExt λ { base → refl ; (loop i) → refl }

    const-isEquiv : isEquiv (const {A = X} {B = S¹})
    const-isEquiv = subst isEquiv e≡ (e .snd)

data Requirements : Type₀ where
  segal thin hset : Requirements

Sᴾ : Requirements → Type₀
Sᴾ segal = Λ²₁
Sᴾ thin = 𝕊 Bool
Sᴾ hset = S¹

Tᴾ : Requirements → Type₀
Tᴾ segal = Δ²
Tᴾ thin = 𝕊 Unit
Tᴾ hset = Unit

Fᴾ : (α : Requirements) → Sᴾ α → Tᴾ α
Fᴾ segal = spine₂
Fᴾ thin = 𝕊map (λ (_ : Bool) → tt)
Fᴾ hset = λ _ → tt

isPreorder : Type ℓ → Type ℓ
isPreorder = isLocal Fᴾ

∥_∥ᴾ : Type ℓ → Type ℓ
∥_∥ᴾ = Localize Fᴾ

ηᴾ : X → ∥ X ∥ᴾ
ηᴾ = ∣_∣

isPreorderP : {X : Type ℓ} → isPreorder ∥ X ∥ᴾ
isPreorderP = isLocal-Localize Fᴾ _

isPropIsPreorder : {X : Type ℓ} → isProp (isPreorder X)
isPropIsPreorder =
  isPropΠ λ _ → isPropIsPathSplitEquiv _

rec : isPreorder Y → (X → Y) → ∥ X ∥ᴾ → Y
rec = Localization.rec

open isPathSplitEquiv public

isProp→isLocal :
  {X : Type ℓ}
  → ((α : Requirements) → Sᴾ α)
  → isProp X
  → isPreorder X
isProp→isLocal s isPropX α =
  fromIsEquiv _ $ isoToIsEquiv $
  iso
    (λ g → g ∘ Fᴾ α)
    (λ h _ → h (s α))
    (λ _ → isPropΠ (λ _ → isPropX) _ _)
    (λ _ → isPropΠ (λ _ → isPropX) _ _)

isPreorder→isThin :
  {X : Type ℓ}
  → isPreorder X
  → isThin X
isPreorder→isThin isPreorderX =
  transport isBoundarySeparated≡isThin λ _ → isPreorderX thin

isPreorder→isSet :
  {X : Type ℓ}
  → isPreorder X
  → isSet X
isPreorder→isSet isPreorderX =
  transport isS¹Null≡isSet λ _ →
  fromIsEquiv _ $ equivIsEquiv $
  compEquiv (invEquiv (UnitToType≃ _)) (_ , toIsEquiv _ (isPreorderX hset))

isProp→isPreorder :
  {X : Type ℓ}
  → isProp X
  → isPreorder X
isProp→isPreorder =
  isProp→isLocal λ
    { segal → inl 𝟎
    ; thin → inr true
    ; hset → base
    }

isPreorderΠ :
  {X : Type ℓ} {Y : X → Type ℓ'}
  → ((x : X) → isPreorder (Y x))
  → isPreorder ((x : X) → Y x)
isPreorderΠ {X = X} {Y = Y} isPreorderY α =
  fromIsEquiv _ (equivIsEquiv equiv)
  where
  flip≃ : (W : Type₀) → (W → (x : X) → Y x) ≃ ((x : X) → W → Y x)
  flip≃ W = isoToEquiv (iso flip flip (λ _ → refl) (λ _ → refl))

  equiv : (Tᴾ α → (x : X) → Y x) ≃ (Sᴾ α → (x : X) → Y x)
  equiv =
    (Tᴾ α → (x : X) → Y x) ≃⟨ flip≃ (Tᴾ α) ⟩
    ((x : X) → Tᴾ α → Y x) ≃⟨ equivΠCod (λ x → _ , toIsEquiv _ (isPreorderY x α)) ⟩
    ((x : X) → Sᴾ α → Y x) ≃⟨ invEquiv (flip≃ (Sᴾ α)) ⟩
    (Sᴾ α → (x : X) → Y x) ■

HomP-isProp :
  {A : Type ℓ} {P : A → Type ℓ'} {x y : A}
  {h : x ≤ y} {u : P x} {v : P y}
  → ((a : A) → isProp (P a))
  → isProp (P ⊢ u ≤[ h ] v)
HomP-isProp {P = P} {h = h} Pprop =
  isPropΣ
    (isPropΠ λ i → Pprop (hom-path h i))
    λ q →
      isProp×
        (isOfHLevelPathP' 1 (isProp→isSet (Pprop _)) _ _)
        (isOfHLevelPathP' 1 (isProp→isSet (Pprop _)) _ _)

Composite-isProp :
  {A : Type ℓ}
  → ((x y : A) → isProp (x ≤ y))
  → {x y z : A}
  → (f : x ≤ y)
  → (g : y ≤ z)
  → isProp (Composite f g)
Composite-isProp homProp {z = z} f g =
  isPropΣ
    (homProp _ z)
    (λ h → HomP-isProp λ w → homProp w z)

isPreorder→isSegal :
  {X : Type ℓ}
  → isPreorder X
  → isSegal X
isPreorder→isSegal {X = X} isPreorderX {x = x} {y = y} {z = z} f g =
  center , Composite-isProp homProp f g center
  where
  homProp : (u v : X) → isProp (u ≤ v)
  homProp = isPreorder→isThin isPreorderX

  spine : Λ²₁ → X
  spine (inl i) = hom-path f i
  spine (inr i) = hom-path g i
  spine (push tt i) = (right-endpoint f ∙ sym (left-endpoint g)) i

  filler : Δ² → X
  filler = isPreorderX segal .sec .fst spine

  filler-spine : filler ∘ spine₂ ≡ spine
  filler-spine = isPreorderX segal .sec .snd spine

  filler-spine-at : (s : Λ²₁) → filler (spine₂ s) ≡ spine s
  filler-spine-at = funExt⁻ filler-spine

  top-collapse : (i : 𝟚) → filler (inl (i , 𝟏)) ≡ z
  top-collapse i =
    cong filler (push i)
    ∙ sym (cong filler (push 𝟏))
    ∙ filler-spine-at (inr 𝟏)
    ∙ right-endpoint g

  h : x ≤ z
  h =
    (λ i → filler (inl (𝟎 , i)))
    , filler-spine-at (inl 𝟎) ∙ left-endpoint f
    , top-collapse 𝟎

  q : (i : 𝟚) → hom-path f i ≤ z
  q i =
    (λ j → filler (inl (i , j)))
    , filler-spine-at (inl i)
    , top-collapse i

  witness : (λ w → w ≤ z) ⊢ h ≤[ f ] g
  witness =
    q
    , isProp→PathP (λ i → homProp (left-endpoint f i) z) (q 𝟎) h
    , isProp→PathP (λ i → homProp (right-endpoint f i) z) (q 𝟏) g

  center : Composite f g
  center = h , witness

isLocalPathFun :
  isPreorder Y
  → (α : Requirements) (P₀ P₁ : Tᴾ α → Y)
  → isPathSplitEquiv (λ (b : (t : Tᴾ α) → P₀ t ≡ P₁ t) → b ∘ Fᴾ α)
isLocalPathFun isPreorderY α P₀ P₁ =
  fromIsEquiv _ $
  isEquiv[equivFunA≃B∘f]→isEquiv[f] (λ b → b ∘ Fᴾ α) funExtEquiv $
  equivIsEquiv $
    compEquiv funExtEquiv $
    congEquiv ((λ k → k ∘ Fᴾ α) , toIsEquiv _ (isPreorderY α))

rec-unique :
  isPreorder Y
  → (f g : ∥ X ∥ᴾ → Y)
  → ((x : X) → f (ηᴾ x) ≡ g (ηᴾ x))
  → (z : ∥ X ∥ᴾ) → f z ≡ g z
rec-unique {X = X} isPreorderY f g p = elim
  where
  elim : (z : ∥ X ∥ᴾ) → f z ≡ g z

  Q : ∥ X ∥ᴾ → Type _
  Q z = f z ≡ g z

  K :
    (α : Requirements) (w : Sᴾ α → ∥ X ∥ᴾ)
    → (f ∘ ext α w) ∘ Fᴾ α ≡ (g ∘ ext α w) ∘ Fᴾ α
  K α w =
    funExt λ s →
      cong f (isExt α w s) ∙ elim (w s) ∙ cong g (sym (isExt α w s))

  secCongDep' :
    (α : Requirements) {u v : Tᴾ α → ∥ X ∥ᴾ} (E : u ≡ v)
    (bx : (t : Tᴾ α) → Q (u t))
    (by : (t : Tᴾ α) → Q (v t))
    → hasSection
        (λ (P : PathP (λ i → (t : Tᴾ α) → Q (E i t)) bx by)
         → cong₂ (λ u (b : (t : Tᴾ α) → Q (u t)) → b ∘ Fᴾ α) E P)
  secCongDep' α E =
    secCongDep
      (λ u (b : (t : Tᴾ α) → Q (u t)) → b ∘ Fᴾ α) E
      (λ u → secCong (isLocalPathFun isPreorderY α (f ∘ u) (g ∘ u)))

  base-path :
    (α : Requirements) (u v : Tᴾ α → ∥ X ∥ᴾ)
    → ((s : Sᴾ α) → u (Fᴾ α s) ≡ v (Fᴾ α s))
    → u ≡ v
  base-path α u v q = funExt λ t → ≡ext α u v q t

  endpt : (α : Requirements) (u : Tᴾ α → ∥ X ∥ᴾ) (t : Tᴾ α) → Q (u t)
  endpt α u t = transport refl (elim (u t))

  input :
    (α : Requirements) (u v : Tᴾ α → ∥ X ∥ᴾ)
    (q : (s : Sᴾ α) → u (Fᴾ α s) ≡ v (Fᴾ α s))
    → PathP (λ i → (s : Sᴾ α)
      → Q (≡ext α u v q (Fᴾ α s) i)) (endpt α u ∘ Fᴾ α) (endpt α v ∘ Fᴾ α)
  input α u v q i s =
    transport (λ k → Q (≡isExt α u v q s (~ k) i)) (elim (q s i))

  elim ∣ x ∣ = p x
  elim (ext α w t) =
    funExt⁻ (secCong (isPreorderY α) (f ∘ ext α w) (g ∘ ext α w) .fst (K α w)) t
  elim (isExt α w s i) =
    compPathR→PathP
      (λ i' →
        funExt⁻
          (secCong (isPreorderY α) (f ∘ ext α w) (g ∘ ext α w) .snd (K α w) i')
          s)
      i
  elim (≡ext α u v q t i) =
    hcomp
      (λ k → λ
        { (i = i0) → transportRefl (elim (u t)) k
        ; (i = i1) → transportRefl (elim (v t)) k
        })
      (secCongDep' α (base-path α u v q) (endpt α u) (endpt α v) .fst (input α u v q) i t)
  elim (≡isExt α u v q s i j) =
    hcomp
      (λ k → λ
        { (j = i0) → toPathP⁻-sq (elim (u (Fᴾ α s))) k i
        ; (j = i1) → toPathP⁻-sq (elim (v (Fᴾ α s))) k i
        ; (i = i1) → elim (q s j)
        })
      (toPathP⁻
        {A = λ i' → Q (≡isExt α u v q s i' j)}
        (λ i' →
          secCongDep' α (base-path α u v q) (endpt α u) (endpt α v)
            .snd (input α u v q) i' j s)
        i)
