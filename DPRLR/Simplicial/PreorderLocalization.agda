module DPRLR.Simplicial.PreorderLocalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Bool hiding (elim ; _≤_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization as Localization hiding (rec)
open import Cubical.HITs.Nullification hiding (rec ; elim)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.S1 hiding (rec ; elim)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Interval
open import DPRLR.Simplicial.Segal
open import DPRLR.Simplicial.Shapes using (Λ²₁ ; Δ² ; spine₂)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
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

𝕊-elim≃ : {X : Type ℓ} → (Y : Type ℓ') → (𝕊 Y → X) ≃ 𝕊-cocone X Y
𝕊-elim≃ {X = X} Y = isoToEquiv 𝕊-elim
  where
  𝕊-elim : Iso (𝕊 Y → X) (𝕊-cocone X Y)
  Iso.fun 𝕊-elim k =
    (k (inr false) , k (inr true))
    , λ y →
        (λ i → k (inl (y , i)))
        , cong k (push (y , false))
        , cong k (push (y , true))
  Iso.inv 𝕊-elim (_ , q) (inl (y , i)) =
    hom-path (q y) i
  Iso.inv 𝕊-elim ((x , x') , q) (inr false) = x
  Iso.inv 𝕊-elim ((x , x') , q) (inr true) = x'
  Iso.inv 𝕊-elim (_ , q) (push (y , false) i) =
    left-endpoint (q y) i
  Iso.inv 𝕊-elim (_ , q) (push (y , true) i) =
    right-endpoint (q y) i
  Iso.rightInv 𝕊-elim (_ , q) = refl
  Iso.leftInv 𝕊-elim k i (inl (y , j)) = k (inl (y , j))
  Iso.leftInv 𝕊-elim k i (inr false) = k (inr false)
  Iso.leftInv 𝕊-elim k i (inr true) = k (inr true)
  Iso.leftInv 𝕊-elim k i (push (y , false) j) = k (push (y , false) j)
  Iso.leftInv 𝕊-elim k i (push (y , true) j) = k (push (y , true) j)

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

isPreorder→isSegal :
  {X : Type ℓ}
  → isPreorder X
  → isSegal X
isPreorder→isSegal isPreorderX =
  invEq isSegal≃isEquiv-spine (toIsEquiv _ (isPreorderX segal))

isSetThinSegal→isPreorder :
  {X : Type ℓ} → isSet X → isThin X → isSegal X → isPreorder X
isSetThinSegal→isPreorder setX thinX segalX segal =
  fromIsEquiv _ (equivFun isSegal≃isEquiv-spine segalX)
isSetThinSegal→isPreorder setX thinX segalX thin = 
  transport (sym isBoundarySeparated≡isThin) thinX tt
isSetThinSegal→isPreorder {X = X} setX thinX segalX hset =
  fromIsEquiv _ (equivIsEquiv
    (compEquiv (UnitToType≃ X)
      (_ , toIsEquiv _ (transport (sym isS¹Null≡isSet) setX tt))))

rec-unique :
  isPreorder Y
  → (f g : ∥ X ∥ᴾ → Y)
  → ((x : X) → f (ηᴾ x) ≡ g (ηᴾ x))
  → (z : ∥ X ∥ᴾ) → f z ≡ g z
rec-unique {X = X} isPreorderY f g p = elim
  where
  Q : ∥ X ∥ᴾ → Type _
  Q z = f z ≡ g z

  Q-isProp : (z : ∥ X ∥ᴾ) → isProp (Q z)
  Q-isProp z = isPreorder→isSet isPreorderY (f z) (g z)

  elim : (z : ∥ X ∥ᴾ) → Q z

  boundary-agreement :
    (α : Requirements) (w : Sᴾ α → ∥ X ∥ᴾ)
    → (f ∘ ext α w) ∘ Fᴾ α ≡ (g ∘ ext α w) ∘ Fᴾ α
  boundary-agreement α w = funExt λ s →
      f (ext α w (Fᴾ α s))
    ≡⟨ cong f (isExt α w s) ⟩
      f (w s)
    ≡⟨ elim (w s) ⟩
      g (w s)
    ≡⟨ cong g (sym (isExt α w s)) ⟩
      g (ext α w (Fᴾ α s))
    ∎

  extend-agreement :
    (α : Requirements) (w : Sᴾ α → ∥ X ∥ᴾ) (t : Tᴾ α)
    → Q (ext α w t)
  extend-agreement α w =
    funExt⁻ (secCong (isPreorderY α) (f ∘ ext α w) (g ∘ ext α w)
      .fst (boundary-agreement α w))

  elim ∣ x ∣ = p x
  elim (ext α w t) = extend-agreement α w t
  elim (isExt α w s i) =
    isProp→PathP (λ i → Q-isProp (isExt α w s i))
      (extend-agreement α w (Fᴾ α s)) (elim (w s)) i
  elim (≡ext α u v q t i) =
    isProp→PathP (λ i → Q-isProp (≡ext α u v q t i))
      (elim (u t)) (elim (v t)) i
  elim (≡isExt α u v q s i j) =
    isOfHLevel→isOfHLevelDep 2 {B = Q}
      (λ z → isProp→isSet (Q-isProp z))
      (elim (u (Fᴾ α s))) (elim (v (Fᴾ α s)))
      (isProp→PathP (λ j → Q-isProp (≡ext α u v q (Fᴾ α s) j))
        (elim (u (Fᴾ α s))) (elim (v (Fᴾ α s))))
      (λ j → elim (q s j))
      (≡isExt α u v q s) i j

ηᴾ-universal : isPreorder Y → (∥ X ∥ᴾ → Y) ≃ (X → Y)
ηᴾ-universal localY = isoToEquiv
  (iso (_∘ ηᴾ) (rec localY) (λ _ → refl)
    (λ f → funExt (rec-unique localY _ f (λ _ → refl))))

rec-unique₂ : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  → isPreorder Z → (f g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z)
  → ((x : X) (y : Y) → f (ηᴾ x) (ηᴾ y) ≡ g (ηᴾ x) (ηᴾ y))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) → f x y ≡ g x y
rec-unique₂ localZ f g p x y =
  rec-unique localZ (λ x → f x y) (λ x → g x y)
    (λ x → rec-unique localZ (f (ηᴾ x)) (g (ηᴾ x)) (p x) y) x

rec-unique₃ : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} {W : Type ℓ'''}
  → isPreorder W → (f g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → ∥ Z ∥ᴾ → W)
  → ((x : X) (y : Y) (z : Z) → f (ηᴾ x) (ηᴾ y) (ηᴾ z) ≡ g (ηᴾ x) (ηᴾ y) (ηᴾ z))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) (z : ∥ Z ∥ᴾ) → f x y z ≡ g x y z
rec-unique₃ localW f g p x y z =
  rec-unique localW (λ x → f x y z) (λ x → g x y z)
    (λ x → rec-unique₂ localW (f (ηᴾ x)) (g (ηᴾ x)) (p x) y z) x

rec-uniqueP : {X : Type ℓ} {Y : I → Type ℓ'}
  → isPreorder (Y i1)
  → (f : ∥ X ∥ᴾ → Y i0) (g : ∥ X ∥ᴾ → Y i1)
  → ((x : X) → PathP Y (f (ηᴾ x)) (g (ηᴾ x)))
  → (x : ∥ X ∥ᴾ) → PathP Y (f x) (g x)
rec-uniqueP {Y = Y} localY f g p x = toPathP
  (rec-unique localY (λ x → transport (λ i → Y i) (f x)) g
    (λ x → fromPathP (p x)) x)

rec-uniqueP₂ : {X : Type ℓ} {Y : Type ℓ'} {Z : I → Type ℓ''}
  → isPreorder (Z i1)
  → (f : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z i0) (g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z i1)
  → ((x : X) (y : Y) → PathP Z (f (ηᴾ x) (ηᴾ y)) (g (ηᴾ x) (ηᴾ y)))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) → PathP Z (f x y) (g x y)
rec-uniqueP₂ {Z = Z} localZ f g p x y = toPathP
  (rec-unique₂ localZ (λ x y → transport (λ i → Z i) (f x y)) g
    (λ x y → fromPathP (p x y)) x y)

isPreorder≃ : {X : Type ℓ} {Y : Type ℓ'} → X ≃ Y → isPreorder X → isPreorder Y
isPreorder≃ e localX α =
  fromIsEquiv _ (subst isEquiv (funExt λ f → funExt λ s → secEq e (f (Fᴾ α s))) (equivIsEquiv
    (compEquiv (equivΠCod λ _ → invEquiv e)
      (compEquiv (_ , toIsEquiv _ (localX α))
        (equivΠCod λ _ → e)))))

isPreorder× : {X : Type ℓ} {Y : Type ℓ'}
  → isPreorder X → isPreorder Y → isPreorder (X × Y)
isPreorder× {X = X} {Y = Y} localX localY α =
  fromIsEquiv _ (equivIsEquiv
    (compEquiv (split (Tᴾ α))
      (compEquiv (≃-× (_ , toIsEquiv _ (localX α)) (_ , toIsEquiv _ (localY α)))
        (invEquiv (split (Sᴾ α))))))
  where
  split : (W : Type₀) → (W → X × Y) ≃ ((W → X) × (W → Y))
  split W = isoToEquiv (iso
    (λ f → (fst ∘ f) , (snd ∘ f))
    (λ f x → f .fst x , f .snd x)
    (λ _ → refl) (λ _ → refl))
