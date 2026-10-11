module DPRLR.Simplicial.PreorderLocalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
  using (isEquiv[equivFunA≃B∘f]→isEquiv[f] ; isEquiv[f∘equivFunA≃B]→isEquiv[f] ; congEquiv)
open import Cubical.Foundations.Equiv.Fiberwise using (fiberEquiv)
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure using (TypeWithStr ; str)
open import Cubical.Foundations.Structure using () renaming (⟨_⟩ to ⌞_⌟) public
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv using (funExtEquiv)
open import Cubical.Data.Bool hiding (elim ; _≤_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Localization as Localization hiding (rec)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.S1 hiding (rec ; elim)

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Interval
open import DPRLR.Simplicial.Segal
open import DPRLR.Simplicial.PathTransitive using (isSegal≡isPathTransitive)
open import DPRLR.Simplicial.Shapes using (Λ² ; Δ² ; ι-horn)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓ'''' : Level
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
  Σ[ x ∈ X ] Σ[ x' ∈ X ] (Y → x ≤ x')

𝕊-elim≃ : {X : Type ℓ} → (Y : Type ℓ') → (𝕊 Y → X) ≃ 𝕊-cocone X Y
𝕊-elim≃ {X = X} Y = isoToEquiv 𝕊-elim
  where
  𝕊-elim : Iso (𝕊 Y → X) (𝕊-cocone X Y)
  Iso.fun 𝕊-elim k =
    k (inr false) , k (inr true)
    , λ y →
        (λ i → k (inl (y , i)))
        , cong k (push (y , false))
        , cong k (push (y , true))
  Iso.inv 𝕊-elim (_ , _ , q) (inl (y , i)) =
    hom-path (q y) i
  Iso.inv 𝕊-elim (x , x' , q) (inr false) = x
  Iso.inv 𝕊-elim (x , x' , q) (inr true) = x'
  Iso.inv 𝕊-elim (_ , _ , q) (push (y , false) i) =
    left-endpoint (q y) i
  Iso.inv 𝕊-elim (_ , _ , q) (push (y , true) i) =
    right-endpoint (q y) i
  Iso.rightInv 𝕊-elim (_ , _ , q) = refl
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
  isBoundarySeparated→isThin : isBoundarySeparated X → isThin X
  isBoundarySeparated→isThin separated x y p q =
    p           ≡⟨ sym (common-path≡pair false) ⟩
    common-path ≡⟨ common-path≡pair true ⟩
    q ∎
    where
    cocones≃ : 𝕊-cocone X Unit ≃ 𝕊-cocone X Bool
    cocones≃ =
      𝕊-cocone X Unit
        ≃⟨ invEquiv (𝕊-elim≃ Unit) ⟩
      (𝕊 Unit → X)
        ≃⟨ _ , toIsEquiv _ (separated tt) ⟩
      (𝕊 Bool → X)
        ≃⟨ 𝕊-elim≃ Bool ⟩
      𝕊-cocone X Bool ■

    paths≃ : (Unit → x ≤ y) ≃ (Bool → x ≤ y)
    paths≃ = _ , fiberEquiv _ _ _
      (fiberEquiv _ _ _ (equivIsEquiv cocones≃) x) y

    pair : Bool → x ≤ y
    pair false = p
    pair true = q

    common-path : x ≤ y
    common-path = invEq paths≃ pair tt

    common-path≡pair : (b : Bool) → common-path ≡ pair b
    common-path≡pair = funExt⁻ (secEq paths≃ pair)

  isThin→isBoundarySeparated : isThin X → isBoundarySeparated X
  isThin→isBoundarySeparated thin _ = fromIsEquiv _ $
    isEquiv[equivFunA≃B∘f]→isEquiv[f] _ (𝕊-elim≃ Bool) $ equivIsEquiv $
      (𝕊 Unit → X)
    ≃⟨ 𝕊-elim≃ Unit ⟩
      𝕊-cocone X Unit
    ≃⟨ Σ-cong-equiv-snd (λ x → Σ-cong-equiv-snd (λ y →
        propBiimpl→Equiv (isPropΠ λ _ → thin x y) (isPropΠ λ _ → thin x y)
          (λ f _ → f tt) (λ f _ → f true))) ⟩
      𝕊-cocone X Bool
    ■

isS¹Local≡isSet :
  {X : Type ℓ} → isLocal {A = Unit} (const (terminal S¹)) X ≡ isSet X
isS¹Local≡isSet {X = X} =
  hPropExt (isPropΠ λ _ → isPropIsPathSplitEquiv _) isPropIsSet
    isLocal→isSet isSet→isLocal
  where
  isLocal→isSet : isLocal {A = Unit} (const (terminal S¹)) X → isSet X
  isLocal→isSet localX = isOfHLevelΩ→isOfHLevel 0 loops-isProp
    where
    constant-loops : X ≃ (Σ[ x ∈ X ] (x ≡ x))
    constant-loops =
        X
      ≃⟨ invEquiv (UnitToType≃ X) ⟩
        (Unit → X)
      ≃⟨ _ , toIsEquiv _ (localX tt) ⟩
        (S¹ → X)
      ≃⟨ isoToEquiv IsoFunSpaceS¹ ⟩
        Σ[ x ∈ X ] (x ≡ x)
      ■

    K : (x : X) (p : x ≡ x) → p ≡ refl
    K x p = J (λ (y , q) _ → q ≡ refl) refl constant-loop-path
      where
      constant-loop-path : (invEq constant-loops (x , p) , refl) ≡ (x , p)
      constant-loop-path = secEq constant-loops (x , p)

    loops-isProp : (x : X) → isProp (x ≡ x)
    loops-isProp x p q = K x p ∙ sym (K x q)

  isSet→isLocal : isSet X → isLocal {A = Unit} (const (terminal S¹)) X
  isSet→isLocal setX _ = fromIsEquiv (_∘ terminal S¹) (isoToIsEquiv S¹→XIso)
    where
    S¹→XIso : Iso (Unit → X) (S¹ → X)
    S¹→XIso .Iso.fun f = f ∘ terminal S¹
    S¹→XIso .Iso.inv f _ = f base
    S¹→XIso .Iso.rightInv f = funExt (toPropElim (λ _ → setX _ _) refl)
    S¹→XIso .Iso.leftInv f = funExt λ { tt → refl }

data Requirements : Type₀ where
  segal thin hset : Requirements

Sᴾ : Requirements → Type₀
Sᴾ segal = Λ²
Sᴾ thin = 𝕊 Bool
Sᴾ hset = S¹

Tᴾ : Requirements → Type₀
Tᴾ segal = Δ²
Tᴾ thin = 𝕊 Unit
Tᴾ hset = Unit

Fᴾ : (α : Requirements) → Sᴾ α → Tᴾ α
Fᴾ segal = ι-horn
Fᴾ thin = 𝕊map (λ (_ : Bool) → tt)
Fᴾ hset = λ _ → tt

isPreorder : Type ℓ → Type ℓ
isPreorder = isLocal Fᴾ

∥_∥ᴾ : Type ℓ → Type ℓ
∥_∥ᴾ = Localize Fᴾ

ηᴾ : X → ∥ X ∥ᴾ
ηᴾ = ∣_∣

∥∥ᴾ-isPreorder : {X : Type ℓ} → isPreorder ∥ X ∥ᴾ
∥∥ᴾ-isPreorder = isLocal-Localize Fᴾ _

isPropIsPreorder : {X : Type ℓ} → isProp (isPreorder X)
isPropIsPreorder =
  isPropΠ λ _ → isPropIsPathSplitEquiv _

Preorder : (ℓ : Level) → Type (ℓ-suc ℓ)
Preorder ℓ = TypeWithStr ℓ isPreorder

recᴾ : isPreorder Y → (X → Y) → ∥ X ∥ᴾ → Y
recᴾ = Localization.rec

recᴾ₂ : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  → isPreorder Z → (X → Y → Z) → ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z
recᴾ₂ localZ f x y = recᴾ localZ (λ x₀ → recᴾ localZ (f x₀) y) x

recᴾ₃ : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} {W : Type ℓ'''}
  → isPreorder W → (X → Y → Z → W) → ∥ X ∥ᴾ → ∥ Y ∥ᴾ → ∥ Z ∥ᴾ → W
recᴾ₃ localW f x y z = recᴾ localW (λ x₀ → recᴾ₂ localW (f x₀) y z) x

open isPathSplitEquiv

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

opaque
  isPreorder→isThin :
    {X : Type ℓ}
    → isPreorder X
    → isThin X
  isPreorder→isThin isPreorderX =
    transport isBoundarySeparated≡isThin λ _ → isPreorderX thin

opaque
  isPreorder→isSet :
    {X : Type ℓ}
    → isPreorder X
    → isSet X
  isPreorder→isSet isPreorderX =
    transport isS¹Local≡isSet λ _ → isPreorderX hset

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

opaque
  isPreorder→isSegal :
    {X : Type ℓ}
    → isPreorder X
    → isSegal X
  isPreorder→isSegal isPreorderX =
    transport (sym isSegal≡isPathTransitive) (λ _ → isPreorderX segal)

isSetThinSegal→isPreorder :
  {X : Type ℓ} → isSet X → isThin X → isSegal X → isPreorder X
isSetThinSegal→isPreorder setX thinX segalX segal =
  transport isSegal≡isPathTransitive segalX tt
isSetThinSegal→isPreorder setX thinX segalX thin =
  transport (sym isBoundarySeparated≡isThin) thinX tt
isSetThinSegal→isPreorder setX thinX segalX hset =
  transport (sym isS¹Local≡isSet) setX tt

recᴾ-unique :
  isPreorder Y
  → (f g : ∥ X ∥ᴾ → Y)
  → ((x : X) → f (ηᴾ x) ≡ g (ηᴾ x))
  → (z : ∥ X ∥ᴾ) → f z ≡ g z
recᴾ-unique {X = X} isPreorderY f g p = elim
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
  (iso (_∘ ηᴾ) (recᴾ localY) (λ _ → refl)
    (λ f → funExt (recᴾ-unique localY _ f (λ _ → refl))))

recᴾ-unique₂ : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  → isPreorder Z → (f g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z)
  → ((x : X) (y : Y) → f (ηᴾ x) (ηᴾ y) ≡ g (ηᴾ x) (ηᴾ y))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) → f x y ≡ g x y
recᴾ-unique₂ localZ f g p x y =
  recᴾ-unique localZ (λ x → f x y) (λ x → g x y)
    (λ x → recᴾ-unique localZ (f (ηᴾ x)) (g (ηᴾ x)) (p x) y) x

recᴾ-unique₃ : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} {W : Type ℓ'''}
  → isPreorder W → (f g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → ∥ Z ∥ᴾ → W)
  → ((x : X) (y : Y) (z : Z) → f (ηᴾ x) (ηᴾ y) (ηᴾ z) ≡ g (ηᴾ x) (ηᴾ y) (ηᴾ z))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) (z : ∥ Z ∥ᴾ) → f x y z ≡ g x y z
recᴾ-unique₃ localW f g p x y z =
  recᴾ-unique localW (λ x → f x y z) (λ x → g x y z)
    (λ x → recᴾ-unique₂ localW (f (ηᴾ x)) (g (ηᴾ x)) (p x) y z) x

recᴾ-unique₄ : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''} {W : Type ℓ'''} {V : Type ℓ''''}
  → isPreorder V → (f g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → ∥ Z ∥ᴾ → ∥ W ∥ᴾ → V)
  → ((x : X) (y : Y) (z : Z) (w : W)
      → f (ηᴾ x) (ηᴾ y) (ηᴾ z) (ηᴾ w) ≡ g (ηᴾ x) (ηᴾ y) (ηᴾ z) (ηᴾ w))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) (z : ∥ Z ∥ᴾ) (w : ∥ W ∥ᴾ) → f x y z w ≡ g x y z w
recᴾ-unique₄ localV f g p x y z w =
  recᴾ-unique localV (λ x → f x y z w) (λ x → g x y z w)
    (λ x → recᴾ-unique₃ localV (f (ηᴾ x)) (g (ηᴾ x)) (p x) y z w) x

recᴾ-uniqueP : {X : Type ℓ} {Y : I → Type ℓ'}
  → isPreorder (Y i1)
  → (f : ∥ X ∥ᴾ → Y i0) (g : ∥ X ∥ᴾ → Y i1)
  → ((x : X) → PathP Y (f (ηᴾ x)) (g (ηᴾ x)))
  → (x : ∥ X ∥ᴾ) → PathP Y (f x) (g x)
recᴾ-uniqueP {Y = Y} localY f g p x = toPathP
  (recᴾ-unique localY (λ x → transport (λ i → Y i) (f x)) g
    (λ x → fromPathP (p x)) x)

recᴾ-uniqueP₂ : {X : Type ℓ} {Y : Type ℓ'} {Z : I → Type ℓ''}
  → isPreorder (Z i1)
  → (f : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z i0) (g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z i1)
  → ((x : X) (y : Y) → PathP Z (f (ηᴾ x) (ηᴾ y)) (g (ηᴾ x) (ηᴾ y)))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) → PathP Z (f x y) (g x y)
recᴾ-uniqueP₂ {Z = Z} localZ f g p x y = toPathP
  (recᴾ-unique₂ localZ (λ x y → transport (λ i → Z i) (f x y)) g
    (λ x y → fromPathP (p x y)) x y)

recᴾ-hom : {X : Type ℓ} {Y : Type ℓ'}
  → isPreorder Y → (f g : ∥ X ∥ᴾ → Y)
  → ((x : X) → f (ηᴾ x) ≤ g (ηᴾ x))
  → (x : ∥ X ∥ᴾ) → f x ≤ g x
recᴾ-hom {X = X} {Y = Y} localY f g h x =
  line x
  , recᴾ-unique localY (λ x → line x 𝟎) f (λ x → left-endpoint (h x)) x
  , recᴾ-unique localY (λ x → line x 𝟏) g (λ x → right-endpoint (h x)) x
  where
  line : ∥ X ∥ᴾ → 𝟚 → Y
  line = recᴾ (isPreorderΠ λ _ → localY) (λ x → hom-path (h x))

recᴾ-hom₂ : {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  → isPreorder Z → (f g : ∥ X ∥ᴾ → ∥ Y ∥ᴾ → Z)
  → ((x : X) (y : Y) → f (ηᴾ x) (ηᴾ y) ≤ g (ηᴾ x) (ηᴾ y))
  → (x : ∥ X ∥ᴾ) (y : ∥ Y ∥ᴾ) → f x y ≤ g x y
recᴾ-hom₂ localZ f g h x y =
  recᴾ-hom localZ (λ x → f x y) (λ x → g x y)
    (λ x → recᴾ-hom localZ (f (ηᴾ x)) (g (ηᴾ x)) (h x) y) x

isPreorder≃ : {X : Type ℓ} {Y : Type ℓ'} → X ≃ Y → isPreorder X → isPreorder Y
isPreorder≃ e localX α = fromIsEquiv _
  (isEquiv[f∘equivFunA≃B]→isEquiv[f] _ (equivΠCod λ _ → e)
    (compEquiv (_ , toIsEquiv _ (localX α)) (equivΠCod λ _ → e) .snd))

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

isPreorderEqualizer : {X : Type ℓ} {Y : Type ℓ'} (f g : X → Y)
  → isPreorder X → isPreorder Y → isPreorder (Σ X (λ x → f x ≡ g x))
isPreorderEqualizer {X = X} {Y = Y} f g localX localY α =
  fromIsEquiv _ (equivIsEquiv $
    ( Tᴾ α → Σ X (λ x → f x ≡ g x))
    ≃⟨ split (Tᴾ α) ⟩
      Σ (Tᴾ α → X) (λ h → (w : Tᴾ α) → f (h w) ≡ g (h w))
    ≃⟨ Σ-cong-equiv (_ , toIsEquiv _ (localX α)) (λ h →
        ((w : Tᴾ α) → f (h w) ≡ g (h w))
          ≃⟨ funExtEquiv ⟩
        (f ∘ h ≡ g ∘ h)
          ≃⟨ congEquiv (_ , toIsEquiv _ (localY α)) ⟩
        (f ∘ h ∘ Fᴾ α ≡ g ∘ h ∘ Fᴾ α)
          ≃⟨ invEquiv funExtEquiv ⟩
        ((w : Sᴾ α) → f (h (Fᴾ α w)) ≡ g (h (Fᴾ α w))) ■) ⟩
      Σ (Sᴾ α → X) (λ h → (w : Sᴾ α) → f (h w) ≡ g (h w))
    ≃⟨ invEquiv (split (Sᴾ α)) ⟩
      (Sᴾ α → Σ X (λ x → f x ≡ g x))
    ■)
  where
  split : (W : Type₀)
    → (W → Σ X (λ x → f x ≡ g x)) ≃ Σ (W → X) (λ h → (w : W) → f (h w) ≡ g (h w))
  split W = isoToEquiv (iso
    (λ k → fst ∘ k , snd ∘ k)
    (λ (h , p) w → h w , p w)
    (λ _ → refl) (λ _ → refl))
