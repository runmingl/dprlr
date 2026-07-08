module DPRLR.Simplicial.Contravariant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Interval
open import DPRLR.Simplicial.Discrete
open import DPRLR.Simplicial.FunctionExtensionality
open import DPRLR.Simplicial.ProductExtensionality

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ
    X : Type ℓ''
    C : A → Type ℓ'
    D : A → Type ℓ''

record isContravariant {A : Type ℓ} (C : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    contrav-lift :
      {x y : A} (f : x ≤ y) (v : C y)
      → isContr (Σ (C x) (λ u → C ⊢ u ≤[ f ] v))

open isContravariant public

contrav-transport :
  {C : A → Type ℓ'} → isContravariant C
  → {x y : A} → x ≤ y → C y → C x
contrav-transport c f v = contrav-lift c f v .fst .fst

contravariant-lift-hom :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x y : A} (f : x ≤ y) (v : C y)
  → C ⊢ contrav-transport c f v ≤[ f ] v
contravariant-lift-hom c f v = contrav-lift c f v .fst .snd

contravariant-universal-to :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x y : A} {f : x ≤ y} {u : C x} {v : C y}
  → C ⊢ u ≤[ f ] v
  → u ≡ contrav-transport c f v
contravariant-universal-to c {f = f} {u = u} {v = v} q =
  cong fst
    (isContr→isProp
      (contrav-lift c f v)
      (u , q)
      (contrav-lift c f v .fst))

contravariant-universal-from :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x y : A} {f : x ≤ y} {u : C x} {v : C y}
  → u ≡ contrav-transport c f v
  → C ⊢ u ≤[ f ] v
contravariant-universal-from c {f = f} {v = v} u≡f*v =
  subst (λ u → _ ⊢ u ≤[ f ] v) (sym u≡f*v)
    (contravariant-lift-hom c f v)

contravariant-universal-Iso :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x y : A} {f : x ≤ y} {u : C x} {v : C y}
  → Iso (C ⊢ u ≤[ f ] v) (u ≡ contrav-transport c f v)
Iso.fun (contravariant-universal-Iso c) =
  contravariant-universal-to c
Iso.inv (contravariant-universal-Iso c) =
  contravariant-universal-from c
Iso.rightInv
  (contravariant-universal-Iso {C = C} c {x = x} {f = f} {u = u} {v = v})
  p =
  cong (cong fst) (total-isSet _ _ α β)
  where
  Fiber : C x → Type _
  Fiber u =
    C ⊢ u ≤[ f ] v

  total-isSet : isSet (Σ (C x) Fiber)
  total-isSet =
    isProp→isSet (isContr→isProp (contrav-lift c f v))

  center : Σ (C x) Fiber
  center =
    contrav-lift c f v .fst

  q : Fiber u
  q =
    contravariant-universal-from c p

  α : (u , q) ≡ center
  α =
    isContr→isProp (contrav-lift c f v) (u , q) center

  β : (u , q) ≡ center
  β =
    sym (ΣPathP (sym p , subst-filler Fiber (sym p) (snd center)))
Iso.leftInv
  (contravariant-universal-Iso {C = C} c {x = x} {f = f} {u = u} {v = v})
  q =
  fromPathP (snd (PathPΣ (sym α)))
  where
  Fiber : C x → Type _
  Fiber u =
    C ⊢ u ≤[ f ] v

  center : Σ (C x) Fiber
  center =
    contrav-lift c f v .fst

  α : (u , q) ≡ center
  α =
    isContr→isProp (contrav-lift c f v) (u , q) center

contravariant-universal≃ :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x y : A} {f : x ≤ y} {u : C x} {v : C y}
  → (C ⊢ u ≤[ f ] v) ≃ (u ≡ contrav-transport c f v)
contravariant-universal≃ c =
  isoToEquiv (contravariant-universal-Iso c)

contravariant-universal-to-isEquiv :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x y : A} {f : x ≤ y} {u : C x} {v : C y}
  → isEquiv (contravariant-universal-to c {f = f} {u = u} {v = v})
contravariant-universal-to-isEquiv c =
  contravariant-universal≃ c .snd

contravariant-transport-refl :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x : A} (v : C x)
  → contrav-transport c (hom-refl x) v ≡ v
contravariant-transport-refl c {x = x} v =
  sym
    (contravariant-universal-to c
      {f = hom-refl x}
      (hom-refl v))

contravariant-fiber-Hom≃Path :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x : A} (u v : C x)
  → (u ≤ v) ≃ (u ≡ v)
contravariant-fiber-Hom≃Path c {x = x} u v =
  compEquiv
    (contravariant-universal≃ c {f = hom-refl x} {u = u} {v = v})
    ((_∙ contravariant-transport-refl c v)
    , compPathr-isEquiv (contravariant-transport-refl c v))

contravariant-fiber-Hom≃Path-idtoarr :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x : A} {u v : C x}
  → (p : u ≡ v)
  → contravariant-fiber-Hom≃Path c u v .fst (idtoarr p) ≡ p
contravariant-fiber-Hom≃Path-idtoarr c {x = x} {u = u} =
  J
    (λ v p → contravariant-fiber-Hom≃Path c u v .fst (idtoarr p) ≡ p)
    (cong (contravariant-fiber-Hom≃Path c u u .fst) idtoarr-refl
      ∙ rCancel (contravariant-universal-to c {f = hom-refl x} (hom-refl u)))

contravariant-fiber-idtoarr≡inv :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x : A} {u v : C x}
  → (p : u ≡ v)
  → idtoarr p ≡ invEq (contravariant-fiber-Hom≃Path c u v) p
contravariant-fiber-idtoarr≡inv c {u = u} {v = v} p =
  isoFunInjective
    (equivToIso (contravariant-fiber-Hom≃Path c u v))
    (idtoarr p)
    (invEq (contravariant-fiber-Hom≃Path c u v) p)
    (contravariant-fiber-Hom≃Path-idtoarr c p
      ∙ sym (secEq (contravariant-fiber-Hom≃Path c u v) p))

contravariant-fiber-isDiscrete :
  {C : A → Type ℓ'} (c : isContravariant C)
  → (x : A)
  → isDiscrete (C x)
contravariant-fiber-isDiscrete c x u v =
  subst isEquiv
    (sym (funExt (contravariant-fiber-idtoarr≡inv c)))
    (invEquiv (contravariant-fiber-Hom≃Path c u v) .snd)

HomP-isProp-contravariant :
  {C : A → Type ℓ'} (c : isContravariant C)
  → ((x : A) → isSet (C x))
  → {x y : A} (f : x ≤ y) (u : C x) (v : C y)
  → isProp (C ⊢ u ≤[ f ] v)
HomP-isProp-contravariant {C = C} c Cset {x = x} f u v =
  isPropRetract to from from-to fiber-prop
  where
  Total : Type _
  Total =
    Σ (C x) (λ u′ → C ⊢ u′ ≤[ f ] v)

  Fiber : Type _
  Fiber =
    Σ Total (λ w → fst w ≡ u)

  to :
    C ⊢ u ≤[ f ] v
    → Fiber
  to q =
    (u , q) , refl

  from :
    Fiber
    → C ⊢ u ≤[ f ] v
  from ((u′ , q) , p) =
    subst (λ z → C ⊢ z ≤[ f ] v) p q

  from-to :
    (q : C ⊢ u ≤[ f ] v)
    → from (to q) ≡ q
  from-to q =
    substRefl {B = λ z → C ⊢ z ≤[ f ] v} q

  fiber-prop : isProp Fiber
  fiber-prop =
    isPropΣ
      (isContr→isProp (contrav-lift c f v))
      (λ w → Cset x (fst w) u)

contravariant-Lift :
  {A : Type ℓ} {C : A → Type ℓ'}
  → isContravariant C
  → isContravariant (λ x → Lift {j = ℓ''} (C x))
contravariant-Lift {A = A} {C = C} c .contrav-lift {x = x} f v =
  isContrRetract to from from-to (contrav-lift c f (lower v))
  where
  LiftC : A → Type _
  LiftC x = Lift (C x)

  lower-HomP :
    {x y : A} {h : x ≤ y}
    {u : LiftC x} {v : LiftC y}
    → LiftC ⊢ u ≤[ h ] v
    → C ⊢ lower u ≤[ h ] lower v
  lower-HomP q =
    (λ i → lower (q .fst i))
    , (λ i → lower (q .snd .fst i))
    , (λ i → lower (q .snd .snd i))

  lift-HomP :
    {x y : A} {h : x ≤ y}
    {u : C x} {v : C y}
    → C ⊢ u ≤[ h ] v
    → LiftC ⊢ lift u ≤[ h ] lift v
  lift-HomP q =
    (λ i → lift (q .fst i))
    , (λ i → lift (q .snd .fst i))
    , (λ i → lift (q .snd .snd i))

  LiftTotal : Type _
  LiftTotal =
    Σ (LiftC x) (λ u → LiftC ⊢ u ≤[ f ] v)

  Total : Type _
  Total =
    Σ (C x) (λ u → C ⊢ u ≤[ f ] lower v)

  to : LiftTotal → Total
  to (u , q) =
    lower u , lower-HomP q

  from : Total → LiftTotal
  from (u , q) =
    lift u , lift-HomP q

  from-to : (w : LiftTotal) → from (to w) ≡ w
  from-to w = refl

contravariant-reindex :
  {A : Type ℓ} {B : Type ℓ'} {C : B → Type ℓ''}
  → (g : A → B)
  → isContravariant C
  → isContravariant (λ x → C (g x))
contravariant-reindex g c .contrav-lift f v =
  contrav-lift c (hom-map g f) v

contravariant-discrete :
  {A : Type ℓ} {B : Type ℓ'}
  → isDiscrete B
  → isContravariant (λ (_ : A) → B)
contravariant-discrete d .contrav-lift f v =
  hom-to-isContr d v

contravariant-Σ :
  {C : A → Type ℓ'} {D : (a : A) → C a → Type ℓ''}
  → isContravariant C
  → isContravariant (λ au → D (fst au) (snd au))
  → isContravariant (λ a → Σ (C a) (D a))
contravariant-Σ {C = C} {D = D} c d .contrav-lift {x = x} {y = y} f (vC , vD) =
  isContrRetract to from from-to component-lifts
  where
  TotalLift : Type _
  TotalLift =
    Σ (Σ (C x) (D x))
      (λ u → (λ a → Σ (C a) (D a)) ⊢ u ≤[ f ] (vC , vD))

  ComponentLifts : Type _
  ComponentLifts =
    Σ (Σ (C x) (λ uC → C ⊢ uC ≤[ f ] vC))
      (λ uh →
        Σ (D x (fst uh))
          (λ uD →
            (λ au → D (fst au) (snd au))
              ⊢ uD ≤[ Σ≤ f (snd uh) ] vD))

  to : TotalLift → ComponentLifts
  to ((uC , uD) , q) =
    (uC , HomPΣ-fst {C = C} {D = D} {f = f} q)
    , (uD , HomPΣ-snd {C = C} {D = D} {f = f} q)

  from : ComponentLifts → TotalLift
  from ((uC , p) , (uD , q)) =
    (uC , uD) , HomPΣ {C = C} {D = D} {f = f} p q

  from-to : (w : TotalLift) → from (to w) ≡ w
  from-to ((uC , uD) , q) = refl

  component-lifts : isContr ComponentLifts
  component-lifts =
    isContrΣ (contrav-lift c f vC)
      (λ uh → contrav-lift d (Σ≤ f (snd uh)) vD)

ΣLift-idtoarr-isContr :
  {B : Type ℓ''} {C : B → A → Type ℓ'}
  → ((b : B) → isContravariant (C b))
  → {x y : A} (f : x ≤ y)
  → {b₀ b₁ : B}
  → (p : b₀ ≡ b₁)
  → (v : C b₁ y)
  → isContr (Σ (C b₀ x) (λ u → ΣLift {C = C} f (idtoarr p) u v))
ΣLift-idtoarr-isContr {C = C} c {x = x} {y = y} f {b₀ = b₀} p =
  J
    (λ b₁ p →
      (v : C b₁ y)
      → isContr (Σ (C b₀ x) (λ u → ΣLift {C = C} f (idtoarr p) u v)))
    base
    p
  where
  base :
    (v : C b₀ y)
    → isContr (Σ (C b₀ x) (λ u → ΣLift {C = C} f (idtoarr refl) u v))
  base v =
    subst
      (λ h → isContr (Σ (C b₀ x) (λ u → ΣLift {C = C} f h u v)))
      (sym (idtoarr-refl {x = b₀}))
      (contrav-lift (c b₀) f v)

ΣLift-isContr :
  {B : Type ℓ''} {C : B → A → Type ℓ'}
  → isDiscrete B
  → ((b : B) → isContravariant (C b))
  → {x y : A} (f : x ≤ y)
  → {b₀ b₁ : B}
  → (h : b₀ ≤ b₁)
  → (v : C b₁ y)
  → isContr (Σ (C b₀ x) (λ u → ΣLift {C = C} f h u v))
ΣLift-isContr {C = C} d c {x = x} f {b₀ = b₀} h v =
  subst
    (λ h′ → isContr (Σ (C b₀ x) (λ u → ΣLift {C = C} f h′ u v)))
    (idtoarr-arr→path d h)
    (ΣLift-idtoarr-isContr c f (arr→path d h) v)

contravariant-discrete-indexed :
  {B : Type ℓ''} {C : B → A → Type ℓ'}
  → isDiscrete B
  → ((b : B) → isContravariant (C b))
  → isContravariant (λ xb → C (snd xb) (fst xb))
contravariant-discrete-indexed {C = C} d c .contrav-lift {x = x , b₀} {y = y , b₁} r v =
  ΣLift-isContr d c (hom-map fst r) (hom-map snd r) v

contravariant-Σ-discrete :
  {B : Type ℓ''} {C : B → A → Type ℓ'}
  → isDiscrete B
  → ((b : B) → isContravariant (C b))
  → isContravariant (λ x → Σ B (λ b → C b x))
contravariant-Σ-discrete {B = B} {C = C} d c =
  contravariant-Σ
    (contravariant-discrete d)
    (contravariant-discrete-indexed {C = C} d c)

contravariant-× :
  {C : A → Type ℓ'} {D : A → Type ℓ''}
  → isContravariant C
  → isContravariant D
  → isContravariant (λ x → C x × D x)
contravariant-× {C = C} {D = D} c d .contrav-lift {x = x} {y = y} f (vC , vD) =
  isContrRetract to from from-to component-lifts
  where
  ProductLift : Type _
  ProductLift =
    Σ (C x × D x)
      (λ u → (λ z → C z × D z) ⊢ u ≤[ f ] (vC , vD))

  ComponentLifts : Type _
  ComponentLifts =
    Σ (Σ (C x) (λ uC → C ⊢ uC ≤[ f ] vC))
      (λ _ → Σ (D x) (λ uD → D ⊢ uD ≤[ f ] vD))

  to : ProductLift → ComponentLifts
  to ((uC , uD) , q) =
    (uC , HomP×-fst {C = C} {D = D} {f = f} q)
    , (uD , HomP×-snd {C = C} {D = D} {f = f} q)

  from : ComponentLifts → ProductLift
  from ((uC , p) , (uD , q)) =
    (uC , uD) , HomP× {C = C} {D = D} {f = f} p q

  from-to : (w : ProductLift) → from (to w) ≡ w
  from-to ((uC , uD) , q) = refl

  component-lifts : isContr ComponentLifts
  component-lifts =
    isContrΣ (contrav-lift c f vC)
      (λ _ → contrav-lift d f vD)

contravariant-Π :
  {A : Type ℓ} {X : Type ℓ'} {C : A → X → Type ℓ''}
  → ((x : X) → isContravariant (λ a → C a x))
  → isContravariant (λ a → (x : X) → C a x)
contravariant-Π {C = C} c .contrav-lift {x = a₀} {y = a₁} f v =
  isContrRetract to from from-to pointwise-lifts
  where
  ΠLift : Type _
  ΠLift =
    Σ ((x : _) → C a₀ x)
      (λ u → (λ a → (x : _) → C a x) ⊢ u ≤[ f ] v)

  PointwiseLifts : Type _
  PointwiseLifts =
    (x : _) → Σ (C a₀ x) (λ u → (λ a → C a x) ⊢ u ≤[ f ] v x)

  to : ΠLift → PointwiseLifts
  to (u , q) x = u x , HomPΠ-happly {P = C} {h = f} q x

  from : PointwiseLifts → ΠLift
  from w =
    (λ x → w x .fst)
    , HomPΠ {P = C} {h = f} (λ x → w x .snd)

  from-to : (w : ΠLift) → from (to w) ≡ w
  from-to (u , q) = refl

  pointwise-lifts : isContr PointwiseLifts
  pointwise-lifts =
    isContrΠ (λ x → contrav-lift (c x) f (v x))


-- random transport lemmas about contravariance
module _ where 

contravariant-transport-source-subst :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x y z : A}
  → (p : x ≡ y)
  → (f : y ≤ z)
  → (v : C z)
  → subst C p
      (contrav-transport c (subst (λ w → w ≤ z) (sym p) f) v)
    ≡ contrav-transport c f v
contravariant-transport-source-subst {C = C} c {x = x} {z = z} p =
  J
    (λ y p →
      (f : y ≤ z) (v : C z)
      → subst C p
          (contrav-transport c (subst (λ w → w ≤ z) (sym p) f) v)
        ≡ contrav-transport c f v)
    base
    p
  where
  base :
    (f : x ≤ z) (v : C z)
    → subst C refl
        (contrav-transport c (subst (λ w → w ≤ z) (sym refl) f) v)
      ≡ contrav-transport c f v
  base f v =
    cong
      (λ h → subst C refl (contrav-transport c h v))
      (substRefl {B = λ w → w ≤ z} f)
    ∙ substRefl {B = C} (contrav-transport c f v)

contravariant-transport-target-subst :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x y z : A}
  → (p : z ≡ y)
  → (f : x ≤ y)
  → (v : C z)
  → contrav-transport c f (subst C p v)
    ≡ contrav-transport c (subst (λ w → x ≤ w) (sym p) f) v
contravariant-transport-target-subst {C = C} c {x = x} {z = z} p =
  J
    (λ y p →
      (f : x ≤ y) (v : C z)
      → contrav-transport c f (subst C p v)
        ≡ contrav-transport c (subst (λ w → x ≤ w) (sym p) f) v)
    base
    p
  where
  base :
    (f : x ≤ z) (v : C z)
    → contrav-transport c f (subst C refl v)
      ≡ contrav-transport c (subst (λ w → x ≤ w) refl f) v
  base f v =
    cong (contrav-transport c f) (substRefl {B = C} v)
    ∙ cong (λ h → contrav-transport c h v)
        (sym (substRefl {B = λ w → x ≤ w} f))

contravariant-transport-pathP :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x x' y y' : A}
  → (p : x ≡ x')
  → (q : y ≡ y')
  → (f : x ≤ y)
  → (f' : x' ≤ y')
  → (v : C y)
  → subst (λ w → x' ≤ w) (sym q) f'
    ≡ subst (λ w → w ≤ y) p f
  → PathP
      (λ i → C (p i))
      (contrav-transport c f v)
      (contrav-transport c f' (subst C q v))
contravariant-transport-pathP {A = A} {C = C} c {x = x} {y = y} p q =
  J
    (λ (x' : A) (p : x ≡ x') →
      {y' : _}
      → (q : y ≡ y')
      → (f : x ≤ y)
      → (f' : x' ≤ y')
      → (v : C y)
      → subst (λ w → x' ≤ w) (sym q) f'
        ≡ subst (λ w → w ≤ y) p f
      → PathP
          (λ i → C (p i))
          (contrav-transport c f v)
          (contrav-transport c f' (subst C q v)))
    base-source
    p
    q
  where
  base-target :
    (f : x ≤ y)
    → (f' : x ≤ y)
    → (v : C y)
    → subst (λ w → x ≤ w) (sym refl) f'
      ≡ subst (λ w → w ≤ y) refl f
    → PathP
        (λ i → C (refl {x = x} i))
        (contrav-transport c f v)
        (contrav-transport c f' (subst C refl v))
  base-target f f' v h =
    toPathP
      (transportRefl (contrav-transport c f v)
      ∙ cong₂
          (λ h′ v′ → contrav-transport c h′ v′)
          (sym
            (substRefl {B = λ w → w ≤ y} f)
            ∙ sym h
            ∙ substRefl {B = λ w → x ≤ w} f')
          (sym (substRefl {B = C} v)))

  base-source :
    {y' : A}
    → (q : y ≡ y')
    → (f : x ≤ y)
    → (f' : x ≤ y')
    → (v : C y)
    → subst (λ w → x ≤ w) (sym q) f'
      ≡ subst (λ w → w ≤ y) refl f
    → PathP
        (λ i → C (refl {x = x} i))
        (contrav-transport c f v)
        (contrav-transport c f' (subst C q v))
  base-source q =
    J
      (λ (y' : A) (q : y ≡ y') →
        (f : x ≤ y)
        → (f' : x ≤ y')
        → (v : C y)
        → subst (λ w → x ≤ w) (sym q) f'
          ≡ subst (λ w → w ≤ y) refl f
        → PathP
            (λ i → C (refl {x = x} i))
            (contrav-transport c f v)
            (contrav-transport c f' (subst C q v)))
      base-target
      q
