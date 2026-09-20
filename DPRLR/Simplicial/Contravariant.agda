module DPRLR.Simplicial.Contravariant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport using (substCommSlice ; substInPathsL)
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Discrete
open import DPRLR.Simplicial.Function
open import DPRLR.Simplicial.Product
open import DPRLR.Simplicial.Segal using (isSegal)
open import DPRLR.Simplicial.PreorderLocalization
  using (isPreorder ; isPreorder→isSet ; isPreorder→isThin ; isPreorder→isSegal
        ; isSetThinSegal→isPreorder)

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

contravariant-universal≃ :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x y : A} {f : x ≤ y} {u : C x} {v : C y}
  → (C ⊢ u ≤[ f ] v) ≃ (u ≡ contrav-transport c f v)
contravariant-universal≃ {C = C} c {x = x} {f = f} {u = u} {v = v} =
  isoToEquiv contravariant-universal-Iso
  where
  Fiber : C x → Type _
  Fiber u = C ⊢ u ≤[ f ] v

  Lifts : Type _
  Lifts = Σ (C x) Fiber

  chosen-lift : Lifts
  chosen-lift = contrav-lift c f v .fst

  lift≡chosen : (w : Lifts) → w ≡ chosen-lift
  lift≡chosen w = isContr→isProp (contrav-lift c f v) w chosen-lift

  lifts-isSet : isSet Lifts
  lifts-isSet = isProp→isSet (isContr→isProp (contrav-lift c f v))

  to-from : (p : u ≡ contrav-transport c f v)
    → contravariant-universal-to c (contravariant-universal-from c {f = f} p) ≡ p
  to-from p =
    cong (cong fst) (lifts-isSet _ _ contraction-path transport-path)
    where
    q : Fiber u
    q = contravariant-universal-from c p

    contraction-path : (u , q) ≡ chosen-lift
    contraction-path = lift≡chosen (u , q)

    transport-path : (u , q) ≡ chosen-lift
    transport-path =
      sym (ΣPathP (sym p , subst-filler Fiber (sym p) (snd chosen-lift)))

  from-to : (q : Fiber u)
    → contravariant-universal-from c (contravariant-universal-to c q) ≡ q
  from-to q =
    fromPathP (snd (PathPΣ (sym (lift≡chosen (u , q)))))

  contravariant-universal-Iso : Iso (Fiber u) (u ≡ contrav-transport c f v)
  contravariant-universal-Iso =
    iso (contravariant-universal-to c) (contravariant-universal-from c) to-from from-to

contravariant-transport-refl :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x : A} (v : C x)
  → contrav-transport c (hom-refl x) v ≡ v
contravariant-transport-refl c {x = x} v =
  sym
    (contravariant-universal-to c
      {f = hom-refl x}
      (hom-refl v))

contravariant-transport-cong :
  {C : A → Type ℓ'} (c : isContravariant C) → isThin A
  → {x x' y y' : A} (p : x ≡ x') (q : y ≡ y')
  → (f : x ≤ y) (g : x' ≤ y')
  → {v : C y} {v' : C y'} → PathP (λ i → C (q i)) v v'
  → PathP (λ i → C (p i)) (contrav-transport c f v) (contrav-transport c g v')
contravariant-transport-cong c thin p q f g v i =
  contrav-transport c (isProp→PathP (λ j → thin (p j) (q j)) f g i) (v i)

contravariant-fiber-isDiscrete :
  {C : A → Type ℓ'} (c : isContravariant C)
  → (x : A)
  → isDiscrete (C x)
contravariant-fiber-isDiscrete {C = C} c x u v =
  subst isEquiv
    (sym (funExt path→hom≡inv))
    (invEquiv (Hom≃Path u v) .snd)
  where
  Hom≃Path : (u v : C x) → (u ≤ v) ≃ (u ≡ v)
  Hom≃Path u v =
      u ≤ v
    ≃⟨ contravariant-universal≃ c {f = hom-refl x} ⟩
      u ≡ contrav-transport c (hom-refl x) v
    ≃⟨ (_∙ contravariant-transport-refl c v)
        , compPathr-isEquiv (contravariant-transport-refl c v) ⟩
      u ≡ v
    ■

  Hom≃Path-path→hom : {u v : C x} (p : u ≡ v)
    → Hom≃Path u v .fst (path→hom p) ≡ p
  Hom≃Path-path→hom {u = u} {v = v} p =
      encode v (path→hom p)
    ≡⟨ sym (substCommSlice (λ v → u ≤ v) (λ v → u ≡ v) encode p (hom-refl u)) ⟩
      subst (λ v → u ≡ v) p (encode u (hom-refl u))
    ≡⟨ cong (subst (λ v → u ≡ v) p)
        (rCancel (contravariant-universal-to c {f = hom-refl x} (hom-refl u))) ⟩
      subst (λ v → u ≡ v) p refl
    ≡⟨ substInPathsL p refl ⟩
      refl ∙ p
    ≡⟨ sym (lUnit p) ⟩
      p
    ∎
    where
    encode : (v : C x) → u ≤ v → u ≡ v
    encode v = Hom≃Path u v .fst

  path→hom≡inv : {u v : C x} (p : u ≡ v)
    → path→hom p ≡ invEq (Hom≃Path u v) p
  path→hom≡inv {u = u} {v = v} p =
    isoFunInjective
      (equivToIso (Hom≃Path u v))
      (path→hom p)
      (invEq (Hom≃Path u v) p)
      (
          Hom≃Path u v .fst (path→hom p)
        ≡⟨ Hom≃Path-path→hom p ⟩
          p
        ≡⟨ sym (secEq (Hom≃Path u v) p) ⟩
          Hom≃Path u v .fst (invEq (Hom≃Path u v) p)
        ∎)

contravariant-equiv :
  {C : A → Type ℓ'} {D : A → Type ℓ''}
  → ((x : A) → C x ≃ D x)
  → isContravariant C
  → isContravariant D
contravariant-equiv {C = C} {D = D} e c .contrav-lift {x = x} {y = y} f v =
  subst (λ v → isContr (Σ (D x) (λ u → D ⊢ u ≤[ f ] v)))
    (secEq (e y) v)
    (isOfHLevelRespectEquiv 0 (lifts≃ (invEq (e y) v))
      (contrav-lift c f (invEq (e y) v)))
  where
  hom≃ : (u : C x) (w : C y)
    → (C ⊢ u ≤[ f ] w) ≃ (D ⊢ e x .fst u ≤[ f ] e y .fst w)
  hom≃ u w =
    Σ-cong-equiv (equivΠCod (λ i → e (hom-path f i))) λ q →
      ≃-× (congPathEquiv (λ i → e (left-endpoint f i)))
          (congPathEquiv (λ i → e (right-endpoint f i)))

  lifts≃ : (w : C y)
    → Σ (C x) (λ u → C ⊢ u ≤[ f ] w)
      ≃ Σ (D x) (λ u → D ⊢ u ≤[ f ] e y .fst w)
  lifts≃ w = Σ-cong-equiv (e x) (λ u → hom≃ u w)

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

contravariant-Σ-discrete :
  {B : Type ℓ''} {C : B → A → Type ℓ'}
  → isDiscrete B
  → ((b : B) → isContravariant (C b))
  → isContravariant (λ x → Σ B (λ b → C b x))
contravariant-Σ-discrete {A = A} {B = B} {C = C} d c =
  contravariant-Σ (contravariant-discrete d) indexed-contravariant
  where
  Indexed : A × B → Type _
  Indexed (x , b) = C b x

  indexed-contravariant : isContravariant Indexed
  indexed-contravariant .contrav-lift {x = x , b₀} {y = y , b₁} r v =
    subst (λ h → isContr (Lifts h v))
      (path→hom-hom→path d h)
      (path-index-lifts (hom→path d h) v)
    where
    f : x ≤ y
    f = hom-map fst r

    h : b₀ ≤ b₁
    h = hom-map snd r

    Lifts : {b : B} → b₀ ≤ b → C b y → Type _
    Lifts h v = Σ (C b₀ x) (λ u → Indexed ⊢ u ≤[ Σ≤ f h ] v)

    fixed-index-lifts : (v : C b₀ y) → isContr (Lifts (hom-refl b₀) v)
    fixed-index-lifts v = contrav-lift (c b₀) f v

    refl-index-lifts : (v : C b₀ y) → isContr (Lifts (path→hom refl) v)
    refl-index-lifts v =
      subst (λ h → isContr (Lifts h v))
        (sym path→hom-refl) (fixed-index-lifts v)

    path-index-lifts : {b : B} (p : b₀ ≡ b) (v : C b y)
      → isContr (Lifts (path→hom p) v)
    path-index-lifts p =
      J (λ b p → (v : C b y) → isContr (Lifts (path→hom p) v))
        refl-index-lifts
        p

contravariant-× :
  {C : A → Type ℓ'} {D : A → Type ℓ''}
  → isContravariant C
  → isContravariant D
  → isContravariant (λ x → C x × D x)
contravariant-× c d =
  contravariant-Σ c (contravariant-reindex fst d)

contravariant-Π :
  {A : Type ℓ} {X : Type ℓ'} {C : A → X → Type ℓ''}
  → ((x : X) → isContravariant (λ a → C a x))
  → isContravariant (λ a → (x : X) → C a x)
contravariant-Π {X = X} {C = C} c .contrav-lift {x = a₀} {y = a₁} f v =
  isContrRetract to from from-to pointwise-lifts
  where
  ΠLift : Type _
  ΠLift =
    Σ ((x : X) → C a₀ x)
      (λ u → (λ a → (x : X) → C a x) ⊢ u ≤[ f ] v)

  PointwiseLifts : Type _
  PointwiseLifts =
    (x : X) → Σ (C a₀ x) (λ u → (λ a → C a x) ⊢ u ≤[ f ] v x)

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

representable-isContravariant :
  {ℓ : Level} {A : Type ℓ}
  → isSegal A
  → (a : A)
  → isContravariant (λ x → x ≤ a)
representable-isContravariant S a .contrav-lift f v =
  S f v

contravariant-total-isSegal :
  {ℓ ℓ' : Level} {A : Type ℓ} {C : A → Type ℓ'}
  → isSegal A → isContravariant C → isSegal (Σ A C)
contravariant-total-isSegal {A = A} {C = C} S c {z = z , v} f g =
  contrav-lift total-homs-contravariant f g
  where
  TotalHom : (x : A) → C x → Type _
  TotalHom x u = Σ (x ≤ z) (λ h → C ⊢ u ≤[ h ] v)

  arrows≃base-homs : (x : A) → Σ (C x) (TotalHom x) ≃ (x ≤ z)
  arrows≃base-homs x =
      Σ (C x) (TotalHom x)
    ≃⟨ isoToEquiv rearrange ⟩
      Σ (x ≤ z) (λ h → Σ (C x) (λ u → C ⊢ u ≤[ h ] v))
    ≃⟨ Σ-contractSnd (λ h → contrav-lift c h v) ⟩
      x ≤ z
    ■
    where
    rearrange : Iso (Σ (C x) (TotalHom x))
      (Σ (x ≤ z) (λ h → Σ (C x) (λ u → C ⊢ u ≤[ h ] v)))
    Iso.fun rearrange (u , h , q) = h , u , q
    Iso.inv rearrange (h , u , q) = u , h , q
    Iso.rightInv rearrange _ = refl
    Iso.leftInv rearrange _ = refl

  summed-representable : isContravariant (λ x → Σ (C x) (TotalHom x))
  summed-representable = contravariant-equiv
    (λ x → invEquiv (arrows≃base-homs x))
    (representable-isContravariant S z)

  total-homs-contravariant : isContravariant (λ xu → xu ≤ (z , v))
  total-homs-contravariant = contravariant-equiv
    (λ xu → invEquiv (HomΣ≃ {x = xu} {y = z , v}))
    (contravariant-Σ-reflect c summed-representable)
    where
    contravariant-Σ-reflect :
      {C : A → Type ℓ'} {D : (a : A) → C a → Type ℓ''}
      → isContravariant C
      → isContravariant (λ a → Σ (C a) (D a))
      → isContravariant (λ au → D (fst au) (snd au))
    contravariant-Σ-reflect {C = C} {D = D} c d
      .contrav-lift {x = x , u} {y = y , v} f w =
      isOfHLevelRespectEquiv 0
        (Σ-contractFst (chosen , isContr→isProp (contrav-lift c h v) chosen))
        component-lifts
      where
      h : x ≤ y
      h = hom-map fst f

      chosen : Σ (C x) (λ u₀ → C ⊢ u₀ ≤[ h ] v)
      chosen = u , snd (Iso.fun HomΣ-Iso f)

      ComponentLifts : Type _
      ComponentLifts =
        Σ (Σ (C x) (λ u₀ → C ⊢ u₀ ≤[ h ] v))
          (λ uq → Σ (D x (fst uq))
            (λ w₀ → (λ au → D (fst au) (snd au)) ⊢ w₀ ≤[ Σ≤ h (snd uq) ] w))

      TotalLifts : Type _
      TotalLifts = Σ (Σ (C x) (D x))
        (λ uw → (λ a → Σ (C a) (D a)) ⊢ uw ≤[ h ] (v , w))

      to : ComponentLifts → TotalLifts
      to ((u₀ , p) , w₀ , q) =
        (u₀ , w₀) , HomPΣ {C = C} {D = D} {f = h} p q

      from : TotalLifts → ComponentLifts
      from ((u₀ , w₀) , q) =
        (u₀ , HomPΣ-fst {C = C} {D = D} {f = h} q)
        , w₀ , HomPΣ-snd {C = C} {D = D} {f = h} q

      from-to : (lifts : ComponentLifts) → from (to lifts) ≡ lifts
      from-to _ = refl

      component-lifts : isContr ComponentLifts
      component-lifts = isContrRetract to from from-to (contrav-lift d h (v , w))

contravariant-total-isThin :
  {ℓ ℓ' : Level} {A : Type ℓ} {C : A → Type ℓ'}
  → isThin A → isContravariant C → ((x : A) → isSet (C x))
  → isThin (Σ A C)
contravariant-total-isThin {C = C} thin c Cset (x , u) (y , v) =
  isOfHLevelRetractFromIso 1 HomΣ-Iso
    (isPropΣ (thin x y) displayed-hom-isProp)
  where
  displayed-hom-isProp : (h : x ≤ y) → isProp (C ⊢ u ≤[ h ] v)
  displayed-hom-isProp h =
    isOfHLevelRespectEquiv 1
      (invEquiv (contravariant-universal≃ c {f = h}))
      (Cset x u (contrav-transport c h v))

contravariant-total-isPreorder :
  {ℓ ℓ' : Level} {A : Type ℓ} {C : A → Type ℓ'}
  → isPreorder A → isContravariant C → ((x : A) → isSet (C x))
  → isPreorder (Σ A C)
contravariant-total-isPreorder P c Cset = isSetThinSegal→isPreorder
  (isSetΣ (isPreorder→isSet P) Cset)
  (contravariant-total-isThin (isPreorder→isThin P) c Cset)
  (contravariant-total-isSegal (isPreorder→isSegal P) c)
