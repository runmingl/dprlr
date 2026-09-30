module DPRLR.Simplicial.Contravariant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Fiberwise using (fiberEquiv)
open import Cubical.Foundations.Equiv.Properties using (isEquivFromIsContr)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma

open import DPRLR.Simplicial.Hom
open import DPRLR.Simplicial.Discrete
open import DPRLR.Simplicial.Function
open import DPRLR.Simplicial.Product
open import DPRLR.Simplicial.Segal
  using (isSegal ; Composite ; segal-compose ; segal-compose-witness)
open import DPRLR.Simplicial.PreorderLocalization
  using (isPreorder ; isPreorder→isSet ; isPreorder→isThin ; isPreorder→isSegal
        ; isSetThinSegal→isPreorder)

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

-- RS17, Definition 8.2.
record isContravariant {A : Type ℓ} (C : A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    contrav-lift :
      {x y : A} (f : x ≤ y) (v : C y)
      → isContr (Σ (C x) (λ u → C ⊢ u ≤[ f ] v))

open isContravariant public

-- RS17, Section 8.2.
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

-- RS17, Lemma 8.15.
contravariant-universal≃ :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x y : A} {f : x ≤ y} {u : C x} {v : C y}
  → (C ⊢ u ≤[ f ] v) ≃ (u ≡ contrav-transport c f v)
contravariant-universal≃ {C = C} c {x = x} {f = f} {u = u} {v = v} =
  contravariant-universal-to c
  , fiberEquiv (λ u → C ⊢ u ≤[ f ] v) (λ u → u ≡ contrav-transport c f v)
      (λ _ → contravariant-universal-to c) total-isEquiv u
  where
  total-isEquiv :
    isEquiv (λ (w : Σ (C x) (λ u → C ⊢ u ≤[ f ] v)) →
      w .fst , contravariant-universal-to c (w .snd))
  total-isEquiv =
    isEquivFromIsContr _ (contrav-lift c f v)
      (isContrRetract (map-snd sym) (map-snd sym) (λ _ → refl)
        (isContrSingl (contrav-transport c f v)))

-- RS17, Proposition 8.16.
contravariant-transport-refl :
  {C : A → Type ℓ'} (c : isContravariant C)
  → {x : A} (v : C x)
  → contrav-transport c (hom-refl x) v ≡ v
contravariant-transport-refl c {x = x} v =
  sym
    (contravariant-universal-to c
      {f = hom-refl x}
      (hom-refl v))

-- RS17, Proposition 8.16.
contravariant-transport-compose :
  {C : A → Type ℓ'} (c : isContravariant C) (S : isSegal A)
  → {x y z : A} (f : x ≤ y) (g : y ≤ z) (v : C z)
  → contrav-transport c (segal-compose S f g) v
    ≡ contrav-transport c f (contrav-transport c g v)
contravariant-transport-compose c S f g v =
  let q = segal-compose-witness S f g in
  contravariant-universal-to c
    ((λ i → contrav-transport c (q .fst i) v)
    , (λ i → contrav-transport c (q .snd .fst i) v)
    , (λ i → contrav-transport c (q .snd .snd i) v))

contravariant-transport-cong :
  {C : A → Type ℓ'} (c : isContravariant C) → isThin A
  → {x x' y y' : A} (p : x ≡ x') (q : y ≡ y')
  → (f : x ≤ y) (g : x' ≤ y')
  → {v : C y} {v' : C y'} → PathP (λ i → C (q i)) v v'
  → PathP (λ i → C (p i)) (contrav-transport c f v) (contrav-transport c g v')
contravariant-transport-cong c thin p q f g v i =
  contrav-transport c (isProp→PathP (λ j → thin (p j) (q j)) f g i) (v i)

-- RS17, Proposition 8.18.
contravariant-fiber-isDiscrete :
  {C : A → Type ℓ'} (c : isContravariant C)
  → (x : A)
  → isDiscrete (C x)
contravariant-fiber-isDiscrete {C = C} c x u v =
  fiberEquiv (λ u → u ≡ v) (λ u → u ≤ v) (λ _ → path→hom) total-isEquiv u
  where
  total-isEquiv :
    isEquiv (λ (w : Σ (C x) (λ u → u ≡ v)) → w .fst , path→hom (w .snd))
  total-isEquiv =
    isEquivFromIsContr _
      (isContrRetract (map-snd sym) (map-snd sym) (λ _ → refl) (isContrSingl v))
      (contrav-lift c (hom-refl x) v)

-- RS17, Remark 8.3.
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
contravariant-Σ {C = C} {D = D} c d .contrav-lift f (vC , vD) =
  isContrRetract
    (λ { ((uC , uD) , q) →
      (uC , HomPΣ-fst {C = C} {D = D} {f = f} q)
      , (uD , HomPΣ-snd {C = C} {D = D} {f = f} q) })
    (λ { ((uC , p) , (uD , q)) →
      (uC , uD) , HomPΣ {C = C} {D = D} {f = f} p q })
    (λ { ((uC , uD) , q) → refl })
    (isContrΣ (contrav-lift c f vC)
      (λ uh → contrav-lift d (Σ≤ f (snd uh)) vD))

contravariant-Σ-discrete :
  {B : Type ℓ''} {C : B → A → Type ℓ'}
  → isDiscrete B
  → ((b : B) → isContravariant (C b))
  → isContravariant (λ x → Σ B (λ b → C b x))
contravariant-Σ-discrete {C = C} d c =
  contravariant-Σ (contravariant-discrete d) indexed-contravariant
  where
  indexed-contravariant : isContravariant (λ ab → C (snd ab) (fst ab))
  indexed-contravariant .contrav-lift {x = x , b₀} {y = y , b₁} r v =
    subst
      (λ bh → isContr (Σ (C (fst bh) x) (λ u →
        (λ ab → C (snd ab) (fst ab))
          ⊢ u ≤[ Σ≤ (hom-map fst r) (snd bh) ] v)))
      (isContr→isProp (hom-to-isContr d b₁)
        (b₁ , hom-refl b₁) (b₀ , hom-map snd r))
      (contrav-lift (c b₁) (hom-map fst r) v)

contravariant-× :
  {C : A → Type ℓ'} {D : A → Type ℓ''}
  → isContravariant C
  → isContravariant D
  → isContravariant (λ x → C x × D x)
contravariant-× c d =
  contravariant-Σ c (contravariant-reindex fst d)

-- RS17, Theorem 8.30.
contravariant-Π :
  {A : Type ℓ} {X : Type ℓ'} {C : A → X → Type ℓ''}
  → ((x : X) → isContravariant (λ a → C a x))
  → isContravariant (λ a → (x : X) → C a x)
contravariant-Π {C = C} c .contrav-lift f v =
  isContrRetract
    (λ { (u , q) x → u x , HomPΠ-happly {P = C} {h = f} q x })
    (λ w → (λ x → w x .fst) , HomPΠ {P = C} {h = f} (λ x → w x .snd))
    (λ { (u , q) → refl })
    (isContrΠ (λ x → contrav-lift (c x) f (v x)))

-- RS17, Proposition 8.13.
representable-isContravariant :
  {ℓ : Level} {A : Type ℓ}
  → isSegal A
  → (a : A)
  → isContravariant (λ x → x ≤ a)
representable-isContravariant S a .contrav-lift f v =
  S f v

-- RS17, Theorem 8.8.
contravariant-total-isSegal :
  {ℓ ℓ' : Level} {A : Type ℓ} {C : A → Type ℓ'}
  → isSegal A → isContravariant C → isSegal (Σ A C)
contravariant-total-isSegal {A = A} {C = C} S c
  {x = x , u} {y = y , w} {z = z , v} f g =
  isOfHLevelRespectEquiv 0
    (Σ-contractFst (chosen , isContr→isProp (contrav-lift c h w) chosen))
    lifted-composites
  where
  h : x ≤ y
  h = hom-map fst f

  chosen : Σ (C x) (λ u₀ → C ⊢ u₀ ≤[ h ] w)
  chosen = u , snd (Iso.fun HomΣ-Iso f)

  arrows≃base-homs : (a : A) → Σ (C a) (λ u₀ → (a , u₀) ≤ (z , v)) ≃ (a ≤ z)
  arrows≃base-homs a = compEquiv
    (isoToEquiv (iso
      (λ { (u₀ , k) → hom-map fst k , u₀ , snd (Iso.fun HomΣ-Iso k) })
      (λ { (k , u₀ , q) → u₀ , Σ≤ k q })
      (λ _ → refl) (λ _ → refl)))
    (Σ-contractSnd (λ k → contrav-lift c k v))

  lifted-composites : isContr
    (Σ (Σ (C x) (λ u₀ → C ⊢ u₀ ≤[ h ] w))
      (λ uq → Composite (Σ≤ h (snd uq)) g))
  lifted-composites = isContrRetract
    (λ { ((u₀ , p) , k , q) →
      (u₀ , k) , HomPΣ {C = C} {D = λ a u₀ → (a , u₀) ≤ (z , v)} {f = h} p q })
    (λ { ((u₀ , k) , q) →
      (u₀ , HomPΣ-fst {C = C} {D = λ a u₀ → (a , u₀) ≤ (z , v)} {f = h} q)
      , k , HomPΣ-snd {C = C} {D = λ a u₀ → (a , u₀) ≤ (z , v)} {f = h} q })
    (λ _ → refl)
    (isOfHLevelRespectEquiv 0
      (invEquiv (Σ-cong-equiv (arrows≃base-homs x) (λ k →
        Σ-cong-equiv (equivΠCod (λ i → arrows≃base-homs (hom-path h i))) (λ q →
          ≃-× (congPathEquiv (λ i → arrows≃base-homs (left-endpoint h i)))
              (congPathEquiv (λ i → arrows≃base-homs (right-endpoint h i)))))))
      (S h (hom-map fst g)))

contravariant-total-isThin :
  {ℓ ℓ' : Level} {A : Type ℓ} {C : A → Type ℓ'}
  → isThin A → isContravariant C → ((x : A) → isSet (C x))
  → isThin (Σ A C)
contravariant-total-isThin {C = C} thin c Cset (x , u) (y , v) =
  isOfHLevelRetractFromIso 1 HomΣ-Iso
    (isPropΣ (thin x y) hom-isProp)
  where
  hom-isProp : (h : x ≤ y) → isProp (C ⊢ u ≤[ h ] v)
  hom-isProp h =
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
