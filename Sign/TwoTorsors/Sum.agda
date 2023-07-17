open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to sumrec)
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Functions.Involution
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Structures.Pointed
open import Sign.TwoTorsors.Base

module Sign.TwoTorsors.Sum where

private
  variable
    ℓ : Level

infixr 30 _+ᵀ_

{- We want to prove that K(S2,1) is an homogeneous type, i.e. that for any two X Y : K(S2,1) we can
   find an equality (K(S2,1),X) = (K(S2,1) = Y), which caracterises the space of an abelian group.
   To do this, we need to introduce the notion of sum of torsors, which then allows us to define the
   expected equality.
   The sum of X and Y will be a torsor Z with + : X → Y → Z commuting with the action on torsors. -}

module _
  ((X , e) : TwoTorsor ℓ)
  ((Y , e') : TwoTorsor ℓ)
    where

  bilin+ : (Z : TwoTorsor ℓ) → (X → Y → ⟨ Z ⟩) → Type ℓ
  bilin+ Z +ᶻ = (x : X) → (y : Y) → (b : Bool) →
    ((+ᶻ (+ₜₐ (X , e) b x) y ≡ +ₜₐ Z b (+ᶻ x y)) × (+ᶻ x (+ₜₐ (Y , e') b y) ≡ +ₜₐ Z b (+ᶻ x y)))

  +²ᵀ : Type (lsuc ℓ)
  +²ᵀ = Σ[ S ∈ (Σ[ Z ∈ (TwoTorsor ℓ)] (X → Y → ⟨ Z ⟩))] (bilin+ (fst S) (snd S))

  isPropBilin : ((Z , e'') : TwoTorsor ℓ) → (+ᶻ : X → Y → Z) → isProp (bilin+ (Z , e'') +ᶻ)
  isPropBilin (Z , e'') +ᶻ α β = funExt (λ x → funExt (λ y → funExt (λ b → ≡-×
    (isSetTors (Z , e'') _ _ (fst (α x y b)) (fst (β x y b)))
    (isSetTors (Z , e'') _ _ (snd (α x y b)) (snd (β x y b))) )))

  +≡ₜ : ((((Z , e) , +ᶻ) , a) : +²ᵀ) → ((((Z' , e') , +ᶻ') , a') : +²ᵀ) →
    (p : Z ≡ Z') → PathP (λ i → (X → Y → p i)) +ᶻ +ᶻ' →
    (((Z , e) , +ᶻ) , a) ≡ (((Z' , e') , +ᶻ') , a')
  +≡ₜ ((Z , +ᶻ) , a) ((Z' , +ᶻ') , a') p q = ΣPathPProp (λ Z → isPropBilin (fst Z) (snd Z))
    (ΣPathP (Σ≡Prop (λ _ → isPropPropTrunc) p , q))

-- We can define Bool + Bool to be (Bool, ⊕)

issumBool : ∀ {ℓ} → +²ᵀ {ℓ = ℓ} ∙ₜ ∙ₜ
issumBool {ℓ} = (∙ₜ , (λ a → λ b → lift (lower a ⊕ lower b))) ,
  (λ x → λ y → λ b → (
  lift (lower (+ₜₐ ∙ₜ b x) ⊕ lower y)
    ≡⟨ cong (λ z → lift (lower {j = ℓ} z ⊕ lower y)) (+∙ₜ b $ lower x) ⟩
  lift ((b ⊕ lower x) ⊕ lower y)
    ≡⟨ cong (λ z → lift z) (sym (⊕-assoc b (lower x) (lower y))) ⟩
  lift (b ⊕ lower (lift {j = ℓ} (lower x ⊕ lower y)))
    ≡⟨ sym (+∙ₜ b (lower x ⊕ lower y)) ⟩
  +ₜₐ ∙ₜ b (lift (lower x ⊕ lower y)) ∎), 
  (lift (lower x ⊕ lower (+ₜₐ ∙ₜ b y))
    ≡⟨ cong (λ z → lift (lower x ⊕ lower {j = ℓ} z)) (+∙ₜ b $ lower y) ⟩
  lift (lower x ⊕ (b ⊕ lower y))
    ≡⟨ cong (λ z → lift (lower x ⊕ z)) (⊕-comm b (lower y)) ⟩
  lift (lower x ⊕ (lower y ⊕ b))
    ≡⟨ cong lift (⊕-assoc (lower x) (lower y) b) ⟩
  lift ((lower x ⊕ lower y) ⊕ b)
    ≡⟨ cong lift (⊕-comm (lower x ⊕ lower y) b) ⟩
  lift (b ⊕ lower (lift {j = ℓ} (lower x ⊕ lower y)))
    ≡⟨ sym (+∙ₜ b (lower x ⊕ lower y)) ⟩
  +ₜₐ ∙ₜ b (lift (lower x ⊕ lower y)) ∎))

-- We show that the universal property defines the sum uniquely,
-- which allow us to transport the result along the troncated paths.
-- We just have to prove that the type sumTors X Y is contractible for Bool Bool.

isContr+²ᵀ : ∀ {ℓ} → (X : TwoTorsor ℓ) → (Y : TwoTorsor ℓ) → isContr (+²ᵀ X Y)
isContr+²ᵀ {ℓ} (X , e) (Y , e') = rec isPropIsContr (λ f → rec isPropIsContr (λ f' →
  subst2 (λ X → λ Y → isContr (+²ᵀ X Y))
  (Σ≡Prop (λ _ → isPropPropTrunc) {u = ∙ₜ} {v = (X , e)}
    (sym (ua (f ∙ₑ LiftEquiv)))) 
  (Σ≡Prop (λ _ → isPropPropTrunc) {u = ∙ₜ} {v = (Y , e')}
    (sym (ua (f' ∙ₑ LiftEquiv))))
  (issumBool , (λ Z → +≡ₜ {ℓ} ∙ₜ ∙ₜ issumBool Z (ua (equivBoolSum Z))
  ((funExt (λ α → funExt (λ β → toPathP (
    transport (ua (equivBoolSum Z)) (lift (lower α ⊕ lower β))
      ≡⟨ uaβ (equivBoolSum Z) (lift (lower α ⊕ lower β)) ⟩
    snd (fst Z) (lift (lower α ⊕ lower β)) (lift false)
      ≡⟨ cong (λ c → snd (fst Z) (lift c) (lift false)) (⊕-comm (lower α) (lower β)) ⟩
    snd (fst Z) (lift (lower β ⊕ lower α)) (lift false)
      ≡⟨ cong (λ c → snd (fst Z) c (lift false)) (sym (+∙ₜ (lower β) (lower α))) ⟩
    snd (fst Z) (+ₜₐ ∙ₜ (lower β) α) (lift false)
      ≡⟨ fst ((snd Z) α (lift false) (lower β)) ⟩
    +ₜₐ (fst (fst Z)) (lower β) (snd (fst Z) α (lift false))
      ≡⟨ sym (snd ((snd Z) α (lift false) (lower β))) ⟩
    snd (fst Z) α (+ₜₐ ∙ₜ (lower β) (lift false))
      ≡⟨ cong (λ c → snd (fst Z) α c) (+∙ₜ (lower β) false) ⟩
    snd (fst Z) α (lift ((lower β) ⊕ false))
      ≡⟨ cong (λ c → snd (fst Z) α (lift c)) (⊕-identityʳ (lower β)) ⟩
    snd (fst Z) α β ∎)))))))) e') e
  where
  equivBoolSum : (Z : +²ᵀ {ℓ = ℓ} ∙ₜ ∙ₜ) →
    (fst (fst (fst (issumBool {ℓ}))) ≃ fst (fst (fst Z)))
  equivBoolSum ((Z , +ᶻ) , ≡ᵇ) = ((λ b → +ᶻ b (lift false)) ,
    subst isEquiv (funExt (λ b →
    +ₜₐ Z (lower b) (+ᶻ (lift false) (lift false))
      ≡⟨ sym (fst (≡ᵇ (lift false) (lift false) (lower b))) ⟩
    +ᶻ (+ₜₐ ∙ₜ (lower b) (lift false)) (lift false)
      ≡⟨ cong (λ x → +ᶻ x (lift false)) (+∙ₜ (lower b) false) ⟩
    +ᶻ (lift ((lower b) ⊕ false)) (lift false)
      ≡⟨ cong (λ x → +ᶻ (lift x) (lift false)) (⊕-identityʳ (lower b)) ⟩
    +ᶻ b (lift false) ∎
    )) ((invEquiv (LiftEquiv {A = Bool}) ∙ₑ ((λ b → +ₜₐ Z b (+ᶻ (lift false) (lift false))) ,
    isTrans+ₜ Z (+ᶻ (lift false) (lift false)))) .snd))

_+ᵀ_ : TwoTorsor ℓ → TwoTorsor ℓ → TwoTorsor ℓ
X +ᵀ Y = isContr+²ᵀ X Y .fst .fst .fst

-- We will prove that this sum makes the type of 2-torsors a monoidal symmetric categories
-- with inverses.
-- For the equalities, we will prove that two objects have the same universal properties.

-- It is symmetric

sym+ᵀ : (X : TwoTorsor ℓ) → (Y : TwoTorsor ℓ) → X +ᵀ Y ≡ Y +ᵀ X
sym+ᵀ X Y = Σ≡Prop (λ _ → isPropPropTrunc) (PathPΣ (PathPΣ (PathPΣ (snd (isContr+²ᵀ X Y) 
    ((Y +ᵀ X , (λ y → λ x → isContr+²ᵀ Y X .fst .fst .snd x y)) ,
    (λ y → λ x → λ b → isContr+²ᵀ Y X .fst .snd x y b .snd , isContr+²ᵀ Y X .fst .snd x y b .fst)))
    .fst) .fst) .fst)

-- The point (Lift Bool , ∣ LiftEquiv ∣₁) is neutral

sumUnit : (X : TwoTorsor ℓ) → X +ᵀ ∙ₜ ≡ X
sumUnit X = Σ≡Prop (λ _ → isPropPropTrunc) (PathPΣ (PathPΣ (PathPΣ (snd (isContr+²ᵀ X ∙ₜ)
    ((X , (λ x → λ y → +ₜₐ X (lower y) x)) ,
    (λ x → λ y → λ b → (
      +ₜₐ X (lower y) (+ₜₐ X b x)
        ≡⟨ cong (λ a → a .fst x) (assoc+ₜ X b (lower y)) ⟩
      +ₜₐ X (b ⊕ lower y) x
        ≡⟨ cong (λ a → +ₜₐ X a x) (⊕-comm b (lower y)) ⟩
      +ₜₐ X (lower y ⊕ b) x
        ≡⟨ cong (λ a → a .fst x) (sym (assoc+ₜ X (lower y) b)) ⟩
      +ₜₐ X b (+ₜₐ X (lower y) x)∎) , (
      +ₜₐ X (lower (+ₜₐ ∙ₜ b y)) x
        ≡⟨ cong (λ a → +ₜₐ X (lower {j = lzero} a) x) (+∙ₜ b (lower y)) ⟩
      +ₜₐ X (b ⊕ lower y) x
        ≡⟨ cong (λ a → +ₜₐ X a x) (⊕-comm b (lower y)) ⟩
      +ₜₐ X (lower y ⊕ b) x
        ≡⟨ cong (λ a → a .fst x) (sym (assoc+ₜ X (lower y) b)) ⟩
      +ₜₐ X b (+ₜₐ X (lower y) x)∎ )))) .fst) .fst) .fst)

-- The inverse of X is itself, thus X + X ≡ Bool

invTors : (X : TwoTorsor ℓ) → X +ᵀ X ≡ ∙ₜ
invTors X = Σ≡Prop (λ _ → isPropPropTrunc) (PathPΣ (PathPΣ (PathPΣ (snd (isContr+²ᵀ X X) 
  (testIntermFin X)) .fst) .fst) .fst)
  where
  plusBoolSum : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → Lift {j = ℓ} Bool
  plusBoolSum X x y = sumrec (λ _ → lift false) (λ _ → lift true) (dichotomyTors X x y)
  lemma1 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → (b : Bool) →
    plusBoolSum X (+ₜₐ X b x) y ≡ +ₜₐ ∙ₜ b (plusBoolSum X x y)
  lemma1 {ℓ} X x y true = sumrec (λ α → sym (
    +ₜₐ ∙ₜ true (plusBoolSum X x y)
      ≡⟨ cong (λ a → +ₜₐ ∙ₜ true
         (sumrec {C = Lift {j = ℓ} Bool} (λ _ → lift false) (λ _ → lift true) a))
      (isPropDichotomyTors X x y (dichotomyTors X x y) (inl α)) ⟩
    +ₜₐ ∙ₜ true (lift false)
      ≡⟨ +∙ₜ true false ⟩
    sumrec (λ _ → lift false) (λ _ → lift true) (inr {A = +ₜₐ X true x ≡ y}
      (cong (λ b → +ₜₐ X true b) α)) 
      ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
        (isPropDichotomyTors X (+ₜₐ X true x) y
        (inr (cong (λ b → +ₜₐ X true b) α))
        (dichotomyTors X (+ₜₐ X true x) y)) ⟩
      plusBoolSum X (+ₜₐ X true x) y ∎)) (λ α → sym (
      +ₜₐ ∙ₜ true (plusBoolSum X x y)
      ≡⟨ cong (λ a → +ₜₐ ∙ₜ true
         (sumrec {C = Lift Bool} (λ _ → lift false) (λ _ → lift true) a))
        (isPropDichotomyTors X x y (dichotomyTors X x y) (inr α)) ⟩
    +ₜₐ ∙ₜ true (lift true)
      ≡⟨ +∙ₜ true true ⟩
    sumrec (λ _ → lift false) (λ _ → lift true) (inl {B = +ₜₐ X true x ≡ +ₜₐ X true y} 
      ( (cong (λ b → +ₜₐ X true b) α) ∙ (cong (λ a → a .fst y) (assoc+ₜ X true true))
        ∙ (cong (λ a → a .fst y) (+ₜ0 X))))
      ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
        (isPropDichotomyTors X (+ₜₐ X true x) y
        (inl {B = +ₜₐ X true x ≡ +ₜₐ X true y} 
          ( (cong (λ b → +ₜₐ X true b) α)
          ∙ (cong (λ a → a .fst y) (assoc+ₜ X true true))
          ∙ (cong (λ a → a .fst y) (+ₜ0 X))))
        (dichotomyTors X (+ₜₐ X true x) y)) ⟩
    plusBoolSum X (+ₜₐ X true x) y ∎)) (dichotomyTors X x y) 
  lemma1 X x y false = cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true)
    (dichotomyTors X (a .fst x) y)) (+ₜ0 X) ∙ sym ((cong (λ a → a .fst (plusBoolSum X x y))) (+ₜ0 ∙ₜ))
  lemmaForLemma2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → (x ≡ y) →
    (x ≡ +ₜₐ X true y) ⊎
    (x ≡ +ₜₐ X true (+ₜₐ X true y))
  lemmaForLemma2 X x y α = inr (α ∙ sym (isNilFlip X y))
  lemma2ForLemma2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → (x ≡ y) →
    +ₜₐ ∙ₜ true (plusBoolSum X x y) ≡
    plusBoolSum X x (+ₜₐ X true y)
  lemma2ForLemma2 X x y α = +ₜₐ ∙ₜ true (plusBoolSum X x y)
    ≡⟨ cong (λ a → +ₜₐ ∙ₜ true
      (sumrec {C = Lift Bool} (λ _ → lift false) (λ _ → lift true) a))
      (isPropDichotomyTors X x y (dichotomyTors X x y) (inl α)) ⟩
    +ₜₐ ∙ₜ true (sumrec (λ _ → lift false) (λ _ → lift true)
      (inl {B = x ≡ +ₜₐ X true y} α))
      ≡⟨ refl ⟩
    +ₜₐ ∙ₜ true (lift false)
      ≡⟨ +∙ₜ true false ⟩
    sumrec (λ _ → lift false) (λ _ → lift true) (lemmaForLemma2 X x y α)
        ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
          (isPropDichotomyTors X x (+ₜₐ X true y)
          (lemmaForLemma2 X x y α) (dichotomyTors X x (+ₜₐ X true y))) ⟩
    plusBoolSum X x (+ₜₐ X true y) ∎
  lemma3ForLemma2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → (x ≡ +ₜₐ X true y) →
    +ₜₐ ∙ₜ true (plusBoolSum X x y) ≡
    plusBoolSum X x (+ₜₐ X true y)
  lemma3ForLemma2 X x y α = +ₜₐ ∙ₜ true (plusBoolSum X x y)
    ≡⟨ cong (λ a → +ₜₐ ∙ₜ true
      (sumrec (λ _ → lift false) (λ _ → lift true) a))
      (isPropDichotomyTors X x y (dichotomyTors X x y) (inr α)) ⟩
    +ₜₐ ∙ₜ true (lift true)
      ≡⟨ +∙ₜ true true ⟩
    sumrec (λ _ → lift false) (λ _ → lift true)
      (inl {B = x ≡ +ₜₐ X true (+ₜₐ X true y)} α)
      ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
        (isPropDichotomyTors X x (+ₜₐ X true y)
        (inl α) (dichotomyTors X x (+ₜₐ X true y))) ⟩
    plusBoolSum X x (+ₜₐ X true y) ∎
  lemma4ForLemma2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) →
    +ₜₐ ∙ₜ false (plusBoolSum X x y) ≡
    plusBoolSum X x (+ₜₐ X false y)
  lemma4ForLemma2 X x y = sumrec (λ α → (+ₜₐ ∙ₜ false (plusBoolSum X x y)
    ≡⟨ cong (λ a → +ₜₐ ∙ₜ false (sumrec (λ _ → lift false) (λ _ → lift true) a))
      (isPropDichotomyTors X x y (dichotomyTors X x y)
      (inl {B = x ≡ +ₜₐ X true y} α)) ⟩
    +ₜₐ ∙ₜ false (lift false)
      ≡⟨ +∙ₜ false false ⟩
    sumrec (λ _ → lift false) (λ _ → lift true)
      (inl {B = x ≡ +ₜₐ X true (+ₜₐ X false y)}
      (α ∙ sym (cong (λ a → a .fst y) (+ₜ0 X))))
      ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
        (isPropDichotomyTors X x (+ₜₐ X false y)
        (inl (α ∙ sym (cong (λ a → a .fst y) (+ₜ0 X))))
        (dichotomyTors X x (+ₜₐ X false y))) ⟩
    plusBoolSum X x (+ₜₐ X false y) ∎)
    ) (λ α → +ₜₐ ∙ₜ false (plusBoolSum X x y) 
      ≡⟨ cong (λ a → +ₜₐ ∙ₜ false
        (sumrec (λ _ → lift false) (λ _ → lift true) a))
        (isPropDichotomyTors X x y (dichotomyTors X x y) (inr {A = x ≡ y} α)) ⟩
    +ₜₐ ∙ₜ false (lift true)
      ≡⟨ +∙ₜ false true ⟩
    sumrec (λ _ → lift false) (λ _ → lift true) (inr {A = x ≡ +ₜₐ X false y}
      (α ∙ sym (cong (λ a → +ₜₐ X true (a .fst y)) (+ₜ0 X))))
      ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
        (isPropDichotomyTors X x (+ₜₐ X false y)
        (inr {A = x ≡ +ₜₐ X false y}
        (α ∙ sym (cong (λ a → +ₜₐ X true (a .fst y)) (+ₜ0 X))))
        (dichotomyTors X x (+ₜₐ X false y))) ⟩
    plusBoolSum X x (+ₜₐ X false y) ∎) (dichotomyTors X x y)
  lemma2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → (b : Bool) →
    plusBoolSum X x (+ₜₐ X b y) ≡ +ₜₐ ∙ₜ b (plusBoolSum X x y)
  lemma2 X x y true = sym (sumrec (lemma2ForLemma2 X x y) (lemma3ForLemma2 X x y)
    (dichotomyTors X x y))
  lemma2 X x y false = sym (lemma4ForLemma2 X x y)
  testInterm : ∀ {ℓ} → (X : TwoTorsor ℓ) → Σ[ S ∈ (Σ[ Z ∈ (TwoTorsor ℓ)] (fst X → fst X → (fst Z)))]
    (bilin+ X X (fst S) (snd S))
  testInterm X = (∙ₜ , plusBoolSum X) , (λ x → λ y → λ b → lemma1 X x y b , lemma2 X x y b)
  testIntermFin : ∀ {ℓ} → (X : TwoTorsor ℓ) → +²ᵀ X X
  testIntermFin X = testInterm X

-- We will prove that the sum is associative, but we first need to introduce ternary sum

triSum : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) (Z : TwoTorsor ℓ) → Type (lsuc ℓ)
triSum {ℓ} X Y Z = Σ[ A ∈ (TwoTorsor ℓ) ] (Σ[ addi ∈ (fst X → fst Y → fst Z → fst A) ]
  ((x : fst X) (y : fst Y) (z : fst Z) (b : Bool) →
  (addi (+ₜₐ X b x) y z ≡ +ₜₐ A b (addi x y z)) ×
  (addi x (+ₜₐ Y b y) z ≡ +ₜₐ A b (addi x y z)) ×
  (addi x y (+ₜₐ Z b z) ≡ +ₜₐ A b (addi x y z)) ))

isTriSumBool : ∀ {ℓ} → triSum {ℓ} ∙ₜ ∙ₜ ∙ₜ
isTriSumBool = (∙ₜ , ((λ b₀ → λ b₁ → λ b₂ → lift (((lower b₀) ⊕ (lower b₁)) ⊕ (lower b₂))) ,
  (λ b₀ → λ b₁ → λ b₂ → λ b₃ →
  (lift ((lower (+ₜₐ ∙ₜ b₃ b₀) ⊕ lower b₁) ⊕ lower b₂)
    ≡⟨ cong (λ a → lift ((lower {j = lzero} a ⊕ lower b₁) ⊕ lower b₂)) (+∙ₜ b₃ (lower b₀)) ⟩
  lift (((b₃ ⊕ lower b₀) ⊕ lower b₁) ⊕ lower b₂)
    ≡⟨ cong (λ a → lift (a ⊕ lower b₂)) (sym (⊕-assoc b₃ (lower b₀) (lower b₁))) ⟩
  lift ((b₃ ⊕ (lower b₀ ⊕ lower b₁)) ⊕ lower b₂)
    ≡⟨ cong lift (sym (⊕-assoc b₃ (lower b₀ ⊕ lower b₁) (lower b₂))) ⟩
  lift (b₃ ⊕ ((lower b₀ ⊕ lower b₁) ⊕ lower b₂))
    ≡⟨ sym (+∙ₜ b₃ ((lower b₀ ⊕ lower b₁) ⊕ lower b₂)) ⟩
  +ₜₐ ∙ₜ b₃ (lift ((lower b₀ ⊕ lower b₁) ⊕ lower b₂)) ∎) ,
  (lift ((lower b₀ ⊕ lower (+ₜₐ ∙ₜ b₃ b₁)) ⊕ lower b₂)
    ≡⟨ cong (λ a → lift ((lower b₀ ⊕ lower {j = lzero} a) ⊕ lower b₂)) (+∙ₜ b₃ (lower b₁)) ⟩
  lift ((lower b₀ ⊕ (b₃ ⊕ lower b₁)) ⊕ lower b₂)
    ≡⟨ cong (λ a → lift ((lower b₀ ⊕ a) ⊕ lower b₂)) (⊕-comm b₃ (lower b₁)) ⟩
  lift ((lower b₀ ⊕ (lower b₁ ⊕ b₃)) ⊕ lower b₂)
    ≡⟨ cong (λ a → lift (a ⊕ lower b₂)) (⊕-assoc (lower b₀) (lower b₁) b₃) ⟩
  lift (((lower b₀ ⊕ lower b₁) ⊕ b₃) ⊕ lower b₂)
    ≡⟨ cong lift (sym (⊕-assoc (lower b₀ ⊕ lower b₁) b₃ (lower b₂))) ⟩
  lift ((lower b₀ ⊕ lower b₁) ⊕ (b₃ ⊕ lower b₂))
    ≡⟨ cong (λ a → lift ((lower b₀ ⊕ lower b₁) ⊕ a)) (⊕-comm b₃ (lower b₂)) ⟩
  lift ((lower b₀ ⊕ lower b₁) ⊕ (lower b₂ ⊕ b₃))
    ≡⟨ cong lift (⊕-assoc (lower b₀ ⊕ lower b₁) (lower b₂) b₃) ⟩
  lift (((lower b₀ ⊕ lower b₁) ⊕ lower b₂) ⊕ b₃)
    ≡⟨ cong lift (⊕-comm ((lower b₀ ⊕ lower b₁) ⊕ lower b₂) b₃) ⟩
  lift (b₃ ⊕ ((lower b₀ ⊕ lower b₁) ⊕ lower b₂))
    ≡⟨ sym (+∙ₜ b₃ ((lower b₀ ⊕ lower b₁) ⊕ lower b₂)) ⟩
  +ₜₐ ∙ₜ b₃ (lift ((lower b₀ ⊕ lower b₁) ⊕ lower b₂)) ∎) ,
  (lift ((lower b₀ ⊕ lower b₁) ⊕ lower (+ₜₐ ∙ₜ b₃ b₂))
    ≡⟨ cong (λ a → lift ((lower b₀ ⊕ lower b₁) ⊕ lower {j = lzero} a)) (+∙ₜ b₃ (lower b₂)) ⟩
  lift ((lower b₀ ⊕ lower b₁) ⊕ (b₃ ⊕ lower b₂))
    ≡⟨ cong (λ a → lift ((lower b₀ ⊕ lower b₁) ⊕ a)) (⊕-comm b₃ (lower b₂)) ⟩
  lift ((lower b₀ ⊕ lower b₁) ⊕ (lower b₂ ⊕ b₃))
    ≡⟨ cong lift (⊕-assoc (lower b₀ ⊕ lower b₁) (lower b₂) b₃) ⟩
  lift (((lower b₀ ⊕ lower b₁) ⊕ lower b₂) ⊕ b₃)
    ≡⟨ cong lift (⊕-comm ((lower b₀ ⊕ lower b₁) ⊕ lower b₂) b₃) ⟩
  lift (b₃ ⊕ ((lower b₀ ⊕ lower b₁) ⊕ lower b₂))
    ≡⟨ sym (+∙ₜ b₃ ((lower b₀ ⊕ lower b₁) ⊕ lower b₂)) ⟩
  +ₜₐ ∙ₜ b₃ (lift ((lower b₀ ⊕ lower b₁) ⊕ lower b₂)) ∎))))

-- We show that the ternary sum is also contractible

isContrTriSumBool : ∀ {ℓ} → isContr (triSum {ℓ} ∙ₜ ∙ₜ ∙ₜ)
isContrTriSumBool = (isTriSumBool , λ S → ΣPathP (
  Σ≡Prop (λ _ → isPropPropTrunc) (ua (lemma2 S)) ,
    ΣPathPProp (λ _ →  isPropΠ ( λ x → isPropΠ (λ y → isPropΠ (λ z → isPropΠ (λ b → isProp×2
      ( isSetTors (S .fst) _ _)
  (isSetTors (S .fst) _ _) (isSetTors (S .fst) _ _))))) )
    (funExt (λ α → funExt (λ β → funExt (λ γ → toPathP (
  transport (ua (lemma2 S)) (lift ((lower α ⊕ lower β) ⊕ lower γ))
    ≡⟨ uaβ (lemma2 S) (lift ((lower α ⊕ lower β) ⊕ lower γ)) ⟩
  S .snd .fst (lift ((lower α ⊕ lower β) ⊕ lower γ)) (lift false) (lift false)
    ≡⟨ cong (λ a → S .snd .fst (lift a) (lift false) (lift false))
      (sym (⊕-assoc (lower α) (lower β) (lower γ)) ∙ ⊕-comm (lower α) (lower β ⊕ lower γ)) ⟩
  S .snd .fst (lift ((lower β ⊕ lower γ) ⊕ lower α)) (lift false) (lift false)
    ≡⟨ cong (λ a → S .snd .fst a (lift false) (lift false))
      (sym (+∙ₜ (lower β ⊕ lower γ) (lower α))) ⟩
  S .snd .fst (+ₜₐ ∙ₜ (lower β ⊕ lower γ) α) (lift false) (lift false)
    ≡⟨ S .snd .snd α (lift false) (lift false) (lower β ⊕ lower γ) .fst ⟩
  +ₜₐ (fst S) (lower β ⊕ lower γ) (S .snd .fst α (lift false) (lift false))
    ≡⟨ cong (λ a → a .fst (S .snd .fst α (lift false) (lift false)))
      (sym (assoc+ₜ (fst S) (lower β) (lower γ))) ⟩
  +ₜₐ (fst S) (lower γ) (+ₜₐ (fst S) (lower β) (S .snd .fst α (lift false) (lift false)))
    ≡⟨ cong (λ a → +ₜₐ (fst S) (lower γ) a)
      (sym (S .snd .snd α (lift false) (lift false) (lower β) .snd .fst)) ⟩
  +ₜₐ (fst S) (lower γ) (S .snd .fst α (+ₜₐ ∙ₜ (lower β) (lift false)) (lift false))
    ≡⟨ cong (λ a → +ₜₐ (fst S) (lower γ) (S .snd .fst α a (lift false))) (+∙ₜ (lower β) false)⟩
  +ₜₐ (fst S) (lower γ) (S .snd .fst α (lift (lower β ⊕ false)) (lift false))
    ≡⟨ cong (λ a → +ₜₐ (fst S) (lower γ) (S .snd .fst α (lift a) (lift false)))
      (⊕-identityʳ (lower β)) ⟩
  +ₜₐ (fst S) (lower γ) (S .snd .fst α β (lift false))
    ≡⟨ sym (S .snd .snd α β (lift false) (lower γ) .snd .snd) ⟩
  S .snd .fst α β (+ₜₐ ∙ₜ (lower γ) (lift false))
    ≡⟨ cong (λ a → S .snd .fst α β a) (+∙ₜ (lower γ) false) ⟩
  S .snd .fst α β (lift (lower γ ⊕ false))
    ≡⟨ cong (λ a → S .snd .fst α β (lift a)) (⊕-identityʳ (lower γ)) ⟩
  S .snd .fst α β γ ∎
  )))))) )
  where
  lemma : ∀ {ℓ} → (S : triSum {ℓ} ∙ₜ ∙ₜ ∙ₜ) →
    (λ x → S .snd .fst x (lift false) (lift false)) ≡
    (λ x → +ₜₐ (fst S) (lower x) (S .snd .fst (lift false) (lift false) (lift false)))
  lemma (S , +ˢ , ≡ˢ) = funExt (λ x →
    +ˢ x (lift false) (lift false)
      ≡⟨ cong (λ a → +ˢ (a .fst x) (lift false) (lift false))
        (sym (+ₜ0 ∙ₜ)) ⟩
    +ˢ (+ₜₐ ∙ₜ false x) (lift false) (lift false)
      ≡⟨ cong (λ a → +ˢ a (lift false) (lift false)) (+∙ₜ false (lower x)) ⟩
    +ˢ (lift (false ⊕ lower x)) (lift false) (lift false)
      ≡⟨ cong (λ a → +ˢ (lift a) (lift false) (lift false)) (⊕-comm false (lower x)) ⟩
    +ˢ (lift (lower x ⊕ false)) (lift false) (lift false)
      ≡⟨ cong (λ a → +ˢ a (lift false) (lift false)) (sym (+∙ₜ (lower x) false)) ⟩
    +ˢ (+ₜₐ ∙ₜ (lower x) (lift false)) (lift false) (lift false)
      ≡⟨ ≡ˢ (lift false) (lift false) (lift false) (lower x) .fst ⟩
    +ₜₐ S (lower x) (+ˢ (lift false) (lift false) (lift false)) ∎)
  lemma2 : ∀ {ℓ} → (S : triSum {ℓ} ∙ₜ ∙ₜ ∙ₜ) → isTriSumBool {ℓ} .fst .fst ≃ S .fst .fst
  lemma2 (S , +ˢ , ≡ˢ) = (λ x → +ˢ x (lift false) (lift false)) ,
    subst isEquiv (sym (lemma (S , +ˢ , ≡ˢ))) ((invEquiv (LiftEquiv {A = Bool}) ∙ₑ
    ((λ b → +ₜₐ S b (+ˢ (lift false) (lift false) (lift false))) , isTrans+ₜ S (+ˢ (lift false)
    (lift false) (lift false)))) .snd)

isContrTriSum : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) (Z : TwoTorsor ℓ) → isContr (triSum X Y Z)
isContrTriSum {ℓ} X Y Z = rec isPropIsContr
  (λ e → rec isPropIsContr (λ e' → rec isPropIsContr (λ e'' →
  lemma2 (TwoTorsor ℓ) (TwoTorsor ℓ) (TwoTorsor ℓ) (λ A → λ B → λ C →
  isContr (triSum A B C)) ∙ₜ X ∙ₜ Y ∙ₜ Z
    (lemma1 X e) (lemma1 Y e') (lemma1 Z e'') isContrTriSumBool) (Z .snd)) (Y .snd)) (X .snd)
  where
  lemma1 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (⟨ X ⟩ ≃ Bool) → ∙ₜ ≡ X
  lemma1 X p = Σ≡Prop (λ _ → isPropPropTrunc) (sym (ua (p ∙ₑ LiftEquiv)))
  lemma2 : ∀ {ℓ ℓ' ℓ'' ℓ'''} → (A : Type ℓ) → (B : Type ℓ') → (C : Type ℓ'') →
    (D : A → B → C → Type ℓ''') → (a b : A) → (c d : B) → (e f : C) →
    (a ≡ b) → (c ≡ d) → (e ≡ f) → D a c e → D b d f
  lemma2 A B C D a b c d e f p q r t = transport (λ i → D (p i) (q i) (r i)) t

-- (X + Y) + Z and X + (Y + Z) are ternary sums

isTriSumXYPlusZ : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) (Z : TwoTorsor ℓ) → triSum X Y Z
isTriSumXYPlusZ X Y Z = ((X +ᵀ Y) +ᵀ Z ,
  ((λ x → λ y → λ z → XYZ .fst .snd (XY . fst .snd x y) z) , (λ x → λ y → λ z → λ b →(
  XYZ .fst .snd (XY .fst .snd (+ₜₐ X b x) y) z
    ≡⟨ cong (λ a → XYZ .fst .snd a z) (XY .snd x y b .fst) ⟩
  XYZ .fst .snd (+ₜₐ (X +ᵀ Y) b (XY .fst .snd x y)) z
    ≡⟨ XYZ .snd (XY .fst .snd x y) z b .fst ⟩
  +ₜₐ ((X +ᵀ Y) +ᵀ Z) b (XYZ .fst .snd (XY .fst .snd x y) z) ∎
  ), (
  XYZ .fst .snd (XY .fst .snd x (+ₜₐ Y b y)) z
    ≡⟨ cong (λ a → XYZ .fst .snd a z) (XY .snd x y b .snd) ⟩
  XYZ .fst .snd (+ₜₐ (X +ᵀ Y) b (XY .fst .snd x y)) z
    ≡⟨ XYZ .snd (XY .fst .snd x y) z b .fst ⟩
  +ₜₐ ((X +ᵀ Y) +ᵀ Z) b (XYZ .fst .snd (XY .fst .snd x y) z) ∎
  ) , XYZ .snd (XY .fst .snd x y) z b .snd)))
  where
  XY : +²ᵀ X Y
  XY = isContr+²ᵀ X Y .fst
  XYZ : +²ᵀ (X +ᵀ Y) Z
  XYZ = isContr+²ᵀ (X +ᵀ Y) Z .fst

isTriSumXPlusYZ : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) (Z : TwoTorsor ℓ) → triSum X Y Z
isTriSumXPlusYZ X Y Z = (X +ᵀ Y +ᵀ Z ,
  ((λ x → λ y → λ z → XYZ .fst .snd x (YZ . fst .snd y z)) , (λ x → λ y → λ z → λ b →(
  XYZ .snd x (YZ .fst .snd y z) b .fst , (
  XYZ .fst .snd x (YZ .fst .snd (+ₜₐ Y b y) z)
    ≡⟨ cong (λ a → XYZ .fst .snd x a) (YZ .snd y z b .fst) ⟩
  XYZ .fst .snd x (+ₜₐ (Y +ᵀ Z) b (YZ .fst .snd y z))
    ≡⟨ XYZ .snd x (YZ .fst .snd y z) b .snd ⟩
  +ₜₐ (X +ᵀ Y +ᵀ Z) b (XYZ .fst .snd x (YZ .fst .snd y z)) ∎
  ), (
  XYZ .fst .snd x (YZ .fst .snd y (+ₜₐ Z b z))
    ≡⟨ cong (λ a → XYZ .fst .snd x a) (YZ .snd y z b .snd) ⟩
  XYZ .fst .snd x (+ₜₐ (Y +ᵀ Z) b (YZ .fst .snd y z))
    ≡⟨ XYZ .snd x (YZ .fst .snd y z) b .snd ⟩
  +ₜₐ (X +ᵀ Y +ᵀ Z) b (XYZ .fst .snd x (YZ .fst .snd y z)) ∎
  )))))
  where
  YZ : +²ᵀ Y Z
  YZ = isContr+²ᵀ Y Z .fst
  XYZ : +²ᵀ X (Y +ᵀ Z)
  XYZ = isContr+²ᵀ X (Y +ᵀ Z) .fst

-- We deduce the associativity of the sum

assoc+ᵀ : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) (Z : TwoTorsor ℓ) → (X +ᵀ Y) +ᵀ Z ≡ X +ᵀ Y +ᵀ Z
assoc+ᵀ X Y Z = Σ≡Prop (λ _ → isPropPropTrunc) (PathPΣ (PathPΣ (isContr→isProp (isContrTriSum X Y Z)
    (isTriSumXYPlusZ X Y Z) (isTriSumXPlusYZ X Y Z)) .fst) .fst)

-- Now we define the equivalence leading to the homogeneity of K(S2,1)

≃+ᵀ : ∀ {ℓ} → (X : TwoTorsor ℓ) → TwoTorsor ℓ ≃ TwoTorsor ℓ
≃+ᵀ X = _+ᵀ X , involIsEquiv (λ A → assoc+ᵀ A X X ∙ cong (λ a → A +ᵀ a) (invTors X) ∙ sumUnit A)

-- K(S2,1) is homogeneous

HomoTors : ∀ {ℓ} → (X : TwoTorsor ℓ) → (TwoTorsor ℓ , ∙ₜ {ℓ = ℓ}) ≡ (TwoTorsor ℓ , X)
HomoTors {ℓ} X = pointed-sip (TwoTorsor ℓ , ∙ₜ) (TwoTorsor ℓ , X) (≃+ᵀ X , sym+ᵀ ∙ₜ X ∙ sumUnit X)

HomoEqRefl : ∀ {ℓ} → HomoTors {ℓ} ∙ₜ ≡ refl
HomoEqRefl {ℓ = ℓ} = cong (pointed-sip (TwoTorsor ℓ , ∙ₜ) (TwoTorsor ℓ , ∙ₜ))
  (ΣPathP hom≡≃) ∙ pointed-sip-idEquiv∙ (TwoTorsor ℓ , ∙ₜ)
  where
  hom≡ : Σ[ p ∈ (_+ᵀ ∙ₜ) ≡ idfun (TwoTorsor ℓ) ] PathP (λ i → p i ∙ₜ ≡ ∙ₜ)
    (sym+ᵀ ∙ₜ ∙ₜ ∙ sumUnit ∙ₜ) refl
  hom≡ = PathPΣ (→∙Homogeneous≡ HomoTors (funExt sumUnit))
  hom≡1 : (_+ᵀ ∙ₜ) ≡ idfun (TwoTorsor ℓ)
  hom≡1 = hom≡ .fst
  hom≡2 : PathP (λ i → hom≡1 i ∙ₜ ≡ ∙ₜ) (sym+ᵀ ∙ₜ ∙ₜ ∙ sumUnit ∙ₜ) refl
  hom≡2 = hom≡ .snd
  hom≡1≃ : ≃+ᵀ ∙ₜ ≡ idEquiv (TwoTorsor ℓ)
  hom≡1≃ = equivEq hom≡1
  hom≡2≃ : PathP (λ i → hom≡1≃ i .fst ∙ₜ ≡ ∙ₜ) (sym+ᵀ ∙ₜ ∙ₜ ∙ sumUnit ∙ₜ) refl
  hom≡2≃ = hom≡2
  hom≡≃ : Σ[ p ∈ ≃+ᵀ ∙ₜ ≡ idEquiv (TwoTorsor ℓ)] PathP (λ i → p i .fst ∙ₜ ≡ ∙ₜ)
    (sym+ᵀ ∙ₜ ∙ₜ ∙ sumUnit ∙ₜ) refl
  hom≡≃ = hom≡1≃ , hom≡2≃
