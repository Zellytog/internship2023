open import Cubical.Data.Nat
open import Agda.Primitive
open import Cubical.Data.Bool
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum renaming (rec to sumrec)
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Relation.Nullary.Base
open import Cubical.Data.Sigma
open import Sign.TwoTorsors.Base
open import Cubical.Functions.Involution

module Sign.TwoTorsors.Sum where

private
  variable
    ℓ : Level

{- We want to prove that K(S2,1) is an homogeneous type, i.e. that for any two X Y : K(S2,1) we can
   find an equality (K(S2,1),X) = (K(S2,1) = Y), which caracterises the space of an abelian group.
   To do this, we need to introduce the notion of sum of torsors, which then allows us to define the
   expected equality.
   The sum of X and Y will be a torsor Z with + : X → Y → Z commuting with the action on torsors. -}

module _
  ((X , e) : TwoTorsor ℓ)
  ((Y , e') : TwoTorsor ℓ)
    where

  compatAct : (Z : TwoTorsor ℓ) → (addi : X → Y → (fst Z)) → Type ℓ
  compatAct Z addi = (x : X) → (y : Y) → (b : Lift {_} {ℓ} Bool) →
    ((addi (actTors (X , e) b .fst x) y ≡ actTors Z b .fst (addi x y)) ×
    (addi x (actTors (Y , e') b .fst y) ≡ actTors Z b .fst (addi x y)))

  sumTors : Type (lsuc ℓ)
  sumTors = Σ[ S ∈ (Σ[ Z ∈ (TwoTorsor ℓ)] (X → Y → (fst Z)))]
    (compatAct (fst S) (snd S))

  isPropcompAct : ((Z , e'') : TwoTorsor ℓ) → (addi : X → Y → Z)
    → isProp (compatAct (Z , e'') addi)
  isPropcompAct (Z , e'') addi α β = funExt (λ x → funExt (λ y → funExt (λ b → ≡-×
    (isSetTors (Z , e'') _ _ (fst (α x y b)) (fst (β x y b)))
    (isSetTors (Z , e'') _ _ (snd (α x y b)) (snd (β x y b))) )))

  sumEq : ((((Z , e) , addi) , a) : sumTors) →
          ((((Z' , e') , addi') , a') : sumTors) →
    (p : Z ≡ Z') → PathP (λ i → (X → Y → p i)) addi addi' →
    (((Z , e) , addi) , a) ≡ (((Z' , e') , addi') , a')
  sumEq ((Z , addi) , a) ((Z' , addi') , a') p q = ΣPathPProp (λ Z → isPropcompAct (fst Z) (snd Z))
    (ΣPathP (Σ≡Prop (λ _ → isPropPropTrunc) p , q))

-- We can define Bool + Bool to be (Bool, ⊕)

issumBool : ∀ {ℓ} → sumTors {ℓ = ℓ} pointedTors pointedTors
issumBool {ℓ} = (pointedTors , (λ a → λ b → lift (lower a ⊕ lower b))) ,
  (λ x → λ y → λ b → (
  lift (lower (actTors (Lift Bool , ∣ refl ∣₁) b .fst x) ⊕ lower y)
    ≡⟨ cong (λ z → lift (lower z ⊕ lower y)) (actOnBool b x) ⟩
  lift ((lower b ⊕ lower x) ⊕ lower y)
    ≡⟨ cong (λ z → lift z) (sym (⊕-assoc (lower b) (lower x) (lower y))) ⟩
  lift (lower b ⊕ lower (lift {j = ℓ} (lower x ⊕ lower y)))
    ≡⟨ sym (actOnBool b (lift (lower x ⊕ lower y))) ⟩
  actTors (Lift Bool , ∣ refl ∣₁) b .fst (lift (lower x ⊕ lower y)) ∎), 
  (lift (lower x ⊕ lower (actTors (Lift Bool , ∣ refl ∣₁) b .fst y))
    ≡⟨ cong (λ z → lift (lower x ⊕ lower z)) (actOnBool b y) ⟩
  lift (lower x ⊕ (lower b ⊕ lower y))
    ≡⟨ cong (λ z → lift (lower x ⊕ z)) (⊕-comm (lower b) (lower y)) ⟩
  lift (lower x ⊕ (lower y ⊕ lower b))
    ≡⟨ cong (λ z → lift z) (⊕-assoc (lower x) (lower y) (lower b)) ⟩
  lift ((lower x ⊕ lower y) ⊕ lower b)
    ≡⟨ cong (λ z → lift z) (⊕-comm (lower x ⊕ lower y) (lower b)) ⟩
  lift (lower b ⊕ lower (lift {j = ℓ} (lower x ⊕ lower y)))
    ≡⟨ sym (actOnBool b (lift (lower x ⊕ lower y))) ⟩
  actTors (Lift Bool , ∣ refl ∣₁) b .fst (lift (lower x ⊕ lower y)) ∎))

-- We show that the universal property defines the sum uniquely,
-- which allow us to transport the result along the troncated paths.
-- We just have to prove that the type sumTors X Y is contractible for Bool Bool.

isContrSum : ∀ {ℓ} → (X : TwoTorsor ℓ) → (Y : TwoTorsor ℓ) → isContr (sumTors X Y)
isContrSum {ℓ} (X , e) (Y , e') = rec isPropIsContr (λ f → rec isPropIsContr (λ f' →
  subst2 (λ X → λ Y → isContr (sumTors X Y)) (Σ≡Prop (λ _ → isPropPropTrunc)
    {u = pointedTors} {v = (X , e)} (sym f)) 
  (Σ≡Prop (λ _ → isPropPropTrunc) {u = pointedTors} {v = (Y , e')} (sym f')) 
  (issumBool , (λ Z → sumEq {ℓ} pointedTors pointedTors issumBool Z (ua (equivBoolSum Z))
  ((funExt (λ α → funExt (λ β → toPathP (
    transport (ua (equivBoolSum Z)) (lift ((lower α) ⊕ (lower β)))
      ≡⟨ uaβ (equivBoolSum Z) (lift ((lower α) ⊕ (lower β))) ⟩
    snd (fst Z) (lift ((lower α) ⊕ (lower β))) (lift false)
      ≡⟨ cong (λ c → snd (fst Z) (lift c) (lift false)) (⊕-comm (lower α) (lower β)) ⟩
    snd (fst Z) (lift ((lower β) ⊕ (lower α))) (lift false)
      ≡⟨ cong (λ c → snd (fst Z) (c) (lift false)) (sym (actOnBool β α)) ⟩
    snd (fst Z) (actTors pointedTors β .fst α) (lift false)
      ≡⟨ fst ((snd Z) α (lift false) β) ⟩
    actTors (fst (fst Z)) β .fst (snd (fst Z) α (lift false))
      ≡⟨ sym (snd ((snd Z) α (lift false) β)) ⟩
    snd (fst Z) α (actTors pointedTors β .fst (lift false))
      ≡⟨ cong (λ c → snd (fst Z) α c) (actOnBool β (lift false)) ⟩
    snd (fst Z) α (lift ((lower β) ⊕ false))
      ≡⟨ cong (λ c → snd (fst Z) α (lift c)) (⊕-identityʳ (lower β)) ⟩
    snd (fst Z) α β ∎)))))) )
  ) e') e
  where
  equivBoolSum : (Z : sumTors {ℓ = ℓ} pointedTors pointedTors) →
    (fst (fst (fst (issumBool {ℓ}))) ≃ fst (fst (fst Z)))
  equivBoolSum Z = ((λ b → snd (fst Z) b (lift false)) ,
    subst isEquiv ((funExt (λ b → 
    actTors (fst (fst Z)) b .fst (snd (fst Z) (lift false) (lift false))
      ≡⟨ sym (fst (snd Z (lift false) (lift false) b)) ⟩
    snd (fst Z) (actTors (pointedTors) b .fst (lift false)) (lift false)
      ≡⟨ cong (λ x → snd (fst Z) x (lift false)) (actOnBool b (lift false)) ⟩
    snd (fst Z) (lift ((lower b) ⊕ false)) (lift false)
      ≡⟨ cong (λ x → snd (fst Z) (lift x) (lift false)) (⊕-identityʳ (lower b)) ⟩
    snd (fst Z) b (lift false) ∎
    ))) (isEquivAction (fst (fst Z)) (snd (fst Z) (lift false) (lift false))))

takeSum : TwoTorsor ℓ → TwoTorsor ℓ → TwoTorsor ℓ
takeSum X Y = isContrSum X Y .fst .fst .fst

-- We will prove that this sum makes the type of 2-torsors a monoidal symmetric categories
-- with inverses.
-- For the equalities, we will prove that two objects have the same universal properties.

-- It is symmetric

symSum : (X : TwoTorsor ℓ) → (Y : TwoTorsor ℓ) → takeSum X Y ≡ takeSum Y X
symSum X Y = Σ≡Prop (λ _ → isPropPropTrunc) (PathPΣ (PathPΣ (PathPΣ (snd (isContrSum X Y) 
    ((takeSum Y X , (λ y → λ x → isContrSum Y X .fst .fst .snd x y)) ,
    (λ y → λ x → λ b → isContrSum Y X .fst .snd x y b .snd , isContrSum Y X .fst .snd x y b .fst))) .fst) .fst) .fst)

-- The point (Bool , ∣ refl ∣₁) is neutral

sumUnit : (X : TwoTorsor ℓ) → takeSum X pointedTors ≡ X
sumUnit X = Σ≡Prop (λ _ → isPropPropTrunc) (PathPΣ (PathPΣ (PathPΣ (snd (isContrSum X pointedTors)
    ((X , (λ x → λ y → actTors X y .fst x)) ,
    (λ x → λ y → λ b → (
      actTors X y .fst (actTors X b .fst x)
        ≡⟨ cong (λ a → a .fst x) (isAssocAct X b y) ⟩
      actTors X (lift (lower b ⊕ lower y)) .fst x
        ≡⟨ cong (λ a → actTors X (lift a) .fst x) (⊕-comm (lower b) (lower y)) ⟩
      actTors X (lift (lower y ⊕ lower b)) .fst x
        ≡⟨ cong (λ a → a .fst x) (sym (isAssocAct X y b)) ⟩
      actTors X b .fst (actTors X y .fst x)∎
    ) , (
      actTors X (actTors pointedTors b .fst y) .fst x
        ≡⟨ cong (λ a → actTors X a .fst x) (actOnBool b y) ⟩
      actTors X (lift (lower b ⊕ lower y)) .fst x
        ≡⟨ cong (λ a → actTors X (lift a) .fst x) (⊕-comm (lower b) (lower y)) ⟩
      actTors X (lift (lower y ⊕ lower b)) .fst x
        ≡⟨ cong (λ a → a .fst x) (sym (isAssocAct X y b)) ⟩
      actTors X b .fst (actTors X y .fst x)∎ )))) .fst) .fst) .fst)

-- The inverse of X is itself, thus X + X ≡ Bool

invTors : (X : TwoTorsor ℓ) → takeSum X X ≡ pointedTors
invTors X = Σ≡Prop (λ _ → isPropPropTrunc) (PathPΣ (PathPΣ (PathPΣ (snd (isContrSum X X) 
  (testIntermFin X)) .fst) .fst) .fst)
  where
  plusBoolSum : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → Lift {_} {ℓ} Bool
  plusBoolSum X x y = sumrec (λ _ → lift false) (λ _ → lift true) (dichotomyTors X x y)
  lemma1 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → (b : Lift {_} {ℓ} Bool) →
    plusBoolSum X (actTors X b .fst x) y ≡ actTors pointedTors b .fst (plusBoolSum X x y)
  lemma1 {ℓ} X x y (lift true) = sumrec (λ α → sym (
    actTors pointedTors (lift true) .fst (plusBoolSum X x y)
      ≡⟨ cong (λ a → actTors pointedTors (lift true) .fst
        (sumrec {C = Lift Bool} (λ _ → lift false) (λ _ → lift true) a))
        (isPropDichotomyTors X x y (dichotomyTors X x y) (inl α)) ⟩
    actTors pointedTors (lift true) .fst (sumrec (λ _ → lift false) (λ _ → lift true)
      (inl {B = x ≡ actTors X (lift true) .fst y} α))
      ≡⟨ refl ⟩
    actTors pointedTors (lift true) .fst (lift false)
      ≡⟨ actOnBool (lift true) (lift false) ⟩
    sumrec (λ _ → lift false) (λ _ → lift true) (inr {A = actTors X (lift true) .fst x ≡ y}
      (cong (λ b → actTors X (lift true) .fst b) α)) 
      ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
        (isPropDichotomyTors X (actTors X (lift true) .fst x) y
    (inr (cong (λ b → actTors X (lift true) .fst b) α))
      (dichotomyTors X (actTors X (lift true) .fst x) y)) ⟩
      plusBoolSum X (actTors X (lift true) .fst x) y ∎)) (λ α → sym (
      actTors pointedTors (lift true) .fst (plusBoolSum X x y)
      ≡⟨ cong (λ a → actTors pointedTors (lift true) .fst
        (sumrec {C = Lift Bool} (λ _ → lift false) (λ _ → lift true) a))
        (isPropDichotomyTors X x y (dichotomyTors X x y) (inr α)) ⟩
    actTors pointedTors (lift true) .fst
      (sumrec (λ _ → lift false) (λ _ → lift true) (inr {A = x ≡ y} α))
      ≡⟨ refl ⟩
    actTors pointedTors (lift true) .fst (lift true)
      ≡⟨ actOnBool (lift true) (lift true) ⟩
    sumrec (λ _ → lift false) (λ _ → lift true)
      (inl {B = actTors X (lift true) .fst x ≡ actTors X (lift true) .fst y} 
      ( (cong (λ b → actTors X (lift true) .fst b) α)
        ∙ (cong (λ a → a .fst y) (isAssocAct X (lift true) (lift true)))
        ∙ (cong (λ a → a .fst y) (isNeutralFalse X))))
      ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
        (isPropDichotomyTors X (actTors X (lift true) .fst x) y
        (inl {B = actTors X (lift true) .fst x ≡ actTors X (lift true) .fst y} 
          ( (cong (λ b → actTors X (lift true) .fst b) α)
          ∙ (cong (λ a → a .fst y) (isAssocAct X (lift true) (lift true)))
          ∙ (cong (λ a → a .fst y) (isNeutralFalse X))))
        (dichotomyTors X (actTors X (lift true) .fst x) y)) ⟩
    plusBoolSum X (actTors X (lift true) .fst x) y ∎
    )) (dichotomyTors X x y) 
  lemma1 X x y (lift false) = cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true)
    (dichotomyTors X (a .fst x) y)) (isNeutralFalse X) ∙
    sym ((cong (λ a → a .fst (plusBoolSum X x y))) (isNeutralFalse pointedTors))
  lemmaForLemma2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → (x ≡ y) →
    (x ≡ actTors X (lift true) .fst y) ⊎
    (x ≡ actTors X (lift true) .fst (actTors X (lift true) .fst y))
  lemmaForLemma2 X x y α = inr (α ∙ sym (isNilFlip X y))
  lemma2ForLemma2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → (x ≡ y) →
    actTors pointedTors (lift {j = ℓ} true) .fst (plusBoolSum X x y) ≡
    plusBoolSum X x (actTors X (lift true) .fst y)
  lemma2ForLemma2 X x y α = actTors pointedTors (lift true) .fst (plusBoolSum X x y)
    ≡⟨ cong (λ a → actTors pointedTors (lift true) .fst
      (sumrec {C = Lift Bool} (λ _ → lift false) (λ _ → lift true) a))
      (isPropDichotomyTors X x y (dichotomyTors X x y) (inl α)) ⟩
    actTors pointedTors (lift true) .fst (sumrec (λ _ → lift false) (λ _ → lift true)
      (inl {B = x ≡ actTors X (lift true) .fst y} α))
      ≡⟨ refl ⟩
    actTors pointedTors (lift true) .fst (lift false)
      ≡⟨ actOnBool (lift true) (lift false) ⟩
    sumrec (λ _ → lift false) (λ _ → lift true) (lemmaForLemma2 X x y α)
        ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
          (isPropDichotomyTors X x (actTors X (lift true) .fst y)
          (lemmaForLemma2 X x y α) (dichotomyTors X x (actTors X (lift true) .fst y))) ⟩
    plusBoolSum X x (actTors X (lift true) .fst y) ∎
  lemma3ForLemma2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) →
    (x ≡ actTors X (lift true) .fst y) →
    actTors pointedTors (lift {j = ℓ} true) .fst (plusBoolSum X x y) ≡
    plusBoolSum X x (actTors X (lift true) .fst y)
  lemma3ForLemma2 X x y α = actTors pointedTors (lift true) .fst (plusBoolSum X x y)
    ≡⟨ cong (λ a → actTors pointedTors (lift true) .fst
      (sumrec (λ _ → lift false) (λ _ → lift true) a))
      (isPropDichotomyTors X x y (dichotomyTors X x y) (inr α)) ⟩
    actTors pointedTors (lift true) .fst (sumrec (λ _ → lift false) (λ _ → lift true)
      (inr {A = x ≡ y} α))
      ≡⟨ refl ⟩
    actTors pointedTors (lift true) .fst (lift true)
      ≡⟨ actOnBool (lift true) (lift true) ⟩
    sumrec (λ _ → lift false) (λ _ → lift true)
      (inl {B = x ≡ actTors X (lift true) .fst (actTors X (lift true) .fst y)} α)
      ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
        (isPropDichotomyTors X x (actTors X (lift true) .fst y)
        (inl α) (dichotomyTors X x (actTors X (lift true) .fst y))) ⟩
    plusBoolSum X x (actTors X (lift true) .fst y) ∎
  lemma4ForLemma2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) →
    actTors pointedTors (lift {j = ℓ} false) .fst (plusBoolSum X x y) ≡
    plusBoolSum X x (actTors X (lift false) .fst y)
  lemma4ForLemma2 X x y = sumrec (λ α → (actTors pointedTors (lift false) .fst (plusBoolSum X x y)
    ≡⟨ cong (λ a → actTors pointedTors (lift false) .fst
      (sumrec (λ _ → lift false) (λ _ → lift true) a))
      (isPropDichotomyTors X x y (dichotomyTors X x y)
      (inl {B = x ≡ actTors X (lift true) .fst y} α)) ⟩
    actTors pointedTors (lift false) .fst (sumrec (λ _ → lift false) (λ _ → lift true)
      (inl {B = x ≡ actTors X (lift true) .fst y} α))
      ≡⟨ refl ⟩
    actTors pointedTors (lift false) .fst (lift false)
      ≡⟨ actOnBool (lift false) (lift false) ⟩
    sumrec (λ _ → lift false) (λ _ → lift true)
      (inl {B = x ≡ actTors X (lift true) .fst (actTors X (lift false) .fst y)}
      (α ∙ sym (cong (λ a → a .fst y) (isNeutralFalse X))))
      ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
        (isPropDichotomyTors X x (actTors X (lift false) .fst y)
        (inl (α ∙ sym (cong (λ a → a .fst y) (isNeutralFalse X))))
        (dichotomyTors X x (actTors X (lift false) .fst y))) ⟩
    plusBoolSum X x (actTors X (lift false) .fst y) ∎)
    ) (λ α → actTors pointedTors (lift false) .fst (plusBoolSum X x y) 
      ≡⟨ cong (λ a → actTors pointedTors (lift false) .fst
        (sumrec (λ _ → lift false) (λ _ → lift true) a))
        (isPropDichotomyTors X x y (dichotomyTors X x y) (inr {A = x ≡ y} α)) ⟩
    actTors pointedTors (lift false) .fst (lift true)
      ≡⟨ actOnBool (lift false) (lift true) ⟩
    sumrec (λ _ → lift false) (λ _ → lift true) (inr {A = x ≡ actTors X (lift false) .fst y}
      (α ∙ sym (cong (λ a → actTors X (lift true) .fst (a .fst y)) (isNeutralFalse X))))
      ≡⟨ cong (λ a → sumrec (λ _ → lift false) (λ _ → lift true) a)
        (isPropDichotomyTors X x (actTors X (lift false) .fst y)
        (inr {A = x ≡ actTors X (lift false) .fst y}
        (α ∙ sym (cong (λ a → actTors X (lift true) .fst (a .fst y)) (isNeutralFalse X))))
        (dichotomyTors X x (actTors X (lift false) .fst y))) ⟩
    plusBoolSum X x (actTors X (lift false) .fst y) ∎) (dichotomyTors X x y)
  lemma2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → (b : Lift {_} {ℓ} Bool) →
    plusBoolSum X x (actTors X b .fst y) ≡ actTors pointedTors b .fst (plusBoolSum X x y)
  lemma2 X x y (lift true) = sym (sumrec (lemma2ForLemma2 X x y) (lemma3ForLemma2 X x y)
    (dichotomyTors X x y))
  lemma2 X x y (lift false) = sym (lemma4ForLemma2 X x y)
  testInterm : ∀ {ℓ} → (X : TwoTorsor ℓ) → Σ[ S ∈ (Σ[ Z ∈ (TwoTorsor ℓ)] (fst X → fst X → (fst Z)))]
    (compatAct X X (fst S) (snd S))
  testInterm X = (pointedTors , plusBoolSum X) , (λ x → λ y → λ b → lemma1 X x y b , lemma2 X x y b)
  testIntermFin : ∀ {ℓ} → (X : TwoTorsor ℓ) → sumTors X X
  testIntermFin X = testInterm X

-- We will prove that the sum is associative, but we first need to introduce ternary sum


triSum : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) (Z : TwoTorsor ℓ) → Type (lsuc ℓ)
triSum {ℓ} X Y Z = Σ[ A ∈ (TwoTorsor ℓ) ] (Σ[ addi ∈ (fst X → fst Y → fst Z → fst A) ]
  ((x : fst X) (y : fst Y) (z : fst Z) (b : Lift {_} {ℓ} Bool) →
  (addi (actTors X b .fst x) y z ≡ actTors A b .fst (addi x y z)) ×
  (addi x (actTors Y b .fst y) z ≡ actTors A b .fst (addi x y z)) ×
  (addi x y (actTors Z b .fst z) ≡ actTors A b .fst (addi x y z)) ))

isTriSumBool : ∀ {ℓ} → triSum {ℓ} pointedTors pointedTors pointedTors
isTriSumBool = (pointedTors , ((λ b₀ → λ b₁ → λ b₂ → lift (((lower b₀) ⊕ (lower b₁)) ⊕ (lower b₂))) ,
  (λ b₀ → λ b₁ → λ b₂ → λ b₃ →
  (lift ((lower (actTors pointedTors b₃ .fst b₀) ⊕ lower b₁) ⊕ lower b₂)
    ≡⟨ cong (λ a → lift ((lower a ⊕ lower b₁) ⊕ lower b₂)) (actOnBool b₃ b₀) ⟩
  lift (((lower b₃ ⊕ lower b₀) ⊕ lower b₁) ⊕ lower b₂)
    ≡⟨ cong (λ a → lift (a ⊕ lower b₂)) (sym (⊕-assoc (lower b₃) (lower b₀) (lower b₁))) ⟩
  lift ((lower b₃ ⊕ (lower b₀ ⊕ lower b₁)) ⊕ lower b₂)
    ≡⟨ cong lift (sym (⊕-assoc (lower b₃) (lower b₀ ⊕ lower b₁) (lower b₂))) ⟩
  lift (lower b₃ ⊕ ((lower b₀ ⊕ lower b₁) ⊕ lower b₂))
    ≡⟨ sym (actOnBool b₃ (lift ((lower b₀ ⊕ lower b₁) ⊕ lower b₂))) ⟩
  actTors pointedTors b₃ .fst (lift ((lower b₀ ⊕ lower b₁) ⊕ lower b₂)) ∎) ,
  (lift ((lower b₀ ⊕ lower (actTors pointedTors b₃ .fst b₁)) ⊕ lower b₂)
    ≡⟨ cong (λ a → lift ((lower b₀ ⊕ lower a) ⊕ lower b₂)) (actOnBool b₃ b₁) ⟩
  lift ((lower b₀ ⊕ (lower b₃ ⊕ lower b₁)) ⊕ lower b₂)
    ≡⟨ cong (λ a → lift ((lower b₀ ⊕ a) ⊕ lower b₂)) (⊕-comm (lower b₃) (lower b₁)) ⟩
  lift ((lower b₀ ⊕ (lower b₁ ⊕ lower b₃)) ⊕ lower b₂)
    ≡⟨ cong (λ a → lift (a ⊕ lower b₂)) (⊕-assoc (lower b₀) (lower b₁) (lower b₃)) ⟩
  lift (((lower b₀ ⊕ lower b₁) ⊕ lower b₃) ⊕ lower b₂)
    ≡⟨ cong lift (sym (⊕-assoc (lower b₀ ⊕ lower b₁) (lower b₃) (lower b₂))) ⟩
  lift ((lower b₀ ⊕ lower b₁) ⊕ (lower b₃ ⊕ lower b₂))
    ≡⟨ cong (λ a → lift ((lower b₀ ⊕ lower b₁) ⊕ a)) (⊕-comm (lower b₃) (lower b₂)) ⟩
  lift ((lower b₀ ⊕ lower b₁) ⊕ (lower b₂ ⊕ lower b₃))
    ≡⟨ cong lift (⊕-assoc (lower b₀ ⊕ lower b₁) (lower b₂) (lower b₃)) ⟩
  lift (((lower b₀ ⊕ lower b₁) ⊕ lower b₂) ⊕ lower b₃)
    ≡⟨ cong lift (⊕-comm ((lower b₀ ⊕ lower b₁) ⊕ lower b₂) (lower b₃)) ⟩
  lift (lower b₃ ⊕ ((lower b₀ ⊕ lower b₁) ⊕ lower b₂))
    ≡⟨ sym (actOnBool b₃ (lift ((lower b₀ ⊕ lower b₁) ⊕ lower b₂))) ⟩
  actTors pointedTors b₃ .fst (lift ((lower b₀ ⊕ lower b₁) ⊕ lower b₂)) ∎) ,
  (lift ((lower b₀ ⊕ lower b₁) ⊕ lower (actTors pointedTors b₃ .fst b₂))
    ≡⟨ cong (λ a → lift ((lower b₀ ⊕ lower b₁) ⊕ lower a)) (actOnBool b₃ b₂) ⟩
  lift ((lower b₀ ⊕ lower b₁) ⊕ (lower b₃ ⊕ lower b₂))
    ≡⟨ cong (λ a → lift ((lower b₀ ⊕ lower b₁) ⊕ a)) (⊕-comm (lower b₃) (lower b₂)) ⟩
  lift ((lower b₀ ⊕ lower b₁) ⊕ (lower b₂ ⊕ lower b₃))
    ≡⟨ cong lift (⊕-assoc (lower b₀ ⊕ lower b₁) (lower b₂) (lower b₃)) ⟩
  lift (((lower b₀ ⊕ lower b₁) ⊕ lower b₂) ⊕ lower b₃)
    ≡⟨ cong lift (⊕-comm ((lower b₀ ⊕ lower b₁) ⊕ lower b₂) (lower b₃)) ⟩
  lift (lower b₃ ⊕ ((lower b₀ ⊕ lower b₁) ⊕ lower b₂))
    ≡⟨ sym (actOnBool b₃ (lift ((lower b₀ ⊕ lower b₁) ⊕ lower b₂))) ⟩
  actTors pointedTors b₃ .fst (lift ((lower b₀ ⊕ lower b₁) ⊕ lower b₂)) ∎))))

-- We show that the ternary sum is also contractible

isContrTriSumBool : ∀ {ℓ} → isContr (triSum {ℓ} pointedTors pointedTors pointedTors)
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
      (sym (actOnBool (lift (lower β ⊕ lower γ)) α)) ⟩
  S .snd .fst (actTors pointedTors (lift (lower β ⊕ lower γ)) .fst α) (lift false) (lift false)
    ≡⟨ S .snd .snd α (lift false) (lift false) (lift (lower β ⊕ lower γ)) .fst ⟩
  actTors (fst S) (lift (lower β ⊕ lower γ)) .fst (S .snd .fst α (lift false) (lift false))
    ≡⟨ cong (λ a → a .fst (S .snd .fst α (lift false) (lift false))) (sym (isAssocAct (fst S) β γ)) ⟩
  actTors (fst S) γ .fst (actTors (fst S) β .fst (S .snd .fst α (lift false) (lift false)))
    ≡⟨ cong (λ a → actTors (fst S) γ .fst a)
      (sym (S .snd .snd α (lift false) (lift false) β .snd .fst)) ⟩
  actTors (fst S) γ .fst (S .snd .fst α (actTors pointedTors β .fst (lift false)) (lift false))
    ≡⟨ cong (λ a → actTors (fst S) γ .fst (S .snd .fst α a (lift false))) (actOnBool β (lift false))⟩
  actTors (fst S) γ .fst (S .snd .fst α (lift (lower β ⊕ false)) (lift false))
    ≡⟨ cong (λ a → actTors (fst S) γ .fst (S .snd .fst α (lift a) (lift false)))
      (⊕-identityʳ (lower β)) ⟩
  actTors (fst S) γ .fst (S .snd .fst α β (lift false))
    ≡⟨ sym (S .snd .snd α β (lift false) γ .snd .snd) ⟩
  S .snd .fst α β (actTors pointedTors γ .fst (lift false))
    ≡⟨ cong (λ a → S .snd .fst α β a) (actOnBool γ (lift false)) ⟩
  S .snd .fst α β (lift (lower γ ⊕ false))
    ≡⟨ cong (λ a → S .snd .fst α β (lift a)) (⊕-identityʳ (lower γ)) ⟩
  S .snd .fst α β γ ∎
  )))))) )
  where
  lemma : ∀ {ℓ} → (S : triSum {ℓ} pointedTors pointedTors pointedTors) →
    (λ x → S .snd .fst x (lift false) (lift false)) ≡
    (λ x → actTors (fst S) x .fst (S .snd .fst (lift false) (lift false) (lift false)))
  lemma S = funExt (λ x →
    S .snd .fst x (lift false) (lift false)
      ≡⟨ cong (λ a → S .snd .fst (a .fst x) (lift false) (lift false))
        (sym (isNeutralFalse pointedTors)) ⟩
    S .snd .fst (actTors pointedTors (lift false) .fst x) (lift false) (lift false)
      ≡⟨ cong (λ a → S .snd .fst a (lift false) (lift false)) (actOnBool (lift false) x) ⟩
    S .snd .fst (lift (false ⊕ lower x)) (lift false) (lift false)
      ≡⟨ cong (λ a → S .snd .fst (lift a) (lift false) (lift false)) (⊕-comm false (lower x)) ⟩
    S .snd .fst (lift (lower x ⊕ false)) (lift false) (lift false)
      ≡⟨ cong (λ a → S .snd .fst a (lift false) (lift false)) (sym (actOnBool x (lift false))) ⟩
    S .snd .fst (actTors pointedTors x .fst (lift false)) (lift false) (lift false)
      ≡⟨ S .snd .snd (lift false) (lift false) (lift false) x .fst ⟩
    actTors (fst S) x .fst (S .snd .fst (lift false) (lift false) (lift false)) ∎)
  lemma2 : ∀ {ℓ} → (S : triSum {ℓ} pointedTors pointedTors pointedTors) →
    isTriSumBool {ℓ} .fst .fst ≃ S .fst .fst
  lemma2 S = (λ x → S .snd .fst x (lift false) (lift false)) ,
    subst isEquiv (sym (lemma S)) (isEquivAction (fst S)
      (S .snd .fst (lift false) (lift false) (lift false)))

isContrTriSum : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) (Z : TwoTorsor ℓ) → isContr (triSum X Y Z)
isContrTriSum {ℓ} X Y Z = rec isPropIsContr
  (λ e → rec isPropIsContr (λ e' → rec isPropIsContr (λ e'' →
  lemma2 (TwoTorsor ℓ) (TwoTorsor ℓ) (TwoTorsor ℓ) (λ A → λ B → λ C →
  isContr (triSum A B C)) pointedTors X pointedTors Y pointedTors Z
    (lemma1 X e) (lemma1 Y e') (lemma1 Z e'') isContrTriSumBool) (Z .snd)) (Y .snd)) (X .snd)
  where
  lemma1 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (fst X ≡ Lift {_} {ℓ} Bool) → pointedTors ≡ X
  lemma1 X p = Σ≡Prop (λ _ → isPropPropTrunc) (sym p)
  lemma2 : ∀ {ℓ ℓ' ℓ'' ℓ'''} → (A : Type ℓ) → (B : Type ℓ') → (C : Type ℓ'') →
    (D : A → B → C → Type ℓ''') → (a b : A) → (c d : B) → (e f : C) →
    (a ≡ b) → (c ≡ d) → (e ≡ f) → D a c e → D b d f
  lemma2 A B C D a b c d e f p q r t = transport (λ i → D (p i) (q i) (r i)) t

-- (X + Y) + Z and X + (Y + Z) are ternary sums

isTriSumXYPlusZ : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) (Z : TwoTorsor ℓ) → triSum X Y Z
isTriSumXYPlusZ X Y Z = (takeSum (takeSum X Y) Z ,
  ((λ x → λ y → λ z → XYZ .fst .snd (XY . fst .snd x y) z) , (λ x → λ y → λ z → λ b →(
  XYZ .fst .snd (XY .fst .snd (actTors X b .fst x) y) z
    ≡⟨ cong (λ a → XYZ .fst .snd a z) (XY .snd x y b .fst) ⟩
  XYZ .fst .snd (actTors (takeSum X Y) b .fst (XY .fst .snd x y)) z
    ≡⟨ XYZ .snd (XY .fst .snd x y) z b .fst ⟩
  actTors (takeSum (takeSum X Y) Z) b .fst (XYZ .fst .snd (XY .fst .snd x y) z) ∎
  ), (
  XYZ .fst .snd (XY .fst .snd x (actTors Y b .fst y)) z
    ≡⟨ cong (λ a → XYZ .fst .snd a z) (XY .snd x y b .snd) ⟩
  XYZ .fst .snd (actTors (takeSum X Y) b .fst (XY .fst .snd x y)) z
    ≡⟨ XYZ .snd (XY .fst .snd x y) z b .fst ⟩
  actTors (takeSum (takeSum X Y) Z) b .fst (XYZ .fst .snd (XY .fst .snd x y) z) ∎
  ) , XYZ .snd (XY .fst .snd x y) z b .snd)))
  where
  XY : sumTors X Y
  XY = isContrSum X Y .fst
  XYZ : sumTors (takeSum X Y) Z
  XYZ = isContrSum (takeSum X Y) Z .fst

isTriSumXPlusYZ : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) (Z : TwoTorsor ℓ) → triSum X Y Z
isTriSumXPlusYZ X Y Z = (takeSum X (takeSum Y Z) ,
  ((λ x → λ y → λ z → XYZ .fst .snd x (YZ . fst .snd y z)) , (λ x → λ y → λ z → λ b →(
  XYZ .snd x (YZ .fst .snd y z) b .fst , (
  XYZ .fst .snd x (YZ .fst .snd (actTors Y b .fst y) z)
    ≡⟨ cong (λ a → XYZ .fst .snd x a) (YZ .snd y z b .fst) ⟩
  XYZ .fst .snd x (actTors (takeSum Y Z) b .fst (YZ .fst .snd y z))
    ≡⟨ XYZ .snd x (YZ .fst .snd y z) b .snd ⟩
  actTors (takeSum X (takeSum Y Z)) b .fst (XYZ .fst .snd x (YZ .fst .snd y z)) ∎
  ), (
  XYZ .fst .snd x (YZ .fst .snd y (actTors Z b .fst z))
    ≡⟨ cong (λ a → XYZ .fst .snd x a) (YZ .snd y z b .snd) ⟩
  XYZ .fst .snd x (actTors (takeSum Y Z) b .fst (YZ .fst .snd y z))
    ≡⟨ XYZ .snd x (YZ .fst .snd y z) b .snd ⟩
  actTors (takeSum X (takeSum Y Z)) b .fst (XYZ .fst .snd x (YZ .fst .snd y z)) ∎
  )))))
  where
  YZ : sumTors Y Z
  YZ = isContrSum Y Z .fst
  XYZ : sumTors X (takeSum Y Z)
  XYZ = isContrSum X (takeSum Y Z) .fst

-- We deduce the associativity of the sum

assocSum : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) (Z : TwoTorsor ℓ) →
  takeSum (takeSum X Y) Z ≡ takeSum X (takeSum Y Z)
assocSum X Y Z = Σ≡Prop (λ _ → isPropPropTrunc) (PathPΣ (PathPΣ (isContr→isProp (isContrTriSum X Y Z)
    (isTriSumXYPlusZ X Y Z) (isTriSumXPlusYZ X Y Z)) .fst) .fst)

-- Now we define the equivalence leading to the homogeneity of K(S2,1)

transportTors : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) → TwoTorsor ℓ → TwoTorsor ℓ
transportTors X Y A = takeSum A (takeSum X Y)

isEquivTransportTors : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) → isEquiv (transportTors X Y)
isEquivTransportTors X Y = involIsEquiv (λ A →
  takeSum (takeSum A (takeSum X Y)) (takeSum X Y)
    ≡⟨ assocSum A (takeSum X Y) (takeSum X Y) ⟩
  takeSum A (takeSum (takeSum X Y) (takeSum X Y))
    ≡⟨ cong (λ a → takeSum A a) (invTors (takeSum X Y)) ⟩
  takeSum A pointedTors
    ≡⟨ sumUnit A ⟩
  A ∎
  )

-- K(S2,1) is homogeneous

isHomogeneousTors : ∀ {ℓ} → (X : TwoTorsor ℓ) (Y : TwoTorsor ℓ) →
  PathP (λ _ → Σ[ X ∈ Type (lsuc ℓ) ] X ) (TwoTorsor ℓ , X) (TwoTorsor ℓ , Y)
isHomogeneousTors X Y = ΣPathP ( ua (transportTors X Y , isEquivTransportTors X Y) , toPathP (
  transport (ua (transportTors X Y , isEquivTransportTors X Y)) X
    ≡⟨ uaβ (transportTors X Y , isEquivTransportTors X Y) X ⟩
  takeSum X (takeSum X Y)
    ≡⟨ sym (assocSum X X Y) ⟩
  takeSum (takeSum X X) Y
    ≡⟨ cong (λ a → takeSum a Y) (invTors X) ⟩
  takeSum pointedTors Y
    ≡⟨ symSum pointedTors Y ⟩
  takeSum Y pointedTors
    ≡⟨ sumUnit Y ⟩
  Y ∎))

homoTors : ∀ {ℓ} → (X : TwoTorsor ℓ) →
  PathP (λ _ → Σ[ X ∈ Type (lsuc ℓ) ] X) (TwoTorsor ℓ , pointedTors) (TwoTorsor ℓ , X)
homoTors X = isHomogeneousTors pointedTors pointedTors ⁻¹ ∙ isHomogeneousTors pointedTors X

homoEqRefl : ∀ {ℓ} → homoTors {ℓ} pointedTors ≡ refl
homoEqRefl = lCancel $ isHomogeneousTors pointedTors pointedTors
