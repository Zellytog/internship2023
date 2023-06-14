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

module Sign.TwoTorsors.Base where

{- The type of 2-torsors is K(S2,1), the Eilenberg-MacLane space corresponding to the permutations on two elements.
   We can describe it conveniently as the type of sets with only two elements, and we prove here the basic facts about this type.-}

TwoTorsor : ∀ ℓ → Type (lsuc ℓ)
TwoTorsor ℓ = Σ[ X ∈ Type ℓ ] (∥ X ≡ (Lift Bool) ∥₁)

-- Bool is equivalent to its type of equivalence, which is a very useful property

fctEquivBoolBool : (Bool ≃ Bool) → Bool
fctEquivBoolBool f = fst f false

invEquivBoolBool : Bool → (Bool ≃ Bool)
invEquivBoolBool true = notEquiv
invEquivBoolBool false = idEquiv _

equalOrOpposite : (x : Bool) → (y : Bool) → ((x ≡ y) ⊎ (x ≡ not y))
equalOrOpposite true true = inl refl
equalOrOpposite true false = inr refl
equalOrOpposite false true = inr refl
equalOrOpposite false false = inl refl

commuteEquivNotTrue : ((f , e) : Bool ≃ Bool) → f true ≡ not (f false)
commuteEquivNotTrue (f , e) = sumrec (λ p → zrec (true≢false ((sym ((snd r) true)) ∙ (cong (fst r) p) ∙ ((snd r) false)))) (λ p → p) (equalOrOpposite (f true) (f false))
  where
  r : Σ[ g ∈ (Bool → Bool)] (retract f g)
  r = isEquiv→hasRetract e

commuteEquivNotFalse : ((f , e) : Bool ≃ Bool) → f false ≡ not (f true)
commuteEquivNotFalse (f , e) = sumrec (λ p → zrec (false≢true ((sym ((snd r) false)) ∙ (cong (fst r) p) ∙ ((snd r) true)))) (λ p → p) (equalOrOpposite (f false) (f true))
  where
  r : Σ[ g ∈ (Bool → Bool)] (retract f g)
  r = isEquiv→hasRetract e

isEquivfct : isEquiv fctEquivBoolBool
isEquivfct = record { equiv-proof = λ b → ( (invEquivBoolBool b , lemma b) , λ y → fst ΣPath≃PathΣ (equivEq (funExt (h {b} {y})), isSet→SquareP (λ _ _ → isSetBool) _ _ _ _))} 
    where
    lemma : (b : Bool) → fst (invEquivBoolBool b) false ≡ b
    lemma true = refl
    lemma false = refl
          
    h : {b : Bool} → {y : fiber fctEquivBoolBool b}  → (d : Bool) → ((fst (invEquivBoolBool b)) d) ≡ (fst (fst y) d)
    h {b} {y} true = (sym
      (fst (fst y) true ≡⟨ commuteEquivNotTrue (fst y) ⟩ 
      not (fst (fst y) false) ≡⟨ cong not (snd y) ⟩
      not b ≡⟨ cong not (sym (lemma b)) ⟩
      not (fst (invEquivBoolBool b) false) ≡⟨ sym (commuteEquivNotTrue (invEquivBoolBool b)) ⟩
      fst (invEquivBoolBool b) true ∎ ))
    h {b} {y} false = lemma b ∙ sym (snd y)

-- This allows us to construct an operation on torsors

BoolBoolEquivBool : ∀ {ℓ} → (Lift {_} {ℓ} Bool ≃ Lift {_} {ℓ} Bool) ≃ Lift {_} {ℓ} Bool
BoolBoolEquivBool = (invEquiv (equivComp LiftEquiv LiftEquiv)) ∙ₑ (fctEquivBoolBool , isEquivfct) ∙ₑ LiftEquiv

equivTors : ∀ {ℓ} → ((X , e) : TwoTorsor ℓ) → ((Y , e') : TwoTorsor ℓ) → ∥ (X ≃ Y) ≡ Lift Bool ∥₁
equivTors (X , e) (Y , e') = rec isPropPropTrunc (λ e → rec isPropPropTrunc (λ e' → ∣ ua ((equivComp (pathToEquiv e) (pathToEquiv e')) ∙ₑ BoolBoolEquivBool) ∣₁ ) e') e

operEquivTors : ∀ {ℓ} → TwoTorsor ℓ → TwoTorsor ℓ → TwoTorsor ℓ
operEquivTors (X , e) (Y , e') = ( (X ≃ Y) , equivTors (X , e) (Y , e')) 

-- A few first properties about 2-torsors

pointedTors : ∀ {ℓ} → TwoTorsor ℓ
pointedTors = (Lift Bool , ∣ refl ∣₁)

isSetTors : ∀ {ℓ} → ((X , e) : TwoTorsor ℓ) → isSet X 
isSetTors (X , e) = rec isPropIsSet (λ e → isOfHLevelRespectEquiv 2 (pathToEquiv (sym e)) (isOfHLevelLift 2 isSetBool)) e

isSetEquiv : ∀ {ℓ} → {X : Type ℓ} → {Y : Type ℓ} → (isSet Y) → isSet (X ≃ Y)
isSetEquiv s = isSetΣ (isSetΠ (λ _ → s)) (λ f → isProp→isSet (isPropIsEquiv f))

connexeTors2 : ∀ {ℓ} → ( (X , e) : TwoTorsor ℓ) → ((Y , e') : TwoTorsor ℓ) → ∥ (X , e) ≡ (Y , e') ∥₁
connexeTors2 (X , e) (Y , e') = rec isPropPropTrunc (λ e → rec isPropPropTrunc ( λ e' → ∣ Σ≡Prop (λ X → isPropPropTrunc) ((e ∙ sym e')) ∣₁) e') e

isgroupoidTors : ∀ {ℓ} → isOfHLevel 3 (TwoTorsor ℓ)
isgroupoidTors = λ X Y → isOfHLevelRespectEquiv 2 (Σ≡PropEquiv (λ _ → isPropPropTrunc)) ((isOfHLevelRespectEquiv 2 (invEquiv univalence) (isSetEquiv (isSetTors Y ))))

-- A description of equivalence between two torsors

twoEquivTors : ∀ {ℓ} → {X : Type ℓ} → (p : X ≃ Lift {_} {ℓ} Bool) → (q : X ≃ Lift {_} {ℓ} Bool) → (q ≡ p) ⊎ (q ≡ p ∙ₑ Lift≃Lift notEquiv)
twoEquivTors {ℓ} p q = sumrec (λ r → inl (isoFunInjective (equivToIso (equivComp p (idEquiv _) ∙ₑ BoolBoolEquivBool)) q p (sym (cong lift r))))
  (λ r → inr (isoFunInjective (equivToIso (equivComp p (idEquiv _) ∙ₑ BoolBoolEquivBool)) q (p ∙ₑ Lift≃Lift notEquiv) ((
  fst (invEquiv p ∙ₑ q ∙ₑ idEquiv _) (lift false) ≡⟨ cong lift (sym (notnot (lower (fst (invEquiv p ∙ₑ q ∙ₑ idEquiv _) (lift false))))) ⟩
  fst (Lift≃Lift {ℓ' = ℓ} notEquiv) (fst (Lift≃Lift notEquiv) (fst (invEquiv p ∙ₑ q ∙ₑ idEquiv _) (lift false))) ≡⟨ cong (λ x → fst (Lift≃Lift notEquiv) x) (sym (cong (lift { j = ℓ }) r)) ⟩
  fst (invEquiv p ∙ₑ p ∙ₑ idEquiv _ ∙ₑ (Lift≃Lift notEquiv)) (lift false) ≡⟨ cong (λ x → fst (invEquiv p ∙ₑ p ∙ₑ x) (lift false)) (compEquivIdEquiv (Lift≃Lift notEquiv))⟩
  fst (invEquiv p ∙ₑ p ∙ₑ Lift≃Lift notEquiv) (lift false) ≡⟨ cong (λ x → fst (invEquiv p ∙ₑ p ∙ₑ x) (lift false)) (sym (compEquivEquivId (Lift≃Lift notEquiv))) ⟩
  fst (invEquiv p ∙ₑ (p ∙ₑ Lift≃Lift notEquiv) ∙ₑ idEquiv _) (lift false) ∎
  )))) (equalOrOpposite (fst (equivComp p (idEquiv _) ∙ₑ BoolBoolEquivBool) p .lower) (fst (equivComp p (idEquiv _) ∙ₑ BoolBoolEquivBool) q .lower))

-- We will define the action of Bool on a 2-torsor, for which we first prove that the defined action does not depend on the choice of the path to Bool

uniqAction : ∀ {ℓ} → {X : Type ℓ} → X ≃ Lift {_} {ℓ} Bool → (X ≃ X) ≃ Lift {_} {ℓ} Bool
uniqAction p = equivComp p p ∙ₑ BoolBoolEquivBool

isConstAction : ∀ {ℓ} → {X : Type ℓ} → (p : X ≃ Lift {_} {ℓ} Bool) → (q : X ≃ Lift {_} {ℓ} Bool) → uniqAction p ≡ uniqAction q
isConstAction {ℓ} p q = equivEq (funExt (λ f → sumrec (λ r → (cong (λ x → uniqAction x .fst f) (sym r) ) ) (λ r → sym (
  (fst (invEquiv q ∙ₑ f ∙ₑ q) (lift false)) ≡⟨ cong (λ x → fst (invEquiv x ∙ₑ f ∙ₑ x) (lift false)) r ⟩
  (fst (invEquiv (p ∙ₑ Lift≃Lift {ℓ'' = ℓ} notEquiv) ∙ₑ f ∙ₑ p ∙ₑ Lift≃Lift notEquiv) (lift false)) 
    ≡⟨ cong (λ x → fst (x ∙ₑ f ∙ₑ p ∙ₑ Lift≃Lift notEquiv) (lift false)) (lemma p (Lift≃Lift notEquiv)) ⟩
  (fst ((invEquiv (Lift≃Lift {ℓ'' = ℓ} notEquiv) ∙ₑ invEquiv p) ∙ₑ f ∙ₑ p ∙ₑ Lift≃Lift notEquiv) (lift false)) 
    ≡⟨ cong (λ x → fst x (lift false)) (sym (compEquiv-assoc {A = Lift {_} {ℓ} Bool} (invEquiv (Lift≃Lift notEquiv)) (invEquiv p) (f ∙ₑ p ∙ₑ Lift≃Lift notEquiv))) ⟩
  (fst (Lift≃Lift notEquiv) ( fst (invEquiv p ∙ₑ f ∙ₑ p) (lift true))) ≡⟨ lemma2 (invEquiv p ∙ₑ f ∙ₑ p) ⟩
  fst (invEquiv p ∙ₑ f ∙ₑ p) (lift false) ∎)) (twoEquivTors p q)))
  where
  lemma : ∀ {ℓ} → {X : Type ℓ} → {Y : Type ℓ} → {Z : Type ℓ} → (e : X ≃ Y) → (e' : Y ≃ Z) → invEquiv (e ∙ₑ e') ≡ invEquiv e' ∙ₑ invEquiv e
  lemma e e' = equivEq refl
  lemma2 : ∀ {ℓ} → (e : Lift {_} {ℓ} Bool ≃ Lift {_} {ℓ} Bool) → Lift≃Lift notEquiv .fst (e .fst (lift true)) ≡ e .fst (lift false) 
  lemma2 e = cong lift (sym (commuteEquivNotFalse (LiftEquiv ∙ₑ e ∙ₑ invEquiv LiftEquiv)))


uniqChoiceForConst : ∀ {ℓ} → {X : Type ℓ} → {Y : Type ℓ} → (isSet Y) → (f : X → Y) → ((x : X) → (y : X) → f x ≡ f y) → isProp (Σ[ y ∈ Y ] ∥ Σ[ x ∈ X ] (y ≡ f x) ∥₁ )
uniqChoiceForConst p f q y z = Σ≡Prop (λ _ → isPropPropTrunc) (rec (p (fst y) (fst z)) (λ e → rec (p (fst y) (fst z)) 
  (λ e' → snd e ∙ q (fst e) (fst e') ∙ sym (snd e')) (snd z)) (snd y))

actTors : ∀ {ℓ} → ((X , e) : TwoTorsor ℓ) → Lift {j = ℓ} Bool → X ≃ X
actTors (X , e) = invEquiv (fst (rec (uniqChoiceForConst (isSetEquiv (isOfHLevelLift 2 isSetBool)) uniqAction isConstAction) 
  (λ e → (uniqAction (pathToEquiv e) , ∣ ((pathToEquiv e) , refl) ∣₁)) e)) .fst

isEquivActTors : ∀ {ℓ} → ((X , e) : TwoTorsor ℓ) → isEquiv (actTors (X , e))
isEquivActTors (X , e) = invEquiv (fst (rec (uniqChoiceForConst (isSetEquiv (isOfHLevelLift 2 isSetBool)) uniqAction isConstAction) 
    (λ e → (uniqAction (pathToEquiv e) , ∣ ((pathToEquiv e) , refl) ∣₁)) e)) .snd

-- We make a few results to manipulate the action more easily

rewriteBoolBool : ∀ {ℓ} → (b : Lift {_} {ℓ} Bool) → invEquiv BoolBoolEquivBool .fst b ≡ Lift≃Lift (invEquivBoolBool (lower b))
rewriteBoolBool (lift true) = equivEq (funExt (λ b → if lower b then refl else refl))
rewriteBoolBool (lift false) = equivEq (funExt (λ b → if lower b then refl else refl))

actionForEquiv : ∀ {ℓ} → (X : Type ℓ) → (e : X ≡ Lift {_} {ℓ} Bool) → actTors (X , ∣ e ∣₁) ≡ invEquiv (uniqAction (pathToEquiv e)) .fst
actionForEquiv X e = cong (λ x → invEquiv (fst x) .fst ) (uniqChoiceForConst (isSetEquiv (isOfHLevelLift 2 isSetBool)) uniqAction isConstAction (
  (rec (uniqChoiceForConst (isSetEquiv (isOfHLevelLift 2 isSetBool)) uniqAction isConstAction) 
  (λ e → (uniqAction (pathToEquiv e) , ∣ ((pathToEquiv e) , refl) ∣₁)) ∣ e ∣₁)) (uniqAction (pathToEquiv e), ∣ (pathToEquiv e), refl ∣₁))

lemmaAct : ∀ {ℓ} → (X : Type ℓ) → (e : X ≡ Lift {_} {ℓ} Bool) → (b : Lift {_} {ℓ} Bool) 
  → actTors (X , ∣ e ∣₁) b ≡ pathToEquiv e ∙ₑ Lift≃Lift (invEquivBoolBool (lower b)) ∙ₑ invEquiv (pathToEquiv e)
lemmaAct X e b =
  actTors (X , ∣ e ∣₁) b ≡⟨ cong (λ x → x b) ((actionForEquiv X e)) ⟩
  invEquiv (uniqAction (pathToEquiv e)) .fst b ≡⟨ cong (λ x → x .fst b) (lemma (equivComp (pathToEquiv e) (pathToEquiv e)) BoolBoolEquivBool) ⟩
  (invEquiv BoolBoolEquivBool ∙ₑ invEquiv (equivComp (pathToEquiv e) (pathToEquiv e))) .fst b
    ≡⟨ cong (λ x → invEquiv (equivComp (pathToEquiv e) (pathToEquiv e)) .fst x) (rewriteBoolBool b) ⟩
  equivCompIso (pathToEquiv e) (pathToEquiv e) .Iso.inv (Lift≃Lift (invEquivBoolBool (lower b)))
    ≡⟨ sym (compEquiv-assoc (pathToEquiv e) (Lift≃Lift (invEquivBoolBool (lower b))) (invEquiv (pathToEquiv e))) ⟩
  pathToEquiv e ∙ₑ Lift≃Lift (invEquivBoolBool (lower b)) ∙ₑ invEquiv (pathToEquiv e) ∎
  where
  lemma : ∀ {ℓ} → {X : Type ℓ} → {Y : Type ℓ} → {Z : Type ℓ} → (e : X ≃ Y) → (e' : Y ≃ Z) → invEquiv (e ∙ₑ e') ≡ invEquiv e' ∙ₑ invEquiv e
  lemma e e' = equivEq refl

-- We will prove that the action has the expected properties of an action on a set

isNeutralFalse : ∀ {ℓ} → (X : TwoTorsor ℓ) → actTors X (lift false) ≡ idEquiv (fst X)
isNeutralFalse (X , e₁) = rec (isSetEquiv (isSetTors (X , e₁)) (actTors (X , e₁) (lift false)) (idEquiv X)) (λ e → 
  actTors (X , e₁) (lift false) ≡⟨ cong (λ x → actTors x (lift false)) (Σ≡Prop (λ _ → isPropPropTrunc) {u = (X , e₁)} {v = (X , ∣ e ∣₁)} refl) ⟩
  actTors (X , ∣ e ∣₁) (lift false) ≡⟨ lemmaAct X e (lift false) ⟩
  pathToEquiv e ∙ₑ Lift≃Lift (invEquivBoolBool false) ∙ₑ invEquiv (pathToEquiv e)
    ≡⟨ cong (λ x → pathToEquiv e ∙ₑ x ∙ₑ invEquiv (pathToEquiv e)) (equivEq (funExt (λ b → if lower b then refl else refl))) ⟩
  pathToEquiv e ∙ₑ idEquiv _ ∙ₑ invEquiv (pathToEquiv e) ≡⟨ cong (λ x → pathToEquiv e ∙ₑ x) (compEquivIdEquiv (invEquiv (pathToEquiv e))) ⟩
  pathToEquiv e ∙ₑ invEquiv (pathToEquiv e) ≡⟨ invEquiv-is-rinv (pathToEquiv e) ⟩
  idEquiv _ ∎
  ) e₁

actOnBool : ∀ {ℓ} → (b₀ : Lift {_} {ℓ} Bool) → (b₁ : Lift {_} {ℓ} Bool) → actTors (Lift {_} {ℓ} Bool , ∣ refl ∣₁) b₀ .fst b₁ ≡ lift ((lower b₀) ⊕ (lower b₁))
actOnBool (lift true) (lift true) = refl
actOnBool (lift false) (lift true) = refl
actOnBool (lift true) (lift false) = refl
actOnBool (lift false) (lift false) = refl

isAssocAct : ∀ {ℓ} → ((X , e) : TwoTorsor ℓ) → (b₀ : Lift {_} {ℓ} Bool) → (b₁ : Lift {_} {ℓ} Bool) →
  actTors (X , e) b₀ ∙ₑ actTors (X , e) b₁ ≡ actTors (X , e) (lift ((lower b₀) ⊕ (lower b₁)))
isAssocAct (X , e) (lift false) (lift false) =  (cong (λ x → actTors (X , e) (lift false) ∙ₑ x) (isNeutralFalse (X , e))) ∙ (compEquivEquivId (actTors (X , e) (lift false)))
isAssocAct (X , e) (lift true) (lift false) = (cong (λ x → actTors (X , e) (lift true) ∙ₑ x) (isNeutralFalse (X , e))) ∙ (compEquivEquivId (actTors (X , e) (lift true)))
isAssocAct (X , e) (lift false) (lift true) = (cong (λ x → x ∙ₑ actTors (X , e) (lift true)) (isNeutralFalse (X , e))) ∙ (compEquivIdEquiv (actTors (X , e) (lift true)))
isAssocAct (X , e₁) (lift true) (lift true) = rec (isSetEquiv (isSetTors (X , e₁)) (actTors (X , e₁) (lift true) ∙ₑ actTors (X , e₁) (lift true)) (actTors (X , e₁) (lift false)))
  (λ e → actTors (X , e₁) (lift true) ∙ₑ actTors (X , e₁) (lift true) 
    ≡⟨ cong (λ x → actTors x (lift true) ∙ₑ actTors x (lift true)) (Σ≡Prop (λ _ → isPropPropTrunc) {u = (X , e₁)} {v = (X , ∣ e ∣₁)} refl) ⟩
  actTors (X , ∣ e ∣₁) (lift true) ∙ₑ actTors (X , ∣ e ∣₁) (lift true) ≡⟨ cong (λ x → x ∙ₑ x) (lemmaAct X e (lift true)) ⟩
  (pathToEquiv e ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e)) ∙ₑ (pathToEquiv e ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e))
    ≡⟨ cong (λ x → x ∙ₑ (pathToEquiv e ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e))) (compEquiv-assoc (pathToEquiv e) (Lift≃Lift notEquiv) (invEquiv (pathToEquiv e))) ⟩
  ((pathToEquiv e ∙ₑ Lift≃Lift notEquiv) ∙ₑ invEquiv (pathToEquiv e)) ∙ₑ (pathToEquiv e ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e))
    ≡⟨ sym (compEquiv-assoc (pathToEquiv e ∙ₑ Lift≃Lift notEquiv) (invEquiv (pathToEquiv e)) (pathToEquiv e ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e))) ⟩
  (pathToEquiv e ∙ₑ Lift≃Lift notEquiv) ∙ₑ invEquiv (pathToEquiv e) ∙ₑ (pathToEquiv e ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e))
    ≡⟨ cong (λ x → (pathToEquiv e ∙ₑ Lift≃Lift notEquiv) ∙ₑ x) (compEquiv-assoc (invEquiv (pathToEquiv e)) (pathToEquiv e) (Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e))) ⟩
  (pathToEquiv e ∙ₑ Lift≃Lift notEquiv) ∙ₑ (invEquiv (pathToEquiv e) ∙ₑ pathToEquiv e) ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e)
    ≡⟨ cong (λ x → (pathToEquiv e ∙ₑ Lift≃Lift notEquiv) ∙ₑ x ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e)) (invEquiv-is-linv (pathToEquiv e)) ⟩
  (pathToEquiv e ∙ₑ Lift≃Lift notEquiv) ∙ₑ idEquiv _ ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e)
    ≡⟨ cong (λ x → (pathToEquiv e ∙ₑ Lift≃Lift notEquiv) ∙ₑ x) (compEquivIdEquiv (Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e))) ⟩
  (pathToEquiv e ∙ₑ Lift≃Lift notEquiv) ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv e)
    ≡⟨ compEquiv-assoc (pathToEquiv e ∙ₑ Lift≃Lift notEquiv) (Lift≃Lift notEquiv) (invEquiv (pathToEquiv e)) ⟩
  ((pathToEquiv e ∙ₑ Lift≃Lift notEquiv) ∙ₑ Lift≃Lift notEquiv) ∙ₑ invEquiv (pathToEquiv e)
    ≡⟨ cong (λ x → x ∙ₑ invEquiv (pathToEquiv e)) (sym (compEquiv-assoc (pathToEquiv e) (Lift≃Lift notEquiv) (Lift≃Lift notEquiv))) ⟩
  (pathToEquiv e ∙ₑ Lift≃Lift notEquiv ∙ₑ Lift≃Lift notEquiv) ∙ₑ invEquiv (pathToEquiv e)
    ≡⟨ cong (λ x → (pathToEquiv e ∙ₑ x) ∙ₑ invEquiv (pathToEquiv e)) liftNotNot ⟩
  (pathToEquiv e ∙ₑ idEquiv _) ∙ₑ invEquiv (pathToEquiv e)
    ≡⟨ cong (λ x → x ∙ₑ invEquiv (pathToEquiv e)) (compEquivEquivId (pathToEquiv e)) ⟩
  pathToEquiv e ∙ₑ invEquiv (pathToEquiv e)
    ≡⟨ invEquiv-is-rinv (pathToEquiv e) ⟩
  idEquiv _
    ≡⟨ sym (isNeutralFalse (X , e₁)) ⟩
  actTors (X , e₁) (lift false) ∎
  ) e₁
  where
  liftNotNot : ∀ {ℓ} → (Lift≃Lift {ℓ'' = ℓ}) notEquiv ∙ₑ Lift≃Lift notEquiv ≡ idEquiv (Lift {_} {ℓ} Bool)
  liftNotNot = equivEq (funExt (λ b → cong lift (notnot (lower b))))

-- The action is, moreover, transitive

isEquivAction : ∀ {ℓ} → (Z : TwoTorsor ℓ) → (z : fst Z) → isEquiv (λ b → actTors Z b .fst z)
isEquivAction Z z = rec (isPropIsEquiv (λ b → actTors Z b .fst z)) (λ ε → record { equiv-proof = λ y → sumrec 
    (λ α → ((lift false , isoFunInjective (equivToIso (pathToEquiv ε)) (actTors Z (lift false) .fst z) (y) (
        pathToEquiv ε .fst (actTors Z (lift false) .fst z) ≡⟨ cong (λ x → pathToEquiv ε .fst (x .fst z)) (isNeutralFalse Z) ⟩
        pathToEquiv ε .fst z ≡⟨ sym α ⟩
        pathToEquiv ε .fst y ∎
    )) , λ γ → Σ≡Prop (λ δ → isSetTors Z (actTors Z δ .fst z) y) (sumrec (λ p → cong lift (sym p)) (λ p → zrec ( not≢const (lower (pathToEquiv ε .fst z)) (cong lower (sym (
        pathToEquiv ε .fst z ≡⟨ sym α ⟩
        pathToEquiv ε .fst y ≡⟨ cong (pathToEquiv ε .fst) (sym (snd γ)) ⟩
        pathToEquiv ε .fst (actTors Z (γ .fst) .fst z) ≡⟨ cong (λ x → pathToEquiv ε .fst (actTors Z x .fst z)) (cong lift p) ⟩
        pathToEquiv ε .fst (actTors Z (lift true) .fst z) ≡⟨ cong (λ x → pathToEquiv ε .fst (actTors (fst Z , x) (lift true) .fst z)) (isPropPropTrunc (snd Z) ( ∣ ε ∣₁)) ⟩
        pathToEquiv ε .fst (actTors (fst Z , ∣ ε ∣₁) (lift true) .fst z) ≡⟨ cong (λ x → pathToEquiv ε .fst (x .fst z)) (lemmaAct (fst Z) ε (lift true)) ⟩
        pathToEquiv ε .fst ((pathToEquiv ε ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv ε)) .fst z) 
        ≡⟨ (cong (λ x → x .fst z) (sym (compEquiv-assoc (pathToEquiv ε ∙ₑ Lift≃Lift (notEquiv)) (invEquiv (pathToEquiv ε)) (pathToEquiv ε)))) ∙
            (cong (λ x → ((pathToEquiv ε ∙ₑ Lift≃Lift notEquiv) ∙ₑ x) .fst z) (invEquiv-is-linv (pathToEquiv ε))) ∙
            (cong (λ x → x .fst z) (compEquivEquivId (pathToEquiv ε ∙ₑ Lift≃Lift notEquiv))) ⟩
        Lift≃Lift notEquiv .fst (pathToEquiv ε .fst z) ∎
    )))
        )) 
        (dichotomyBoolSym (lower (fst γ)))))) 
    (λ β → (((lift true , isoFunInjective (equivToIso (pathToEquiv ε)) (actTors Z (lift true) .fst z) (y) (
        pathToEquiv ε .fst (actTors Z (lift true) .fst z) ≡⟨ cong (λ x → pathToEquiv ε .fst (actTors (fst Z , x) (lift true) .fst z)) (isPropPropTrunc (snd Z) ( ∣ ε ∣₁)) ⟩
        pathToEquiv ε .fst (actTors (fst Z , ∣ ε ∣₁) (lift true) .fst z) ≡⟨ cong (λ x → pathToEquiv ε .fst (x .fst z)) (lemmaAct (fst Z) ε (lift true)) ⟩
        pathToEquiv ε .fst ((pathToEquiv ε ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv ε)) .fst z) ≡⟨ refl ⟩
        ((pathToEquiv ε ∙ₑ Lift≃Lift notEquiv ∙ₑ invEquiv (pathToEquiv ε)) ∙ₑ pathToEquiv ε) .fst z 
            ≡⟨ cong (λ x → x .fst z) (sym (compEquiv-assoc (pathToEquiv ε ∙ₑ Lift≃Lift (notEquiv)) (invEquiv (pathToEquiv ε)) (pathToEquiv ε))) ⟩
        ((pathToEquiv ε ∙ₑ Lift≃Lift notEquiv) ∙ₑ (invEquiv (pathToEquiv ε) ∙ₑ pathToEquiv ε)) .fst z
            ≡⟨ cong (λ x → ((pathToEquiv ε ∙ₑ Lift≃Lift notEquiv) ∙ₑ x) .fst z) (invEquiv-is-linv (pathToEquiv ε)) ⟩
        ((pathToEquiv ε ∙ₑ Lift≃Lift notEquiv) ∙ₑ idEquiv _) .fst z
            ≡⟨ cong (λ x → x .fst z) (compEquivEquivId (pathToEquiv ε ∙ₑ Lift≃Lift notEquiv)) ⟩
        (Lift≃Lift notEquiv) .fst (pathToEquiv ε .fst z)
            ≡⟨ sym β ⟩
        pathToEquiv ε .fst y ∎
    ))) , λ γ → Σ≡Prop (λ δ → isSetTors Z (actTors Z δ .fst z) y) (sumrec (λ p → cong lift (sym p)) (λ p → zrec ( not≢const (lower (pathToEquiv ε .fst z)) (cong lower (
        Lift≃Lift notEquiv .fst (pathToEquiv ε .fst z) ≡⟨ sym β ⟩
        pathToEquiv ε .fst y ≡⟨ cong (pathToEquiv ε .fst) (sym (snd γ)) ⟩
        pathToEquiv ε .fst (actTors Z (γ .fst) .fst z) ≡⟨ cong (λ x → pathToEquiv ε .fst (actTors Z x .fst z)) (cong lift p) ⟩
        pathToEquiv ε .fst (actTors Z (lift false) .fst z) ≡⟨ cong (λ x → pathToEquiv ε .fst (x .fst z)) (isNeutralFalse Z) ⟩
        pathToEquiv ε .fst z ∎
    ))
        )) 
        (dichotomyBool (lower (fst γ)))))) 
    (liftUnicityBoolNot (pathToEquiv ε .fst y) (pathToEquiv ε .fst z))}) (snd Z)
    where
    liftUnicityBoolNot : ∀ {ℓ} → (x : Lift {_} {ℓ} Bool) (y : Lift {_} {ℓ} Bool) → (x ≡ y) ⊎ (x ≡ Lift≃Lift notEquiv .fst y)
    liftUnicityBoolNot (lift true) (lift true) = inl refl
    liftUnicityBoolNot (lift true) (lift false) = inr refl
    liftUnicityBoolNot (lift false) (lift true) = inr refl
    liftUnicityBoolNot (lift false) (lift false) = inl refl

-- This leads to a result analogous to dichotomyBool but for a 2-torsor which is a proposition

dichotomyTors : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → (x ≡ y) ⊎ (x ≡ actTors X (lift true) .fst y)
dichotomyTors X x y = sumrec (λ b → (inr (
    x ≡⟨ sym (isEquivAction X y .equiv-proof x .fst .snd) ⟩
    actTors X _ .fst y ≡⟨ cong (λ a → actTors X a .fst y) (cong lift b) ⟩
    actTors X (lift true) .fst y ∎))) (λ b → (inl (
    x ≡⟨ sym (isEquivAction X y .equiv-proof x .fst .snd) ⟩
    actTors X _ .fst y ≡⟨ cong (λ a → actTors X a .fst y) (cong lift b) ⟩
    actTors X (lift false) .fst y ≡⟨ cong (λ a → a .fst y) (isNeutralFalse X) ⟩
    y ∎))) (dichotomyBool (lower (isEquivAction X y .equiv-proof x .fst .fst)))

isPropDichotomyTors : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) → isProp ((x ≡ y) ⊎ (x ≡ actTors X (lift true) .fst y))
isPropDichotomyTors X x y (inl p) (inl q) = cong inl (isSetTors X x y p q)
isPropDichotomyTors X x y (inl p) (inr q) = zrec (false≢true (cong lower (isoFunInjective (equivToIso ((λ b → actTors X b .fst y) , isEquivAction X y))
  (lift false) (lift true) (cong (λ a → a .fst y) (isNeutralFalse X) ∙ sym p ∙ q))))
isPropDichotomyTors X x y (inr p) (inl q) = zrec (false≢true (cong lower (isoFunInjective (equivToIso ((λ b → actTors X b .fst y) , isEquivAction X y))
  (lift false) (lift true) (cong (λ a → a .fst y) (isNeutralFalse X) ∙ sym q ∙ p))))
isPropDichotomyTors X x y (inr p) (inr q) = cong inr (isSetTors X x (actTors X (lift true) .fst y) p q)

-- We define the "not" for a torsor, which we call flip

flipTors : ∀ {ℓ} → (X : TwoTorsor ℓ) → (fst X) → fst X
flipTors X x = actTors X (lift true) .fst x

isNilFlip : ∀ {ℓ} → (X : TwoTorsor ℓ) → (x : fst X) → (flipTors X ∘ flipTors X) x ≡ x
isNilFlip X x = (flipTors X ∘ flipTors X) x ≡⟨ cong (λ a → a .fst x) (isAssocAct X (lift true) (lift true)) ⟩
    actTors X (lift (true ⊕ true)) .fst x ≡⟨ cong (λ a → a .fst x) (isNeutralFalse X) ⟩
    x ∎
