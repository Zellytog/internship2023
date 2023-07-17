open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to sumrec)
open import Cubical.Foundations.Everything
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)

module Sign.TwoTorsors.Base where

infixr 25 _≃ₜ_

private
  variable
    ℓ : Level

-- The type of 2-torsors is K(S2,1), the Eilenberg-MacLane space of ℤ/2ℤ
-- We can describe it conveniently as the type of sets with only two elements,
-- and we prove here basic facts about this type

TwoTorsor : ∀ ℓ → Type (lsuc ℓ)
TwoTorsor ℓ = Σ[ X ∈ Type ℓ ] (∥ X ≃ Bool ∥₁)

-- Bool is equivalent to its type of equivalence, which is a very useful property

𝟚≃𝟚→𝟚 : (Bool ≃ Bool) → Bool
𝟚≃𝟚→𝟚 f = fst f false

𝟚→𝟚≃𝟚 : Bool → (Bool ≃ Bool)
𝟚→𝟚≃𝟚 true = notEquiv
𝟚→𝟚≃𝟚 false = idEquiv _

≡⊎not : (x : Bool) → (y : Bool) → ((x ≡ y) ⊎ (x ≡ not y))
≡⊎not true true = inl refl
≡⊎not true false = inr refl
≡⊎not false true = inr refl
≡⊎not false false = inl refl

com≃not⊤ : ((f , e) : Bool ≃ Bool) → f true ≡ not (f false)
com≃not⊤ (f , e) = sumrec (λ p → zrec (true≢false ((sym ((snd r) true))
  ∙ (cong (fst r) p) ∙ ((snd r) false)))) (λ p → p) (≡⊎not (f true) (f false))
  where
  r : Σ[ g ∈ (Bool → Bool)] (retract f g)
  r = isEquiv→hasRetract e

com≃not⊥ : ((f , e) : Bool ≃ Bool) → f false ≡ not (f true)
com≃not⊥ (f , e) = sumrec (λ p → zrec (false≢true ((sym ((snd r) false))
  ∙ (cong (fst r) p) ∙ ((snd r) true)))) (λ p → p) (≡⊎not (f false) (f true))
  where
  r : Σ[ g ∈ (Bool → Bool)] (retract f g)
  r = isEquiv→hasRetract e

isEquivfct : isEquiv 𝟚≃𝟚→𝟚
isEquivfct = record { equiv-proof = λ b → ( (𝟚→𝟚≃𝟚 b , lemma b) ,
  λ y → fst ΣPath≃PathΣ (equivEq (funExt (h {b} {y})), isSet→SquareP (λ _ _ → isSetBool) _ _ _ _))} 
    where
    lemma : (b : Bool) → fst (𝟚→𝟚≃𝟚 b) false ≡ b
    lemma true = refl
    lemma false = refl
    h : {b : Bool} → {y : fiber 𝟚≃𝟚→𝟚 b}  → (d : Bool) →
      (fst (𝟚→𝟚≃𝟚 b)) d ≡ fst (fst y) d
    h {b} {y} true = (sym
      (fst (fst y) true ≡⟨ com≃not⊤ (fst y) ⟩ 
      not (fst (fst y) false) ≡⟨ cong not (snd y) ⟩
      not b ≡⟨ cong not (sym (lemma b)) ⟩
      not (fst (𝟚→𝟚≃𝟚 b) false) ≡⟨ sym (com≃not⊤ (𝟚→𝟚≃𝟚 b)) ⟩
      fst (𝟚→𝟚≃𝟚 b) true ∎ ))
    h {b} {y} false = lemma b ∙ sym (snd y)

𝟚≃𝟚≃𝟚 : (Bool ≃ Bool) ≃ Bool
𝟚≃𝟚≃𝟚 = (𝟚≃𝟚→𝟚 , isEquivfct)

-- This allows us to construct an operation on torsors
{-
BoolBoolEquivBool : ∀ {ℓ} → (Lift {_} {ℓ} Bool ≃ Lift {_} {ℓ} Bool) ≃ Lift {_} {ℓ} Bool
BoolBoolEquivBool = (invEquiv (equivComp LiftEquiv LiftEquiv)) ∙ₑ (fctEquivBoolBool , isEquivfct)
  ∙ₑ LiftEquiv
-}
equivTors : ∀ {ℓ} → ((X , e) : TwoTorsor ℓ) → ((Y , e') : TwoTorsor ℓ) → ∥ (X ≃ Y) ≃ Bool ∥₁
equivTors (X , e) (Y , e') = proprec isPropPropTrunc (λ e → proprec isPropPropTrunc (λ e' →
  ∣ (equivComp e e') ∙ₑ 𝟚≃𝟚≃𝟚 ∣₁ ) e') e

_≃ₜ_ : ∀ {ℓ} → TwoTorsor ℓ → TwoTorsor ℓ → TwoTorsor ℓ
(X , e) ≃ₜ (Y , e') = ( (X ≃ Y) , equivTors (X , e) (Y , e')) 

-- A few first properties about 2-torsors

∙ₜ : ∀ {ℓ} → TwoTorsor ℓ
∙ₜ = (Lift Bool , ∣ invEquiv LiftEquiv ∣₁)

isSetTors : ((X , e) : TwoTorsor ℓ) → isSet X 
isSetTors (X , e) = proprec isPropIsSet (λ e → isOfHLevelRespectEquiv 2 (invEquiv e) isSetBool) e

isSetEquiv : ∀ {ℓ ℓ'} → {X : Type ℓ} → {Y : Type ℓ'} → (isSet Y) → isSet (X ≃ Y)
isSetEquiv s = isSetΣ (isSetΠ (λ _ → s)) (λ f → isProp→isSet (isPropIsEquiv f))

connexeTors2 : ((X , e) : TwoTorsor ℓ) → ((Y , e') : TwoTorsor ℓ) → ∥ (X , e) ≡ (Y , e') ∥₁
connexeTors2 (X , e) (Y , e') = proprec isPropPropTrunc (λ e → proprec isPropPropTrunc ( λ e' →
  ∣ Σ≡Prop (λ X → isPropPropTrunc) (ua (e ∙ₑ invEquiv e')) ∣₁) e') e

isgroupoidTors : isOfHLevel 3 (TwoTorsor ℓ)
isgroupoidTors = λ X Y → isOfHLevelRespectEquiv 2 (Σ≡PropEquiv (λ _ → isPropPropTrunc))
  (isOfHLevelRespectEquiv 2 (invEquiv univalence) (isSetEquiv (isSetTors Y )))

-- A description of equivalence between two torsors

twoEquivTors : {X : Type ℓ} → (p : X ≃ Bool) → (q : X ≃ Bool) →
  (q ≡ p) ⊎ (q ≡ p ∙ₑ notEquiv)
twoEquivTors {ℓ} p q = sumrec (λ r → inl (isoFunInjective (equivToIso (equivComp p (idEquiv _)
  ∙ₑ 𝟚≃𝟚≃𝟚)) q p (sym r)))
  (λ r → inr (isoFunInjective (equivToIso (equivComp p (idEquiv _) ∙ₑ 𝟚≃𝟚≃𝟚)) q
    (p ∙ₑ notEquiv)
    (sym (notnot (fst (invEquiv p ∙ₑ q ∙ₑ idEquiv _) false))
    ∙ cong (λ x → fst notEquiv x) (sym r)
    ∙ cong (λ x → fst (invEquiv p ∙ₑ p ∙ₑ x) false) (compEquivIdEquiv notEquiv)
    ∙ cong (λ x → fst (invEquiv p ∙ₑ p ∙ₑ x) false) (sym (compEquivEquivId notEquiv)))))
  (≡⊎not (fst (equivComp p (idEquiv _) ∙ₑ 𝟚≃𝟚≃𝟚) p)
         (fst (equivComp p (idEquiv _) ∙ₑ 𝟚≃𝟚≃𝟚) q))

-- We will define the action of Bool on a 2-torsor, for which we first prove
-- that the defined action does not depend on the choice of the path to Bool

uniqAction : {X : Type ℓ} → X ≃ Bool → (X ≃ X) ≃ Bool
uniqAction p = equivComp p p ∙ₑ 𝟚≃𝟚≃𝟚

isConstAction : {X : Type ℓ} → (p : X ≃ Bool) → (q : X ≃ Bool) → uniqAction p ≡ uniqAction q
isConstAction {ℓ} p q = equivEq (funExt (λ f → sumrec
  (λ r → (cong (λ x → uniqAction x .fst f) (sym r) ) )
  (λ r → sym (
    (fst (invEquiv q ∙ₑ f ∙ₑ q) false)
      ≡⟨ cong (λ x → fst (invEquiv x ∙ₑ f ∙ₑ x) false) r ⟩
    (fst (invEquiv (p ∙ₑ notEquiv) ∙ₑ f ∙ₑ p ∙ₑ notEquiv) false) 
      ≡⟨ cong (λ x → fst (x ∙ₑ f ∙ₑ p ∙ₑ notEquiv) false) (lemma p notEquiv) ⟩
    (fst ((invEquiv notEquiv ∙ₑ invEquiv p) ∙ₑ f ∙ₑ p ∙ₑ notEquiv) false)
      ≡⟨ cong (λ x → fst x false) (sym (compEquiv-assoc
        (invEquiv notEquiv) (invEquiv p) (f ∙ₑ p ∙ₑ notEquiv))) ⟩
    (fst notEquiv ( fst (invEquiv p ∙ₑ f ∙ₑ p) true))
      ≡⟨ lemma2 (invEquiv p ∙ₑ f ∙ₑ p) ⟩
  fst (invEquiv p ∙ₑ f ∙ₑ p) false ∎))
  (twoEquivTors p q)))
  where
  lemma : ∀ {ℓ ℓ' ℓ''} → {X : Type ℓ} → {Y : Type ℓ'} → {Z : Type ℓ''} → (e : X ≃ Y) → (e' : Y ≃ Z) →
    invEquiv (e ∙ₑ e') ≡ invEquiv e' ∙ₑ invEquiv e
  lemma e e' = equivEq refl
  lemma2 : (e : Bool ≃ Bool) → notEquiv .fst (e .fst true) ≡ e .fst false
  lemma2 e = sym (com≃not⊥ e)

uniqChoiceForConst : ∀ {ℓ ℓ'} → {X : Type ℓ} → {Y : Type ℓ'} → (isSet Y) → (f : X → Y) →
  ((x : X) → (y : X) → f x ≡ f y) → isProp (Σ[ y ∈ Y ] ∥ Σ[ x ∈ X ] (y ≡ f x) ∥₁ )
uniqChoiceForConst p f q y z = Σ≡Prop (λ _ → isPropPropTrunc) (proprec (p (fst y) (fst z))
  (λ e → proprec (p (fst y) (fst z)) (λ e' → snd e ∙ q (fst e) (fst e') ∙ sym (snd e')) (snd z))
  (snd y))

+ₜ≃ : ((X , e) : TwoTorsor ℓ) → (X ≃ X) ≃ Bool
+ₜ≃ (X , e) = proprec (uniqChoiceForConst (isSetEquiv isSetBool) uniqAction isConstAction)
  (λ r → (uniqAction r , ∣ (r , refl) ∣₁)) e .fst

+ₜ : ((X , e) : TwoTorsor ℓ) → Bool → X ≃ X
+ₜ X = invEquiv (+ₜ≃ X) .fst

+ₜₐ : (X : TwoTorsor ℓ) → Bool → ⟨ X ⟩ → ⟨ X ⟩
+ₜₐ X x = +ₜ X x .fst

-- We make a few results to manipulate the action more easily

actionForEquiv : (X : Type ℓ) → (e : X ≃ Bool) → +ₜ (X , ∣ e ∣₁) ≡ invEquiv (uniqAction e) .fst
actionForEquiv X e = cong (λ x → invEquiv (fst x) .fst )
  (uniqChoiceForConst (isSetEquiv isSetBool) uniqAction isConstAction (
  (proprec (uniqChoiceForConst (isSetEquiv isSetBool) uniqAction isConstAction) 
  (λ e → (uniqAction e , ∣ (e , refl) ∣₁)) ∣ e ∣₁)) (uniqAction e , ∣ e , refl ∣₁))

lemmaAct : (X : Type ℓ) → (e : X ≃ Bool) → (b : Bool) →
  +ₜ (X , ∣ e ∣₁) b ≡ e ∙ₑ 𝟚→𝟚≃𝟚 b ∙ₑ invEquiv e
lemmaAct X e b =
  +ₜ (X , ∣ e ∣₁) b ≡⟨ cong (λ x → x b) (actionForEquiv X e) ⟩
  invEquiv (uniqAction e) .fst b
    ≡⟨ cong (λ x → x .fst b) (lemma (equivComp e e) 𝟚≃𝟚≃𝟚) ⟩
  (invEquiv 𝟚≃𝟚≃𝟚 ∙ₑ invEquiv (equivComp e e)) .fst b
    ≡⟨ refl ⟩
  equivCompIso e e .Iso.inv (𝟚→𝟚≃𝟚 b)
    ≡⟨ sym (compEquiv-assoc e (𝟚→𝟚≃𝟚 b) (invEquiv e)) ⟩
  e ∙ₑ 𝟚→𝟚≃𝟚 b ∙ₑ invEquiv e ∎
  where
  lemma : ∀ {ℓ ℓ' ℓ''} → {X : Type ℓ} → {Y : Type ℓ'} → {Z : Type ℓ''} → (e : X ≃ Y) → (e' : Y ≃ Z) →
    invEquiv (e ∙ₑ e') ≡ invEquiv e' ∙ₑ invEquiv e
  lemma e e' = equivEq refl

-- We will prove that the action has the expected properties of an action on a set

+ₜ0 : (X : TwoTorsor ℓ) → +ₜ X false ≡ idEquiv (fst X)
+ₜ0 (X , e₁) = proprec (isSetEquiv (isSetTors (X , e₁)) (+ₜ (X , e₁) false) (idEquiv X))
  (λ e → cong (λ x → +ₜ x false)
    (Σ≡Prop (λ _ → isPropPropTrunc) {u = (X , e₁)} {v = (X , ∣ e ∣₁)} refl)
    ∙ lemmaAct X e false ∙ cong (λ x → e ∙ₑ x) (compEquivIdEquiv (invEquiv e))
    ∙ invEquiv-is-rinv e) e₁

+∙ₜ : (b₀ : Bool) → (b₁ : Bool) → +ₜₐ (∙ₜ {ℓ = ℓ}) b₀ (lift b₁) ≡ lift (b₀ ⊕ b₁)
+∙ₜ true true = refl
+∙ₜ false true = refl
+∙ₜ true false = refl
+∙ₜ false false = refl

assoc+ₜ : ((X , e) : TwoTorsor ℓ) → (b₀ : Bool) → (b₁ : Bool) →
  +ₜ (X , e) b₀ ∙ₑ +ₜ (X , e) b₁ ≡ +ₜ (X , e) (b₀ ⊕ b₁)
assoc+ₜ (X , e) false false =  (cong (λ x → +ₜ (X , e) false ∙ₑ x)
  (+ₜ0 (X , e))) ∙ (compEquivEquivId (+ₜ (X , e) false))
assoc+ₜ (X , e) true false = (cong (λ x → +ₜ (X , e) true ∙ₑ x)
  (+ₜ0 (X , e))) ∙ (compEquivEquivId (+ₜ (X , e) true))
assoc+ₜ (X , e) false true = (cong (λ x → x ∙ₑ +ₜ (X , e) true)
  (+ₜ0 (X , e))) ∙ (compEquivIdEquiv (+ₜ (X , e) true))
assoc+ₜ (X , e₁) true true = proprec (isSetEquiv (isSetTors (X , e₁))
  (+ₜ (X , e₁) true ∙ₑ +ₜ (X , e₁) true) (+ₜ (X , e₁) false))
  (λ e → +ₜ (X , e₁) true ∙ₑ +ₜ (X , e₁) true 
    ≡⟨ cong (λ x → +ₜ x true ∙ₑ +ₜ x true) (Σ≡Prop (λ _ → isPropPropTrunc)
      {u = (X , e₁)} {v = (X , ∣ e ∣₁)} refl) ⟩
  +ₜ (X , ∣ e ∣₁) true ∙ₑ +ₜ (X , ∣ e ∣₁) true
    ≡⟨ cong (λ x → x ∙ₑ x) (lemmaAct X e true) ⟩
  (e ∙ₑ notEquiv ∙ₑ invEquiv e) ∙ₑ (e ∙ₑ notEquiv ∙ₑ invEquiv e)
    ≡⟨ cong (λ x → x ∙ₑ (e ∙ₑ notEquiv ∙ₑ invEquiv e)) (compEquiv-assoc e notEquiv (invEquiv e)) ⟩
  ((e ∙ₑ notEquiv) ∙ₑ invEquiv e) ∙ₑ (e ∙ₑ notEquiv ∙ₑ invEquiv e)
    ≡⟨ sym (compEquiv-assoc (e ∙ₑ notEquiv) (invEquiv e) (e ∙ₑ notEquiv ∙ₑ invEquiv e)) ⟩
  (e ∙ₑ notEquiv) ∙ₑ invEquiv e ∙ₑ (e ∙ₑ notEquiv ∙ₑ invEquiv e)
    ≡⟨ cong (λ x → (e ∙ₑ notEquiv) ∙ₑ x) (compEquiv-assoc (invEquiv e) e (notEquiv ∙ₑ invEquiv e)) ⟩
  (e ∙ₑ notEquiv) ∙ₑ (invEquiv e ∙ₑ e) ∙ₑ notEquiv ∙ₑ invEquiv e
    ≡⟨ cong (λ x → (e ∙ₑ notEquiv) ∙ₑ x ∙ₑ notEquiv ∙ₑ invEquiv e) (invEquiv-is-linv e) ⟩
  (e ∙ₑ notEquiv) ∙ₑ idEquiv _ ∙ₑ notEquiv ∙ₑ invEquiv e
    ≡⟨ cong (λ x → (e ∙ₑ notEquiv) ∙ₑ x) (compEquivIdEquiv (notEquiv ∙ₑ invEquiv e)) ⟩
  (e ∙ₑ notEquiv) ∙ₑ notEquiv ∙ₑ invEquiv e
    ≡⟨ compEquiv-assoc (e ∙ₑ notEquiv) notEquiv (invEquiv e) ⟩
  ((e ∙ₑ notEquiv) ∙ₑ notEquiv) ∙ₑ invEquiv e
    ≡⟨ cong (λ x → x ∙ₑ invEquiv e) (sym (compEquiv-assoc e notEquiv notEquiv)) ⟩
  (e ∙ₑ notEquiv ∙ₑ notEquiv) ∙ₑ invEquiv e
    ≡⟨ cong (λ x → (e ∙ₑ x) ∙ₑ invEquiv e) (equivEq (funExt notnot)) ⟩
  (e ∙ₑ idEquiv _) ∙ₑ invEquiv e
    ≡⟨ cong (λ x → x ∙ₑ invEquiv e) (compEquivEquivId e) ⟩
  e ∙ₑ invEquiv e
    ≡⟨ invEquiv-is-rinv e ⟩
  idEquiv _
    ≡⟨ sym (+ₜ0 (X , e₁)) ⟩
  +ₜ (X , e₁) false ∎) e₁

-- The action is, moreover, transitive

isTrans+ₜ : (Z : TwoTorsor ℓ) → (z : fst Z) → isEquiv (λ b → +ₜ Z b .fst z)
isTrans+ₜ Z z = proprec (isPropIsEquiv (λ b → +ₜ Z b .fst z))
  (λ ε → record { equiv-proof = λ y → sumrec 
    (λ α → (false , isoFunInjective (equivToIso ε)
      (+ₜ Z false .fst z) y (ε .fst (+ₜ Z false .fst z)
        ≡⟨ cong (λ x → ε .fst (x .fst z)) (+ₜ0 Z) ⟩
      ε .fst z ≡⟨ sym α ⟩
      ε .fst y ∎
    )) , λ γ → Σ≡Prop (λ δ → isSetTors Z (+ₜ Z δ .fst z) y) (sumrec sym
    (λ p → zrec ( not≢const (ε .fst z) (sym (ε .fst z ≡⟨ sym α ⟩
      ε .fst y ≡⟨ cong (ε .fst) (sym (snd γ)) ⟩
      ε .fst (+ₜ Z (γ .fst) .fst z)
        ≡⟨ cong (λ x → ε .fst (+ₜ Z x .fst z)) p ⟩
      ε .fst (+ₜ Z true .fst z)
        ≡⟨ cong (λ x → ε .fst (+ₜ (fst Z , x) true .fst z)) (isPropPropTrunc (snd Z) ( ∣ ε ∣₁)) ⟩
      ε .fst (+ₜ (fst Z , ∣ ε ∣₁) true .fst z)
        ≡⟨ cong (λ x → ε .fst (x .fst z)) (lemmaAct (fst Z) ε true) ⟩
      ε .fst ((ε ∙ₑ notEquiv ∙ₑ invEquiv ε) .fst z) 
        ≡⟨ (cong (λ x → x .fst z) (sym (compEquiv-assoc (ε ∙ₑ notEquiv) (invEquiv ε) ε))) ∙
           (cong (λ x → ((ε ∙ₑ notEquiv) ∙ₑ x) .fst z) (invEquiv-is-linv ε)) ∙
           (cong (λ x → x .fst z) (compEquivEquivId (ε ∙ₑ notEquiv))) ⟩
      notEquiv .fst (ε .fst z) ∎)) ))
      (dichotomyBoolSym $ fst γ)))
    (λ β → (((true , isoFunInjective (equivToIso ε)
      (+ₜ Z true .fst z) y (ε .fst (+ₜ Z true .fst z)
        ≡⟨ cong (λ x → ε .fst (+ₜ (fst Z , x) true .fst z)) (isPropPropTrunc (snd Z) ( ∣ ε ∣₁)) ⟩
      ε .fst (+ₜ (fst Z , ∣ ε ∣₁) true .fst z)
        ≡⟨ cong (λ x → ε .fst (x .fst z)) (lemmaAct (fst Z) ε true) ⟩
      ε .fst ((ε ∙ₑ notEquiv ∙ₑ invEquiv ε) .fst z)
        ≡⟨ refl ⟩
      ((ε ∙ₑ notEquiv ∙ₑ invEquiv ε) ∙ₑ ε) .fst z 
        ≡⟨ cong (λ x → x .fst z) (sym (compEquiv-assoc (ε ∙ₑ notEquiv) (invEquiv ε) ε)) ⟩
      ((ε ∙ₑ notEquiv) ∙ₑ (invEquiv ε ∙ₑ ε)) .fst z
        ≡⟨ cong (λ x → ((ε ∙ₑ notEquiv) ∙ₑ x) .fst z) (invEquiv-is-linv ε) ⟩
      ((ε ∙ₑ notEquiv) ∙ₑ idEquiv _) .fst z
        ≡⟨ cong (λ x → x .fst z) (compEquivEquivId (ε ∙ₑ notEquiv)) ⟩
      notEquiv .fst (ε .fst z)
        ≡⟨ sym β ⟩
      ε .fst y ∎
    ))) , λ γ → Σ≡Prop (λ δ → isSetTors Z (+ₜ Z δ .fst z) y) (sumrec sym
      (λ p → zrec (not≢const (ε .fst z) (notEquiv .fst (ε .fst z) ≡⟨ sym β ⟩
        ε .fst y ≡⟨ cong (ε .fst) (sym (snd γ)) ⟩
        ε .fst (+ₜ Z (γ .fst) .fst z)
          ≡⟨ cong (λ x → ε .fst (+ₜ Z x .fst z)) p ⟩
        ε .fst (+ₜ Z false .fst z)
          ≡⟨ cong (λ x → ε .fst (x .fst z)) (+ₜ0 Z) ⟩
        ε .fst z ∎) ))
        (dichotomyBool $ fst γ)))) 
    (UnicityBoolNot (ε .fst y) (ε .fst z))}) (snd Z)
    where
    UnicityBoolNot : (x : Bool) (y : Bool) → (x ≡ y) ⊎ (x ≡ notEquiv .fst y)
    UnicityBoolNot true true = inl refl
    UnicityBoolNot true false = inr refl
    UnicityBoolNot false true = inr refl
    UnicityBoolNot false false = inl refl

-- This leads to a result analogous to dichotomyBool but for a 2-torsor which is a proposition

dichotomyTors : (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) →
  (x ≡ y) ⊎ (x ≡ +ₜ X true .fst y)
dichotomyTors X x y = sumrec
  (λ b → (inr (
  x ≡⟨ sym (isTrans+ₜ X y .equiv-proof x .fst .snd) ⟩
  +ₜ X _ .fst y ≡⟨ cong (λ a → +ₜ X a .fst y) b ⟩
  +ₜ X true .fst y ∎)))
  (λ b → (inl (
  x ≡⟨ sym (isTrans+ₜ X y .equiv-proof x .fst .snd) ⟩
  +ₜ X _ .fst y ≡⟨ cong (λ a → +ₜ X a .fst y) b ⟩
  +ₜ X false .fst y ≡⟨ cong (λ a → a .fst y) (+ₜ0 X) ⟩
  y ∎))) (dichotomyBool (isTrans+ₜ X y .equiv-proof x .fst .fst))

isPropDichotomyTors : (X : TwoTorsor ℓ) → (x : fst X) → (y : fst X) →
  isProp ((x ≡ y) ⊎ (x ≡ +ₜ X true .fst y))
isPropDichotomyTors X x y (inl p) (inl q) = cong inl (isSetTors X x y p q)
isPropDichotomyTors X x y (inl p) (inr q) = zrec (false≢true (isoFunInjective (equivToIso
  ((λ b → +ₜ X b .fst y) , isTrans+ₜ X y)) false true (cong (λ a → a .fst y) (+ₜ0 X) ∙ sym p ∙ q)))
isPropDichotomyTors X x y (inr p) (inl q) = zrec (false≢true (isoFunInjective (equivToIso
  ((λ b → +ₜ X b .fst y) , isTrans+ₜ X y)) false true (cong (λ a → a .fst y) (+ₜ0 X) ∙ sym q ∙ p)))
isPropDichotomyTors X x y (inr p) (inr q) = cong inr
  (isSetTors X x (+ₜ X true .fst y) p q)

-- We define the "not" for a torsor, which we call flip

flipTors : (X : TwoTorsor ℓ) → (fst X) → fst X
flipTors X x = +ₜ X true .fst x

flipTors≃ : (X : TwoTorsor ℓ) → isEquiv (flipTors X)
flipTors≃ X = +ₜ X true .snd

isNilFlip : (X : TwoTorsor ℓ) → (x : fst X) → (flipTors X ∘ flipTors X) x ≡ x
isNilFlip X x = (flipTors X ∘ flipTors X) x ≡⟨ cong (λ a → a .fst x) (assoc+ₜ X true true) ⟩
  +ₜ X (true ⊕ true) .fst x ≡⟨ cong (λ a → a .fst x) (+ₜ0 X) ⟩ x ∎

¬Flip : (X : TwoTorsor ℓ) → ∀ x → (x ≡ flipTors X x) → ⊥
¬Flip X x e = false≢true (isEmbedding→Inj (isEquiv→isEmbedding (isTrans+ₜ X x)) false true
  (cong ((_$ x) ∘ fst) (+ₜ0 X) ∙ e))

≃comFlip : (X Y : TwoTorsor ℓ) → (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) → ∀ x →
  (e .fst ∘ flipTors X) x ≡ (flipTors Y ∘ e .fst) x
≃comFlip X Y e x = sumrec (λ p →
  zrec (¬Flip X x (sym (isEmbedding→Inj (isEquiv→isEmbedding (e .snd)) (flipTors X x) x p))))
  (idfun _)
  (dichotomyTors Y (e .fst (flipTors X x)) (e .fst x))

flipOn≃ : (X Y : TwoTorsor ℓ) → (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) →
  (flipTors X , flipTors≃ X) ∙ₑ e ≡ flipTors (X ≃ₜ Y) e
flipOn≃ X Y e = sumrec
  (λ p → zrec (proprec isProp⊥ (λ e' →
    ¬Flip Y (fst e (invEquiv e' .fst true))
      (sym (cong ((_$ (invEquiv e' .fst true)) ∘ fst) p) ∙ ≃comFlip X Y e (invEquiv e' .fst true)))
    (X .snd)))(idfun _)
  (dichotomyTors (X ≃ₜ Y) ((flipTors X , flipTors≃ X) ∙ₑ e) e)

-- For two equivalences X ≃ Y, they are equal as soon as they agree on one value

∙eqₜ : ∀ {ℓ} → (X Y : TwoTorsor ℓ) → (e e' : ⟨ X ⟩ ≃ ⟨ Y ⟩) →
  ∀ b → e .fst b ≡ e' .fst b → e ≡ e'
∙eqₜ X Y (f , f≃) (g , g≃) x e = equivEq (funExt (λ x₁ →
  sumrec
  (λ p → cong f (sym p) ∙ e ∙ cong g p)
  (λ p → isEmbedding→Inj (isEquiv→isEmbedding (flipTors≃ Y)) (f x₁) (g x₁)
     (sym (≃comFlip X Y (f , f≃) x₁) ∙ (cong f (sym p) ∙ e ∙ cong g p) ∙ ≃comFlip X Y (g , g≃) x₁))
  (dichotomyTors X x x₁)))
