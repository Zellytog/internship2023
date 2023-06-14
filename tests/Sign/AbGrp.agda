open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Functions.FunExtEquiv
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Cubical.HITs.SetTruncation renaming (elim to setelim)
open import Cubical.HITs.Truncation
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.HSpace
open import Cubical.Structures.Pointed

module Sign.AbGrp where

private
  variable
    ℓ : Level

infixr 30 _→ₐ_ _≃ₐ_

-- Alias for the properties of being a group, i.e. being an homogeneous connected pointed groupoid

connectedPath : Type ℓ → Type ℓ
connectedPath X = (x : X) (y : X) → ∥ x ≡ y ∥₁

homo∙Ab : ∀ {ℓ} → (X : Type ℓ) → X → Type (lsuc ℓ)
homo∙Ab {ℓ} X x = Σ[ e ∈ ((y : X) → PathP (λ i → Σ[ X ∈ Type ℓ ] X) (X , x) (X , y))] (e x ≡ refl)

AbGrp : ∀ ℓ → Type (lsuc ℓ)
AbGrp ℓ = Σ[ X ∈ Type ℓ ] (Σ[ x ∈ X ] ((connectedPath X) × (isGroupoid X) × (homo∙Ab X x)))

-- Definition of main functions to use the informations of a group

⌈_⌋ : (X : AbGrp ℓ) → Type ℓ
⌈_⌋ = fst

∙ₐ : (X : AbGrp ℓ) → ⌈ X ⌋
∙ₐ = fst ∘ snd

⟨⟨_⟩⟩ : (X : AbGrp ℓ) → Pointed ℓ
⟨⟨ X ⟩⟩ = ⌈ X ⌋ , ∙ₐ X

∥≡∥ₐ : (X : AbGrp ℓ) → connectedPath ⌈ X ⌋
∥≡∥ₐ = fst ∘ snd ∘ snd

groupAb : (X : AbGrp ℓ) → isGroupoid ⌈ X ⌋
groupAb = fst ∘ snd ∘ snd ∘ snd

≡∙ₐ : (X : AbGrp ℓ) → (x : ⌈ X ⌋) → PathP (λ i → Σ[ X ∈ Type ℓ ] X) (⌈ X ⌋ , ∙ₐ X) (⌈ X ⌋ , x)
≡∙ₐ = fst ∘ snd ∘ snd ∘ snd ∘ snd

≡∙ₐr : (X : AbGrp ℓ) → ≡∙ₐ X (∙ₐ X) ≡ refl
≡∙ₐr = snd ∘ snd ∘ snd ∘ snd ∘ snd

-- This is a lemma to show that the condition we use can be translated in being connected in the
-- deinition of cubical

connAb : (X : AbGrp ℓ) → isConnected 2 ⌈ X ⌋
connAb X = subst isContr truncX ( ∣ ∙ₐ X ∣₂ , sym ∘ lemma)
  where
  truncX : ∥ ⌈ X ⌋ ∥₂ ≡ hLevelTrunc 2 ⌈ X ⌋
  truncX = propTrunc≡Trunc2 { A = ⌈ X ⌋}
  lemma : (x : ∥ ⌈ X ⌋ ∥₂) → x ≡ ∣ ∙ₐ X ∣₂
  lemma = setelim (λ x → isProp→isSet (isSetSetTrunc x ∣ ∙ₐ X ∣₂))
    (λ x → proprec (isSetSetTrunc ∣ x ∣₂ ∣ ∙ₐ X ∣₂) (cong ∣_∣₂) (∥≡∥ₐ X x (∙ₐ X)))

-- This function allows to rotate a group and is quite useful

∙→∙ₐ : (X : AbGrp ℓ) → ⌈ X ⌋ → AbGrp ℓ
∙→∙ₐ X x = ⌈ X ⌋ , x , ∥≡∥ₐ X , groupAb X , (λ x₁ → ≡∙ₐ X x ⁻¹ ∙ ≡∙ₐ X x₁) , lCancel (≡∙ₐ X x)

-- Essential lemma for proofs of unicity : the set of dependant functions f : (x : A) -> B x
-- for A connected and B a family of n-types is a n-1-type if we fix one of the values of the f

is-1Type∙ : ∀ {ℓ} {ℓ'} → (n : ℕ) → (A : Pointed ℓ) → (connectedPath ⟨ A ⟩) →
  (B : (x : ⟨ A ⟩) → Type ℓ') → ((x : ⟨ A ⟩) → isOfHLevel (suc n) (B x) ) → (b : B (pt A)) →
  isOfHLevel n (Σ[ f ∈ ((x : ⟨ A ⟩) → B(x)) ] (f (pt A) ≡ b))
is-1Type∙ zero A isconA B isPropB b = ((λ x → proprec (isPropB x) (λ p → subst B p b)
  (isconA (pt A) x)) , isPropB (pt A) _ _) , λ f → Σ≡Prop (λ f → isProp→isSet (isPropB (pt A))
  (f (pt A)) b) (funExt (λ x → isPropB x _ _))
is-1Type∙ (suc n) A isconA B isnlevelB b = isOfHLevelPath'⁻ n
  (λ s1 s2 → subst (λ X → isOfHLevel n X)
  ((cong (λ a → Σ-syntax ((x : ⟨ A ⟩) → fst s1 x ≡ fst s2 x) a) (funExt (λ f → ua (
  (f (pt A) ≡ snd s1 ∙ (sym (snd s2))) ≃⟨ isoToEquiv symIso ⟩
  (snd s1 ∙ (sym (snd s2)) ≡ f (pt A)) ≃⟨ congEquiv (compPathrEquiv (snd s2)) ⟩
  ((snd s1 ∙ sym (snd s2)) ∙ snd s2 ≡ f (pt A) ∙ snd s2)
    ≃⟨ compPathlEquiv ((rUnit (snd s1) ∙ cong (snd s1 ∙_) (sym (lCancel (snd s2))) ∙
    assoc (snd s1) (sym (snd s2)) (snd s2))) ⟩
  snd s1 ≡ f (pt A) ∙ snd s2 ≃⟨ congEquiv (compPathlEquiv (sym (f (pt A)))) ⟩
  (sym (f (pt A)) ∙ snd s1 ≡ sym (f (pt A)) ∙ f (pt A) ∙ snd s2)
    ≃⟨ compPathrEquiv (assoc (sym (f (pt A))) (f (pt A)) (snd s2) ∙
      cong (_∙ snd s2) (lCancel (f (pt A))) ∙ sym (lUnit (snd s2))) ⟩
  (sym (f (pt A)) ∙ snd s1 ≡ snd s2)
    ≃⟨ compPathlEquiv (sym (rUnit (sym (f (pt A)) ∙ snd s1) ∙
      sym (assoc (sym (f (pt A))) (snd s1) (refl)) ∙
      sym (substInPaths (idfun _) (λ _ → b) ((f (pt A))) ((snd s1))))) ⟩
  (subst (λ p → p ≡ b) (f (pt A)) (snd s1) ≡ snd s2)
    ≃⟨ invEquiv (PathP≃Path (λ i → f (pt A) i ≡ b) (snd s1) (snd s2)) ⟩
  (PathP (λ i → (f (pt A) i) ≡ b) (snd s1) (snd s2)) ≃⟨ congPathEquiv (λ i → idEquiv _) ⟩
  (PathP (λ i → funExt f i (pt A) ≡ b) (snd s1) (snd s2))
    ≃⟨ pathToEquiv (cong (λ a → PathP (λ i → a i (pt A) ≡ b) (snd s1) (snd s2))
      (sym (uaβ funExtEquiv f))) ⟩
  (PathP (λ i → transport (funExtPath) f i (pt A) ≡ b) (snd s1) (snd s2) ■
  )))) ∙ Σ-cong-fst funExtPath) ∙ ΣPath≡PathΣ)
  (is-1Type∙ n A isconA (λ a → fst s1 a ≡ fst s2 a)
  (λ a → isOfHLevelPath' (suc n) (isnlevelB a) (fst s1 a) (fst s2 a)) (snd s1 ∙ sym (snd s2))))

-- The first consequence is that being a group is just being a proposition on Pointed ℓ

isPropHomo : (X : Type ℓ) → (x : X) → (connectedPath X) → (isGroupoid X) → isProp (homo∙Ab X x)
isPropHomo X x iscon isgrp = is-1Type∙ 1 (X , x) iscon
  (λ x₁ → (X , x) ≡ (X , x₁)) (λ x₁ → isOfHLevelRespectEquiv 2 (lemma (X → X) (λ f → f x ≡ x₁)
  (isEquiv) ∙ₑ pointedSIP (X , x) (X , x₁)) (isSetΣSndProp
  (is-1Type∙ 2 (X , x) iscon (λ x₂ → X) (λ _ → isgrp) x₁) (λ _ → isPropIsEquiv _))) refl
  where
  lemma : ∀ {ℓ ℓ' ℓ''} → (X : Type ℓ) (Y : (x : X) → Type ℓ') (Z : (x : X) → Type ℓ'') →
    (Σ[ xy ∈ (Σ[ x ∈ X ] Y x)] Z (fst xy)) ≃ (Σ[ xz ∈ (Σ[ x ∈ X ] Z x)] Y (fst xz))
  lemma X Y Z = isoToEquiv (record {
    fun = λ x → (fst (fst x) , snd x) , snd (fst x) ;
    inv = λ x → (fst (fst x) , snd x) , snd (fst x) ;
    leftInv = λ x → refl ;
    rightInv = λ x → refl})

Ab∙Prop : (X : Type ℓ) → (x : X) → isProp ((connectedPath X) × (isGroupoid X) × (homo∙Ab X x))
Ab∙Prop X x = isPropΣ (isPropΠ (λ x → isPropΠ(λ y → isPropPropTrunc)))
  (λ p → isPropΣ isPropIsGroupoid (λ q → (isPropHomo X x p q)))

-- We now define the notion of morhism in 𝔸𝕓

AbMorph : (X : AbGrp ℓ) → (Y : AbGrp ℓ) → Type ℓ
AbMorph X Y = ⟨⟨ X ⟩⟩ →∙ ⟨⟨ Y ⟩⟩

_→ₐ_ = AbMorph

idₐ : (X : AbGrp ℓ) → X →ₐ X
idₐ X = idfun ⌈ X ⌋ , refl

module _ (X : AbGrp ℓ) (Y : AbGrp ℓ) where

  0ₐ : X →ₐ Y
  0ₐ = (λ _ → ∙ₐ Y) , refl

  isSet→ₐ : isSet (X →ₐ Y)
  isSet→ₐ = is-1Type∙ 2 ⟨⟨ X ⟩⟩ (∥≡∥ₐ X) (λ _ → ⌈ Y ⌋) (λ _ → groupAb Y) (∙ₐ Y)

  →A≡ : {f : X →ₐ Y} {g : X →ₐ Y} → fst f ≡ fst g  → f ≡ g
  →A≡ p = →∙Homogeneous≡ (≡∙ₐ Y) p

-- Basic properties about composition of morphisms

∘ₐ : (X Y Z : AbGrp ℓ) → (X →ₐ Y) → (Y →ₐ Z) → (X →ₐ Z)
∘ₐ X Y Z f g = g .fst ∘ f .fst , (cong (g .fst) (f .snd) ∙ (g .snd))

lUnitMorph : (X Y : AbGrp ℓ) → (f : X →ₐ Y) → ∘ₐ X X Y (idₐ X) f ≡ f
lUnitMorph X Y f =  ΣPathP (∘-idˡ (f .fst) , toPathP (transportRefl _ ∙ sym (lUnit (f .snd))))

rUnitMorph : (X Y : AbGrp ℓ) → (f : X →ₐ Y) → ∘ₐ X Y Y f (idₐ Y) ≡ f
rUnitMorph X Y f = ΣPathP (∘-idˡ (fst f) , toPathP (transportRefl _ ∙ sym (rUnit (snd f))))

lAbsMorph : (X Y Z : AbGrp ℓ) → (f : Y →ₐ Z) → ∘ₐ X Y Z (0ₐ X Y) f ≡ 0ₐ X Z
lAbsMorph X Y Z f = →A≡ X Z (funExt (λ _ → snd f))

rAbsMorph : (X Y Z : AbGrp ℓ) → (f : X →ₐ Y) → ∘ₐ X Y Z f (0ₐ Y Z) ≡ 0ₐ X Z
rAbsMorph X Y Z f = →A≡ X Z (funExt (λ _ → refl))

assocMorph : (X Y Z A : AbGrp ℓ) → (f : X →ₐ Y) → (g : Y →ₐ Z) → (h : Z →ₐ A) →
  ∘ₐ X Z A (∘ₐ X Y Z f g) h ≡ ∘ₐ X Y A f (∘ₐ Y Z A g h)
assocMorph X Y Z A (f , f∙) (g , g∙) (h , h∙) = sym (ΣPathP (refl , q))
  where
  q : (cong (h ∘ g) f∙) ∙ (cong h g∙ ∙ h∙) ≡ cong h (cong g f∙ ∙ g∙) ∙ h∙
  q = ( (cong (h ∘ g) f∙) ∙ (cong h g∙ ∙ h∙)
      ≡⟨ refl ⟩
      (cong h (cong g f∙)) ∙ (cong h g∙ ∙ h∙)
      ≡⟨ assoc (cong h (cong g f∙)) (cong h g∙) h∙ ⟩
      (cong h (cong g f∙) ∙ cong h g∙) ∙ h∙
      ≡⟨ cong (λ p → p ∙ h∙) ((cong-∙ h (cong g f∙) g∙) ⁻¹) ⟩
      (cong h (cong g f∙ ∙ g∙) ∙ h∙) ∎ )

-- Definitions of equivalences in 𝔸𝕓 and a version of ua for it

EquivMorph : (X Y : AbGrp ℓ) → Type ℓ
EquivMorph X Y = Σ[ e ∈ (⌈ X ⌋ ≃ ⌈ Y ⌋)] (e .fst (∙ₐ X) ≡ ∙ₐ Y)

_≃ₐ_ = EquivMorph

id≃ₐ : (X : AbGrp ℓ) → (X ≃ₐ X)
id≃ₐ X = idEquiv ⌈ X ⌋ , refl

module _ (X : AbGrp ℓ) (Y : AbGrp ℓ) where

  ≃ₐ→ₐ : X ≃ₐ Y → X →ₐ Y
  ≃ₐ→ₐ e = (e .fst .fst , e .snd)

  ≡≃ₐ : (e f : X ≃ₐ Y) → (e ≡ f) ≃ (≃ₐ→ₐ e ≡ ≃ₐ→ₐ f)
  ≡≃ₐ e f = invEquiv ΣPath≃PathΣ ∙ₑ Σ-cong-equiv-fst
    (invEquiv (Σ≡PropEquiv (λ x → isPropIsEquiv x))) ∙ₑ ΣPath≃PathΣ

  ≡fstsnd : (X ≡ Y) → (⟨⟨ X ⟩⟩ ≡ ⟨⟨ Y ⟩⟩)
  ≡fstsnd e i = ⌈ e i ⌋ , ∙ₐ (e i)
    
  exp≡ : (⟨⟨ X ⟩⟩ ≡ ⟨⟨ Y ⟩⟩) → (X ≡ Y)
  exp≡ e i = ⟨ e i ⟩ , pt (e i) , isProp→PathP
    (λ i → Ab∙Prop ⟨ e i ⟩ (pt (e i))) (X .snd .snd) (Y .snd .snd) i
  
  uaₐ : (X ≃ₐ Y) → (X ≡ Y)
  uaₐ (e , p) = ΣPathP (ua (e) , ΣPathPProp (λ y → Ab∙Prop ⌈ Y ⌋ y)
    (toPathP (uaβ e (∙ₐ X) ∙ p)))

  pathTo≃ₐ :(X ≡ Y) → (X ≃ₐ Y)
  pathTo≃ₐ e = pathToEquiv (cong ⌈_⌋ e) , fromPathP (cong ∙ₐ e)

  uaₐβ : (e : X ≃ₐ Y) → pathTo≃ₐ (uaₐ e) ≡ e
  uaₐβ e = invEquiv (≡≃ₐ (pathTo≃ₐ (uaₐ e)) e) .fst (→A≡ X Y (funExt (λ x → uaβ (e .fst) x)))

record Isoₐ {ℓ} (X : AbGrp ℓ) (Y : AbGrp ℓ) : Type (lsuc ℓ) where
  constructor isoₐ
  field
    funₐ : X →ₐ Y
    invₐ : Y →ₐ X
    rightInvₐ : ∘ₐ Y X Y invₐ funₐ ≡ idₐ Y
    leftInvₐ : ∘ₐ X Y X funₐ invₐ ≡ idₐ X

Isoₐ→Iso : (X : AbGrp ℓ) (Y : AbGrp ℓ) → Isoₐ X Y → Iso ⌈ X ⌋ ⌈ Y ⌋
Isoₐ→Iso X Y f .Iso.fun = f .Isoₐ.funₐ .fst
Isoₐ→Iso X Y f .Iso.inv = f .Isoₐ.invₐ .fst
Isoₐ→Iso X Y f .Iso.leftInv x = cong (λ f → fst f x) (f .Isoₐ.leftInvₐ)
Isoₐ→Iso X Y f .Iso.rightInv x = cong (λ f → fst f x) (f .Isoₐ.rightInvₐ)

Isoₐ→≃ₐ : (X : AbGrp ℓ) (Y : AbGrp ℓ) → Isoₐ X Y → X ≃ₐ Y
Isoₐ→≃ₐ X Y f = isoToEquiv (Isoₐ→Iso X Y f) , f .Isoₐ.funₐ .snd

-- Description of the "group" operation +ₐ given by homogeneity in an abelian group
-- and proofs that (⌈X⌋,+ₐ) is indeed an abelian group except for being a set

module _ (X : AbGrp ℓ) where

  +ₐ : ⌈ X ⌋ → ⌈ X ⌋ → ⌈ X ⌋
  +ₐ x = transport (cong fst (≡∙ₐ X x))

  actAbIdf : +ₐ (∙ₐ X) ≡ idfun ⌈ X ⌋
  actAbIdf = funExt (λ x → ((λ i → transport (λ j → ≡∙ₐr X i j .fst) x) ∙ transportRefl x))

  actAbIdr : ∀ x → +ₐ x (∙ₐ X) ≡ x
  actAbIdr x = fromPathP (PathPΣ (≡∙ₐ X x) .snd)

  actAbIdl : ∀ x → +ₐ (∙ₐ X) x ≡ x
  actAbIdl x = cong (_$ x) actAbIdf

  abHSpace : HSpace ⟨⟨ X ⟩⟩
  abHSpace = Iso.inv (HSpace-Π∙-Iso ⟨⟨ X ⟩⟩) s
    where
    s : Π∙ ⟨⟨ X ⟩⟩ (λ x → ⟨⟨ X ⟩⟩ →∙ (⌈ X ⌋ , x)) (idfun∙ ⟨⟨ X ⟩⟩)
    fst s x = (+ₐ x , actAbIdr x)
    snd s = →∙Homogeneous≡ (X .snd .snd .snd .snd .fst) actAbIdf

  leftInvAbHSpace : LeftInvHSpace abHSpace
  LeftInvHSpace.μ-equiv leftInvAbHSpace x = snd (pathToEquiv (cong fst (≡∙ₐ X x)))

  +cfun : Type ℓ
  +cfun = Σ[ g ∈ ((x : ⌈ X ⌋) → X →ₐ (∙→∙ₐ X x))] (g (∙ₐ X) ≡ idₐ X)

  isProp+cfun : isProp +cfun
  isProp+cfun = is-1Type∙ 1 ⟨⟨ X ⟩⟩ (∥≡∥ₐ X)
    (λ x → X →ₐ (∙→∙ₐ X x)) (λ x → isSet→ₐ X (∙→∙ₐ X x)) (idₐ X)

  +cfl : +cfun
  +cfl .fst x₀ .fst x₁ = +ₐ x₀ x₁
  +cfl .fst x₀ .snd = actAbIdr x₀
  +cfl .snd = →A≡ X (∙→∙ₐ X (∙ₐ X)) (funExt actAbIdl)
  
  +cfr : +cfun
  +cfr .fst x₀ .fst x₁ = +ₐ x₁ x₀
  +cfr .fst x₀ .snd = actAbIdl x₀
  +cfr .snd = →A≡ X (∙→∙ₐ X (∙ₐ X)) (funExt actAbIdr)

  +ₐcom : ∀ x₀ x₁ → +ₐ x₀ x₁ ≡ +ₐ x₁ x₀
  +ₐcom x₀ x₁ = cong (λ a → a .fst x₀ .fst x₁) (isProp+cfun +cfl +cfr)

  +afun : Type ℓ
  +afun = Σ[ g ∈ ((x₀ : ⌈ X ⌋) → (x₁ : ⌈ X ⌋) → X →ₐ (∙→∙ₐ X (+ₐ x₀ x₁)))] (g (∙ₐ X) ≡ fun)
    where
    fun : (x₁ : ⌈ X ⌋) → X →ₐ (∙→∙ₐ X (+ₐ (∙ₐ X) x₁))
    fun x₁ = (λ x₂ → +ₐ (+ₐ (∙ₐ X) x₁) x₂) , actAbIdr (+ₐ (∙ₐ X) x₁)

  isProp+afun : isProp +afun
  isProp+afun = is-1Type∙ 1 ⟨⟨ X ⟩⟩ (∥≡∥ₐ X)
    (λ x₀ → (x₁ : ⌈ X ⌋) → X →ₐ (∙→∙ₐ X (+ₐ x₀ x₁)))
    (λ x₀ → isSetΠ (λ x₁ → isSet→ₐ X (∙→∙ₐ X (+ₐ x₀ x₁))))
    (λ x₁ → (λ x₂ → +ₐ (+ₐ (∙ₐ X) x₁) x₂) , actAbIdr (+ₐ (∙ₐ X) x₁))

  +afl : +afun
  +afl .fst x₀ x₁ .fst x₂ = +ₐ (+ₐ x₀ x₁) x₂
  +afl .fst x₀ x₁ .snd = actAbIdr (+ₐ x₀ x₁)
  +afl .snd = funExt (λ x₁ → →A≡ X (∙→∙ₐ X (+ₐ (∙ₐ X) x₁))
    (funExt (λ x₂ → refl)))

  +afr : +afun
  +afr .fst x₀ x₁ .fst x₂ = +ₐ x₀ (+ₐ x₁ x₂)
  +afr .fst x₀ x₁ .snd = cong (λ a → +ₐ x₀ a) (actAbIdr x₁)
  +afr .snd = funExt (λ x₁ → →A≡ X (∙→∙ₐ X (+ₐ (∙ₐ X) x₁))
    (funExt (λ x₂ → actAbIdl (+ₐ x₁ x₂) ∙ cong (λ a → +ₐ a x₂) (sym (actAbIdl x₁)))))

  +ₐassoc : ∀ x₀ x₁ x₂ → +ₐ (+ₐ x₀ x₁) x₂ ≡ +ₐ x₀ (+ₐ x₁ x₂)
  +ₐassoc x₀ x₁ x₂ = cong (λ a → a .fst x₀ x₁ .fst x₂) (isProp+afun +afl +afr)

  _⁻¹ᵃ : ⌈ X ⌋ → ⌈ X ⌋
  x ⁻¹ᵃ = transport (cong fst (sym (≡∙ₐ X x))) (∙ₐ X)

  lCancelₐ : ∀ x → +ₐ x (x ⁻¹ᵃ) ≡ ∙ₐ X
  lCancelₐ x = sym (transportComposite (cong fst (sym (≡∙ₐ X x))) (cong fst (≡∙ₐ X x)) (∙ₐ X)) ∙
    cong (λ a → transport a (∙ₐ X)) (sym (cong-∙ fst (sym (≡∙ₐ X x)) (≡∙ₐ X x))) ∙
    cong (λ a → transport (cong fst a) (∙ₐ X)) (lCancel (≡∙ₐ X x)) ∙ transportRefl (∙ₐ X)

  rCancelₐ : ∀ x → +ₐ (x ⁻¹ᵃ) x ≡ ∙ₐ X
  rCancelₐ x = +ₐcom (x ⁻¹ᵃ) x ∙ lCancelₐ x

-- A morphism in 𝔸𝕓[X,Y] commutes with +ₐ

module _ (X : AbGrp ℓ) (Y : AbGrp ℓ) ((f , f∙) : X →ₐ Y) where

  →+ : (x : ⌈ X ⌋) → X →ₐ (∙→∙ₐ Y (f x))
  →+ x = (λ x₁ → +ₐ Y (f x) (f x₁)) , cong (λ a → +ₐ Y (f x) a) f∙ ∙ actAbIdr Y (f x)

  +→ : (x : ⌈ X ⌋)  → X →ₐ (∙→∙ₐ Y (f x))
  +→ x = (λ x₁ → f (+ₐ X x x₁)) , cong f (actAbIdr X x)

  bifun∙ : Type ℓ
  bifun∙ = Σ[ g ∈ ((x : ⌈ X ⌋) → X →ₐ (∙→∙ₐ Y (f x)))] (g (∙ₐ X) ≡ (f , refl))

  isPropbifun∙ : isProp bifun∙
  isPropbifun∙ = is-1Type∙ 1 ⟨⟨ X ⟩⟩ (∥≡∥ₐ X)
    (λ x → X →ₐ (∙→∙ₐ Y (f x))) (λ x → isSet→ₐ X (∙→∙ₐ Y (f x))) (f , refl)

  →+∈bifun∙ : bifun∙
  →+∈bifun∙ = →+ , →A≡ X (∙→∙ₐ Y (f (∙ₐ X)))
    (funExt (λ x → cong (λ a → +ₐ Y a (f x)) (f∙) ∙ actAbIdl Y (f x)))

  +→∈bifun∙ : bifun∙
  +→∈bifun∙ = +→ , →A≡ X (∙→∙ₐ Y (f (∙ₐ X)))
    (funExt (λ x → cong f (actAbIdl X x)))

  +→≡→+ : →+ ≡ +→
  +→≡→+ = cong fst (isPropbifun∙ →+∈bifun∙ +→∈bifun∙)

  →ₐ+ : (x₀ x₁ : ⌈ X ⌋) → +ₐ Y (f x₀) (f x₁) ≡ f (+ₐ X x₀ x₁)
  →ₐ+ x₀ x₁ = cong (λ a → a x₀ .fst x₁) +→≡→+

-- {0} is both initial and terminal

nulₐ : AbGrp ℓ
nulₐ = Unit* , tt* , (λ x → λ y → ∣ isOfHLevelLift 1 isPropUnit x y ∣₁) ,
  isOfHLevelLift 3 (isOfHLevelUnit 3) , (λ x i → Unit* , isOfHLevelLift 1 isPropUnit tt* x i),
  λ i j → Lift Unit , isOfHLevelLift 2 isSetUnit tt* tt*
    (isOfHLevelLift 1 isPropUnit tt* tt*) refl i j

initNulₐ : (X : AbGrp ℓ) → isContr (nulₐ →ₐ X)
initNulₐ X = 0ₐ nulₐ X , λ f → →A≡ nulₐ X
  (funExt (λ x → sym (snd f) ∙ cong (fst f) (isOfHLevelLift 1 isPropUnit tt* x)))

finNulₐ : (X : AbGrp ℓ) → isContr (X →ₐ nulₐ)
finNulₐ X = 0ₐ X nulₐ , λ f → →A≡ X nulₐ
  (funExt (λ x → isOfHLevelLift 1 isPropUnit tt* (fst f x)))
