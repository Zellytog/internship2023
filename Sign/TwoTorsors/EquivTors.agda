open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to sumrec)
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Functions.Embedding
open import Cubical.Functions.Involution
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Cubical.Structures.Pointed
open import Sign.TwoTorsors.Base
open import Sign.TwoTorsors.Sum

module Sign.TwoTorsors.EquivTors where

private
  variable
    ℓ : Level

-- We show that the homogeneity in TwoTorsor can also be done with the function X ↦ Y ↦ X ≃ Y

isNeutralLeft : (X : TwoTorsor ℓ) → (⟨ ∙ₜ {ℓ = ℓ}⟩ ≃ ⟨ X ⟩) ≃ ⟨ X ⟩
isNeutralLeft X .fst e = e .fst (lift false)
isNeutralLeft X .snd .equiv-proof x .fst .fst = invEquiv LiftEquiv
  ∙ₑ ((λ b → +ₜ X b .fst x) , isTrans+ₜ X x)
isNeutralLeft X .snd .equiv-proof x .fst .snd = cong ((_$ x) ∘ fst) (+ₜ0 X)
isNeutralLeft X .snd .equiv-proof x .snd e = Σ≡Prop
  (λ x₁ → isSetTors X (fst (isNeutralLeft X) x₁) x)
  (∙eqₜ ∙ₜ X (fst (isNeutralLeft X .snd .equiv-proof x) .fst) (e .fst) (lift false)
    (cong ((_$ x) ∘ fst) (+ₜ0 X) ∙ e .snd ⁻¹))

isNeutralRight : ∀ {ℓ} → (X : TwoTorsor ℓ) → (⟨ X ⟩ ≃ ⟨ ∙ₜ {ℓ = ℓ} ⟩) ≃ ⟨ X ⟩
isNeutralRight X .fst e = invEquiv e .fst (lift false)
isNeutralRight X .snd .equiv-proof x .fst =
  invEquiv (invEquiv LiftEquiv ∙ₑ ((λ b → +ₜ X b .fst x) , isTrans+ₜ X x)) ,
  cong ((_$ x) ∘ fst) (+ₜ0 X)
isNeutralRight {ℓ} X .snd .equiv-proof x .snd e = Σ≡Prop
  (λ x₁ → isSetTors X (fst (isNeutralRight X) x₁) x)
  (∙eqₜ X ∙ₜ (fst (isNeutralRight X .snd .equiv-proof x) .fst) (e .fst) x
  (sym (invEquiv
  (equivAdjointEquiv (invEquiv LiftEquiv ∙ₑ ((λ b → +ₜ X b .fst x) , isTrans+ₜ X x))) .fst
    (cong ((_$ x) ∘ fst) (+ₜ0 X)))
  ∙ sym (invEq≡→equivFun≡ (e .fst) (e .snd))))
{-
isContrFiber∙ : ∀ {ℓ} → isContr (fiber (∙ₜ {ℓ = ℓ} ≃ₜ_) (∙ₜ {ℓ = ℓ}))
isContrFiber∙ {ℓ} .fst .fst = ∙ₜ {ℓ = ℓ}
isContrFiber∙ {ℓ} .fst .snd = Σ≡Prop (λ _ → isPropPropTrunc) (ua (+ₜ≃ ∙ₜ ∙ₑ LiftEquiv))
isContrFiber∙ {ℓ} .snd (Y , e) = ΣPathP (Σ≡Prop (λ _ → isPropPropTrunc)
  (cong fst (sym e) ∙ ua (isNeutralLeft Y)) , toPathP
  ((substInPathsR {a = ∙ₜ } {x1 = ∙ₜ ≃ₜ ∙ₜ} {x2 = ∙ₜ ≃ₜ Y}
    (λ i → ∙ₜ ≃ₜ (Σ≡Prop (λ _ → isPropPropTrunc) (cong fst (sym e)
    ∙ ua (isNeutralLeft Y))) i)
    (isContrFiber∙ .fst .snd)
  ∙ {!!} )))
-}

Oper≃ : (X Y : TwoTorsor ℓ) → (x : ⟨ X ⟩) (y : ⟨ Y ⟩) →
  isContr(Σ[ e ∈ ⟨ X ⟩ ≃ ⟨ Y ⟩ ] (e .fst x ≡ y))
Oper≃ (X , e) (Y , e') x y = proprec isPropIsContr (λ f → proprec isPropIsContr (λ f' →
  (f ∙ₑ invEquiv f' ∙ₑ +ₜ (Y , e') (isTrans+ₜ (Y , e')
    ((f ∙ₑ invEquiv f') .fst x) .equiv-proof y .fst .fst) ,
  isTrans+ₜ (Y , e') ((f ∙ₑ invEquiv f') .fst x) .equiv-proof y .fst .snd) ,
  λ y₁ → Σ≡Prop (λ x₁ → isSetTors (Y , e') (x₁ .fst x) y) (∙eqₜ (X , e) (Y , e') (f ∙ₑ
    invEquiv f' ∙ₑ +ₜ (Y , e') (isTrans+ₜ (Y , e') ((f ∙ₑ invEquiv f') .fst x)
      .equiv-proof y .fst .fst)) (y₁ .fst) x
    (isTrans+ₜ (Y , e') ((f ∙ₑ invEquiv f') .fst x) .equiv-proof y .fst .snd ∙ sym (y₁ .snd))))
  e') e

+₌ : (X Y : TwoTorsor ℓ) → (x : ⟨ X ⟩) (y : ⟨ Y ⟩) → ⟨ X ⟩ ≃ ⟨ Y ⟩
+₌ X Y x y = Oper≃ X Y x y .fst .fst

Oper≃isFun : (X Y : TwoTorsor ℓ) → (x₀ x₁ : ⟨ X ⟩) (y : ⟨ Y ⟩) → x₀ ≡ x₁ → +₌ X Y x₀ y ≡ +₌ X Y x₁ y
Oper≃isFun X Y x₀ x₁ y = cong (λ a → +₌ X Y a y)

bilinl+₌ : (X Y : TwoTorsor ℓ) → (x : ⟨ X ⟩) (y : ⟨ Y ⟩) → (b : Bool) →
  +₌ X Y (+ₜₐ X b x) y ≡ +ₜₐ (X ≃ₜ Y) b (+₌ X Y x y)
bilinl+₌ X Y x y false = Oper≃isFun X Y (+ₜₐ X false x) x y (cong ((_$ x) ∘ fst) (+ₜ0 X))
  ∙ cong (λ a → a .fst (+₌ X Y x y)) (sym (+ₜ0 (X ≃ₜ Y)))
bilinl+₌ X Y x y true = ∙eqₜ X Y (+₌ X Y (+ₜₐ X true x) y) (+ₜₐ (X ≃ₜ Y) true (+₌ X Y x y)) x
  (sumrec
    (λ p → zrec (¬Flip (X ≃ₜ Y) (+₌ X Y x y) (∙eqₜ X Y (+₌ X Y x y)
      (flipTors (X ≃ₜ Y) (+₌ X Y x y)) x (Oper≃ X Y x y .fst .snd ∙ sym p))))
    (λ p → cong (+₌ X Y (+ₜₐ X true x) y .fst) (sym (isNilFlip X x))
      ∙ ≃comFlip X Y (+₌ X Y (+ₜₐ X true x) y) (+ₜₐ X true x)
      ∙ cong (flipTors Y) (Oper≃ X Y (+ₜₐ X true x) y .fst .snd)
      ∙ sym p)
  (dichotomyTors Y (+ₜₐ (X ≃ₜ Y) true (+₌ X Y x y) .fst x) y))

Oper≃isFun2 : (X Y : TwoTorsor ℓ) → (x : ⟨ X ⟩) (y₀ y₁ : ⟨ Y ⟩) → y₀ ≡ y₁ → +₌ X Y x y₀ ≡ +₌ X Y x y₁
Oper≃isFun2 X Y x y₀ y₁ = cong (λ a → +₌ X Y x a)

bilinr+₌ : (X Y : TwoTorsor ℓ) → (x : ⟨ X ⟩) (y : ⟨ Y ⟩) → (b : Bool) →
  +₌ X Y x (+ₜₐ Y b y) ≡ +ₜₐ (X ≃ₜ Y) b (+₌ X Y x y)
bilinr+₌ X Y x y false = Oper≃isFun2 X Y x (+ₜₐ Y false y) y (cong ((_$ y) ∘ fst) (+ₜ0 Y))
  ∙ cong (λ a → a .fst (+₌ X Y x y)) (sym (+ₜ0 (X ≃ₜ Y)))
bilinr+₌ X Y x y true = ∙eqₜ X Y (+₌ X Y x (+ₜₐ Y true y)) (+ₜₐ (X ≃ₜ Y) true (+₌ X Y x y)) x
  (sumrec
    (λ p → zrec (¬Flip (X ≃ₜ Y) (+₌ X Y x y) (∙eqₜ X Y (+₌ X Y x y) (flipTors (X ≃ₜ Y) (+₌ X Y x y))
      x (Oper≃ X Y x y .fst .snd ∙ sym p))))
    (λ p → Oper≃ X Y x (+ₜₐ Y true y) .fst .snd ∙ sym p)
  (dichotomyTors Y (+ₜₐ (X ≃ₜ Y) true (+₌ X Y x y) .fst x) y))

is+²ᵀ≃ₜ : (X Y : TwoTorsor ℓ) → +²ᵀ X Y
is+²ᵀ≃ₜ X Y = (X ≃ₜ Y , +₌ X Y) , λ x y b → bilinl+₌ X Y x y b , bilinr+₌ X Y x y b

+ᵀ≡≃ₜ : (X Y : TwoTorsor ℓ) → X +ᵀ Y ≡ X ≃ₜ Y
+ᵀ≡≃ₜ X Y = cong (fst ∘ fst) (isContr+²ᵀ X Y .snd (is+²ᵀ≃ₜ X Y))

≃≃ₜ : ∀ {ℓ} → (X : TwoTorsor ℓ) → TwoTorsor ℓ ≃ TwoTorsor ℓ
≃≃ₜ X = _≃ₜ X , subst isEquiv (funExt (λ Y → +ᵀ≡≃ₜ Y X)) (≃+ᵀ X .snd)

HomoTors2 : ∀ {ℓ} → (X : TwoTorsor ℓ) → (TwoTorsor ℓ , ∙ₜ {ℓ = ℓ}) ≡ (TwoTorsor ℓ , X)
HomoTors2 {ℓ} X = pointed-sip (TwoTorsor ℓ , ∙ₜ) (TwoTorsor ℓ , X)
  (≃≃ₜ X , Σ≡Prop (λ _ → isPropPropTrunc) (ua (isNeutralLeft X)))

HomoEqRefl2 : ∀ {ℓ} → HomoTors2 {ℓ} ∙ₜ ≡ refl
HomoEqRefl2 {ℓ = ℓ} = cong (pointed-sip (TwoTorsor ℓ , ∙ₜ) (TwoTorsor ℓ , ∙ₜ))
  (ΣPathP hom≡≃) ∙ pointed-sip-idEquiv∙ (TwoTorsor ℓ , ∙ₜ)
  where
  hom≡ : Σ[ p ∈ (_≃ₜ ∙ₜ) ≡ idfun (TwoTorsor ℓ) ] PathP (λ i → p i ∙ₜ ≡ ∙ₜ)
    (Σ≡Prop (λ _ → isPropPropTrunc) (ua (isNeutralLeft ∙ₜ))) refl
  hom≡ = PathPΣ (→∙Homogeneous≡ HomoTors2 (funExt λ Y → Σ≡Prop (λ _ → isPropPropTrunc)
    (ua (isNeutralRight Y))))
  hom≡1 : (_≃ₜ ∙ₜ) ≡ idfun (TwoTorsor ℓ)
  hom≡1 = hom≡ .fst
  hom≡2 : PathP (λ i → hom≡1 i ∙ₜ ≡ ∙ₜ) (Σ≡Prop (λ _ → isPropPropTrunc) (ua (isNeutralLeft ∙ₜ))) refl
  hom≡2 = hom≡ .snd
  hom≡1≃ : ≃≃ₜ ∙ₜ ≡ idEquiv (TwoTorsor ℓ)
  hom≡1≃ = equivEq hom≡1
  hom≡2≃ : PathP (λ i → hom≡1≃ i .fst ∙ₜ ≡ ∙ₜ)
    (Σ≡Prop (λ _ → isPropPropTrunc) (ua (isNeutralLeft ∙ₜ))) refl
  hom≡2≃ = hom≡2
  hom≡≃ : Σ[ p ∈ ≃≃ₜ ∙ₜ ≡ idEquiv (TwoTorsor ℓ)] PathP (λ i → p i .fst ∙ₜ ≡ ∙ₜ)
    (Σ≡Prop (λ _ → isPropPropTrunc) (ua (isNeutralLeft ∙ₜ))) refl
  hom≡≃ = hom≡1≃ , hom≡2≃
