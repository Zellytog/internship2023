open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Induction
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to sumrec ; elim to sumelim)
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Foundations.Everything
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Cubical.Relation.Nullary
open import Sign.AbGrp
open import Sign.TwoTorsors
open import Sign.Orientation.FinPart
open import Sign.Orientation.BinPart

module Sign.Orientation.Base where

private
  variable
    ℓ ℓ' : Level

-- Given a family (Aᵢ) of abelian groups, we define the group ∏ Aᵢ

connectedN : ∀ {ℓ} {ℓ'} → (n : ℕ) → (f : Fin n → AbGrp ℓ) →
  connectedPath ((x : Lift {j = ℓ'} (Fin n)) → ⌈ (f ∘ lower) x ⌋)
connectedN {ℓ} {ℓ'} 0 f x y = ∣ funExt (λ a → cong (λ b → b (lower a))
  (isContr→isProp isContrΠ⊥ (x ∘ lift) (y ∘ lift))) ∣₁
connectedN {ℓ} {ℓ'} (suc n) f x y = proprec (λ _ → isPropPropTrunc _)
  (λ p → proprec (λ _ → isPropPropTrunc _) (λ q → ∣ funExt (λ a →
     decRec (λ r → subst (λ b → x b ≡ y b) (sym r) q)
            (λ r → subst (λ b → x b ≡ y b) (sym (lemmaLiftFin n a r .snd))
              (cong (_$ (lift {j = ℓ'} (fst (lemmaLiftFin n a r)))) p))
     (isFinSet→Discrete ((suc n , ∣ invEquiv LiftEquiv ∣₁)) a (lift fzero))) ∣₁)
    (∥≡∥ₐ (f fzero) (x (lift fzero)) (y (lift (fzero)))))
  (connectedN n (f ∘ fsuc) (x ∘ lift ∘ fsuc ∘ lower) (y ∘ lift ∘ fsuc ∘ lower))

connectedFin : (f : Finₐ ℓ) → connectedPath ((x : Lift {j = ℓ'} (Fin  $ fst f)) → ⌈ snd f (lower x) ⌋)
connectedFin f = connectedN (fst f) (snd f)

∏ₐ : FinSetₐ ℓ ℓ' → AbGrp (ℓ-max ℓ ℓ')
∏ₐ ((X , e) , f) = ((x : X) → ⌈ f x ⌋) ,
  ∙ₐ ∘ f ,
  (FinSetₐrec (λ f → connectedPath ((x : ⟨ fst f ⟩) → ⌈ snd f x ⌋))
    (λ _ → isPropΠ(λ _ → isPropΠ (λ _ → isPropPropTrunc)))
    connectedFin ((X , e) , f)) ,
  isGroupoidΠ (λ x → groupAb (f x)) ,
  (λ y → λ i → ((x : X) → ≡∙ₐ (f x) (y x) i .fst) , λ x → ≡∙ₐ (f x) (y x) i .snd) ,
  (λ j → λ i → ((x : X) → ≡∙ₐr (f x) j i .fst) , λ x → ≡∙ₐr (f x) j i .snd)

-- This allows us to construct the function which, given (x₁,...,xₙ) ∈ A₁×...×Aₙ, gives respectively
-- x₁, x₂ ... which, when we pair it, gives a function ∏ Aᵢ →ₐ ⨁ Aᵢ

TakeTuple : ∀ {ℓ ℓ'} → (f : FinSetₐ (ℓ-max ℓ ℓ') ℓ') → (x : ⟨ fst f ⟩) → ∏ₐ f →ₐ snd f x
TakeTuple f x .fst a = a x
TakeTuple f x .snd = refl

injTuple : ∀ {ℓ ℓ'} → (f : FinSetₐ (ℓ-max ℓ ℓ') ℓ') → ∏ₐ f →ₐ ⨁ₐ f
injTuple {ℓ} {ℓ'} f = ⟨⟩ᶠ (∏ₐ f) f (TakeTuple {ℓ = ℓ} {ℓ' = ℓ'} f)

-- For an abelian group A, we can define the constant family (A) and then define the sum of elements
-- of A indexed by a finite set I, as ∇ᴵ (λ _ → idₐ A) 

module _ (X : AbGrp (ℓ-max ℓ ℓ')) (J : FinSet ℓ') where

  cstₛ : FinSetₐ (ℓ-max ℓ ℓ') ℓ'
  cstₛ = J , λ _ → X

  ∏ᶜ : AbGrp (ℓ-max ℓ ℓ')
  ∏ᶜ = ∏ₐ cstₛ

  ∇ₛ : ⨁ₐ cstₛ →ₐ X
  ∇ₛ = []ᶜˢ cstₛ (Ab⨁→Ab+s cstₛ (⨁ₜ cstₛ)) X (λ _ → (idₐ X))

  Sumₛ : ∏ᶜ →ₐ X
  Sumₛ = ∘ₐ ∏ᶜ (⨁ₐ cstₛ) X (injTuple {ℓ} {ℓ'} cstₛ) ∇ₛ

  Σₛ : (⟨ J ⟩ → ⌈ X ⌋) → ⌈ X ⌋
  Σₛ f = Sumₛ .fst f

-- Now we can turn back to the type TwoTorsors and define a sum of sets of 2 elements indexed by a
-- finite set

2TorsGrp : ∀ {ℓ} → AbGrp (lsuc ℓ)
2TorsGrp {ℓ} = TwoTorsor ℓ , ∙ₜ , connexeTors2 , isgroupoidTors , HomoTors , HomoEqRefl

2TorsGrp≃ : ∀ {ℓ} → AbGrp (lsuc ℓ)
2TorsGrp≃ {ℓ} = TwoTorsor ℓ , ∙ₜ , connexeTors2 , isgroupoidTors , HomoTors2 , HomoEqRefl2

Σ₂ : ∀ {ℓ ℓ'} → (J : FinSet ℓ') → (⟨ J ⟩ → TwoTorsor (ℓ-max ℓ ℓ')) → TwoTorsor (ℓ-max ℓ ℓ')
Σ₂ J f = Σₛ 2TorsGrp J f

Σ₂≃ : ∀ {ℓ ℓ'} → (J : FinSet ℓ') → (⟨ J ⟩ → TwoTorsor (ℓ-max ℓ ℓ')) → TwoTorsor (ℓ-max ℓ ℓ')
Σ₂≃ J f = Σₛ 2TorsGrp≃ J f

-- Finally, as an element of ℙᵈ₂ is in TwoTorsor, we can sum all those elements, which is the
-- orientation of a finite set X

ℙᵈ₂Tors : (X : Type ℓ) → ℙᵈᵢ 2 X → TwoTorsor ℓ
ℙᵈ₂Tors X P = fiber (P .fst) true , proprec isPropPropTrunc (∣_∣₁ ∘ (_∙ₑ SumFin2≃Bool)) (P .snd)

-- A few possible definitions of orientation, with our different constructions of the sum
-- the last one is the one we will use for ε but do behave badly to compute directly an orientation

ori : ∀ {ℓ} → (X : FinSet ℓ) → TwoTorsor ℓ
ori {ℓ} X = Σ₂ {ℓ = ℓ} {ℓ' = ℓ} (ℙᵈᵢ 2 ⟨ X ⟩ , isFinℙᵈᵢ 2 X) (ℙᵈ₂Tors ⟨ X ⟩)

ori≃ : ∀ {ℓ} → (X : FinSet ℓ) → TwoTorsor ℓ
ori≃ {ℓ} X = Σ₂≃ {ℓ = ℓ} {ℓ' = ℓ} (ℙᵈᵢ 2 ⟨ X ⟩ , isFinℙᵈᵢ 2 X) (ℙᵈ₂Tors ⟨ X ⟩)

ori' : ∀ {ℓ} → (X : FinSet ℓ) → TwoTorsor ℓ
ori' {ℓ} X = Σ₂ᵀ (ℙᵈᵢ 2 ⟨ X ⟩ , isFinℙᵈᵢ 2 X) (ℙᵈ₂Tors ⟨ X ⟩)

ori'≃ : ∀ {ℓ} → (X : FinSet ℓ) → TwoTorsor ℓ
ori'≃ {ℓ} X = Σᵀᶠ≃ (ℙᵈᵢ 2 ⟨ X ⟩ , isFinℙᵈᵢ 2 X) (ℙᵈ₂Tors ⟨ X ⟩)

ori'≃₂ : ∀ {ℓ} → (X : FinSet ℓ) → TwoTorsor ℓ
ori'≃₂ {ℓ} X = Σᵀᶠ≃ {ℓ = ℓ} {ℓ' = ℓ} (ℙᵈᵢ 2 ⟨ X ⟩ , isFinℙᵈ₂ X) (ℙᵈ₂Tors ⟨ X ⟩)
