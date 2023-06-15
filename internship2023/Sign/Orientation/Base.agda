open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Empty
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Cubical.Relation.Nullary
open import Sign.AbGrp
open import Sign.TwoTorsors

module Sign.Orientation.Base where

private
  variable
    ℓ : Level

-- Given a family (Aᵢ) of abelian groups, we define the group ∏ Aᵢ

connectedN : (n : ℕ) → (f : Fin n → AbGrp ℓ) →
  connectedPath ((x : Lift {j = ℓ} (Fin n)) → ⌈ (f ∘ lower) x ⌋)
connectedN 0 f x y = ∣ funExt (λ a → cong (λ b → b (lower a))
  (isContr→isProp isContrΠ⊥ (x ∘ lift) (y ∘ lift))) ∣₁
connectedN (suc n) f x y = proprec (λ _ → isPropPropTrunc _)
  (λ p → proprec (λ _ → isPropPropTrunc _) (λ q → ∣ funExt (λ a →
     decRec (λ r → subst (λ b → x b ≡ y b) (sym r) q)
            (λ r → subst (λ b → x b ≡ y b) (sym (lemmaLiftFin n a r .snd))
              (cong (_$ (lift (fst (lemmaLiftFin n a r)))) p))
     (isFinSet→Discrete ((suc n , ∣ invEquiv LiftEquiv ∣₁)) a (lift fzero))) ∣₁)
    (∥≡∥ₐ (f fzero) (x (lift fzero)) (y (lift (fzero)))))
  (connectedN n (f ∘ fsuc) (x ∘ lift ∘ fsuc ∘ lower) (y ∘ lift ∘ fsuc ∘ lower))

connectedFin : (f : Finₐ ℓ) → connectedPath ((x : Lift {j = ℓ} (Fin  $ fst f)) → ⌈ snd f (lower x) ⌋)
connectedFin f = connectedN (fst f) (snd f)

∏ₐ : FinSetₐ ℓ → AbGrp ℓ
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

TakeTuple : (f : FinSetₐ ℓ) → (x : ⟨ fst f ⟩) → ∏ₐ f →ₐ snd f x
TakeTuple f x .fst a = a x
TakeTuple f x .snd = refl

injTuple : (f : FinSetₐ ℓ) → ∏ₐ f →ₐ ⨁ₐ f
injTuple f = ⟨⟩ᶠ (∏ₐ f) f (TakeTuple f)

-- For an abelian group A, we can define the constant family (A) and then define the sum of elements
-- of A indexed by a finite set I, as ∇ᴵ (λ _ → idₐ A) 

module _ (X : AbGrp ℓ) (J : FinSet ℓ) where

  cstₛ : FinSetₐ ℓ
  cstₛ = J , λ _ → X

  ∏ᶜ : AbGrp ℓ
  ∏ᶜ = ∏ₐ cstₛ

  ∇ₛ : ⨁ₐ cstₛ →ₐ X
  ∇ₛ = []ᶜˢ cstₛ (Ab⨁→Ab+s cstₛ (⨁ₜ cstₛ)) X (λ _ → (idₐ X))

  Sumₛ : ∏ᶜ →ₐ X
  Sumₛ = ∘ₐ ∏ᶜ (⨁ₐ cstₛ) X (injTuple cstₛ) ∇ₛ

  Σₛ : (⟨ J ⟩ → ⌈ X ⌋) → ⌈ X ⌋
  Σₛ f = Sumₛ .fst f

-- Now we can turn back to the type TwoTorsors and define a sum of sets of 2 elements indexed by a
-- finite set

2TorsGrp : ∀ {ℓ} → AbGrp (lsuc ℓ)
2TorsGrp {ℓ} = TwoTorsor ℓ , pointedTors , connexeTors2 , isgroupoidTors , homoTors , homoEqRefl

Σ₂ : ∀ {ℓ} → (J : FinSet (lsuc ℓ)) → (⟨ J ⟩ → TwoTorsor ℓ) → TwoTorsor ℓ
Σ₂ J f = Σₛ 2TorsGrp J f

-- We define ℙᵈ, the decidable powerset of a finite set, and ℙᵈ₂ as the subset of 2 elements and
-- prove that this is a finite index set

ℙᵈ : Type ℓ → Type ℓ
ℙᵈ X = X → Bool

ℙᵈ₂ : Type ℓ → Type (lsuc ℓ)
ℙᵈ₂ X = Σ[ P ∈ ℙᵈ X ] ∥ (fiber P true) ≡ Lift Bool ∥₁

isFinℙᵈ : (X : Type ℓ) → isFinSet X → isFinSet (ℙᵈ X)
isFinℙᵈ X isFin = isFinSet→ ((X , isFin)) ((Bool , isFinSetBool))

isFinℙᵈ₂ : (X : Type ℓ) → isFinSet X → isFinSet (ℙᵈ₂ X)
isFinℙᵈ₂ X isFin = isFinSetΣ ((ℙᵈ X , isFinℙᵈ X isFin))
  (λ P → ∥ (fiber P true) ≡ Lift Bool ∥₁ ,
    isFinSet∥∥ (((fiber P true) ≡ Lift Bool) , isFinSetType≡
      ((fiber P true , isFinSetFiber ((X , isFin)) ((Bool , isFinSetBool)) P true))
      ((Lift Bool , EquivPresIsFinSet LiftEquiv isFinSetBool))))

-- Finally, as an element of ℙᵈ₂ is in TwoTorsor, we can sum all those elements, which is the
-- orientation of a finite set X

ℙᵈ₂Tors : (X : Type ℓ) → ℙᵈ₂ X → TwoTorsor ℓ
ℙᵈ₂Tors X P = fiber (P .fst) true , P .snd

ori : (X : FinSet ℓ) → TwoTorsor ℓ
ori X = Σ₂ (ℙᵈ₂ ⟨ X ⟩ , isFinℙᵈ₂ ⟨ X ⟩ (snd X)) (ℙᵈ₂Tors ⟨ X ⟩)
