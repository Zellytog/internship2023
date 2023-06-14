open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation
open import Sign.AbGrp
open import Sign.BinBiprod
open import Sign.FinBiprod
open import Sign.FinSetBiprod
open import Sign.TwoTorsors

module Sign.SumTors where

private
  variable
    ℓ : Level

2TorsGrp : ∀ {ℓ} → AbGrp (lsuc ℓ)
2TorsGrp {ℓ} = TwoTorsor ℓ , pointedTors , connexeTors2 , isgroupoidTors ,
  homoTors , homoEqRefl

Σ₂ : ∀ {ℓ} → (J : FinSet (lsuc ℓ)) → (⟨ J ⟩ → TwoTorsor ℓ) → TwoTorsor ℓ
Σ₂ J f = Σₛ 2TorsGrp J f

ℙᵈ : Type ℓ → Type ℓ
ℙᵈ X = X → Bool

isFinℙᵈ : (X : Type ℓ) → isFinSet X → isFinSet (ℙᵈ X)
isFinℙᵈ X isFin = isFinSet→ ((X , isFin)) ((Bool , isFinSetBool))

ℙᵈ₂ : Type ℓ → Type (lsuc ℓ)
ℙᵈ₂ X = Σ[ P ∈ ℙᵈ X ] ∥ (fiber P true) ≡ Lift Bool ∥₁

isFinℙᵈ₂ : (X : Type ℓ) → isFinSet X → isFinSet (ℙᵈ₂ X)
isFinℙᵈ₂ X isFin = isFinSetΣ ((ℙᵈ X , isFinℙᵈ X isFin))
  (λ P → ∥ (fiber P true) ≡ Lift Bool ∥₁ ,
    isFinSet∥∥ (((fiber P true) ≡ Lift Bool) , isFinSetType≡
      ((fiber P true , isFinSetFiber ((X , isFin)) ((Bool , isFinSetBool)) P true))
      ((Lift Bool , EquivPresIsFinSet LiftEquiv isFinSetBool))))

ℙᵈ₂Tors : (X : Type ℓ) → ℙᵈ₂ X → TwoTorsor ℓ
ℙᵈ₂Tors X P = fiber (P .fst) true , P .snd

ori : (X : FinSet ℓ) → TwoTorsor ℓ
ori X = Σ₂ (ℙᵈ₂ ⟨ X ⟩ , isFinℙᵈ₂ ⟨ X ⟩ (snd X)) (ℙᵈ₂Tors ⟨ X ⟩)

𝔖 : (n : ℕ) → Type₁
𝔖 n = Fin n ≡ Fin n

sign : {n : ℕ} → 𝔖 n → ori (Fin n , isFinSetFin) ≡ ori (Fin n , isFinSetFin)
sign {n = n} σ = cong ori (Σ≡Prop (λ _ → isPropIsFinSet) {u = Fin n , isFinSetFin}
  {v = Fin n , isFinSetFin} σ)

εₗ : {n : ℕ} → 𝔖 n → Lift {j = lzero} Bool
εₗ {n = n} σ = invEquiv (actTors (ori (Fin n , isFinSetFin)) ,
                 isEquivActTors (ori (Fin n , isFinSetFin)))
       .fst $ pathToEquiv (cong fst (sign σ))

ε : {n : ℕ} → 𝔖 n → Bool
ε = lower ∘ εₗ

𝔄 : (n : ℕ) → Type₁
𝔄 n = fiber (ε {n = n}) false
