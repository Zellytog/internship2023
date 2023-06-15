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
open import Sign.TwoTorsors
open import Sign.Orientation.Base

module Sign.Orientation.Sign where

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
