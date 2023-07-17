open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.FinSet
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin
open import Cubical.Foundations.Everything
open import Cubical.Functions.Involution
open import Cubical.HITs.PropositionalTruncation
open import Sign.Orientation.Base
open import Sign.TwoTorsors
open import Sign.Orientation.FinPart

module Sign.Orientation.Sign where

𝔖 : (n : ℕ) → Type₁
𝔖 n = Fin n ≡ Fin n

pσ : {n : ℕ} → (σ : 𝔖 n) → PathP (λ i → ∥ σ i ≃ Fin n ∥₁) ∣ idEquiv _ ∣₁ ∣ idEquiv _ ∣₁
pσ σ = isProp→PathP (λ _ → isPropPropTrunc) ∣ idEquiv _ ∣₁ ∣ idEquiv _ ∣₁

pσF : {n : ℕ} → 𝔖 n → Path (Σ[ X ∈ Type₀ ] isFinSet X) (Fin n , isFinSetFin) (Fin n , isFinSetFin)
pσF {n = n} σ = ΣPathP (σ , λ i → n , pσ σ i)

sign : {n : ℕ} → 𝔖 n → ori'≃₂ (Fin n , isFinSetFin) ≡ ori'≃₂ (Fin n , isFinSetFin)
sign {n = n} σ = congS ori'≃₂ (pσF σ)

ε : {n : ℕ} → 𝔖 n → Bool
ε {n} = +ₜ≃ (ori'≃₂ (Fin n , isFinSetFin)) .fst ∘ pathToEquiv ∘ congS fst ∘ sign {n = n}

𝔄 : (n : ℕ) → Type₁
𝔄 n = fiber (ε {n = n}) false

𝔖ᶠ : ∀ {ℓ} → (F : FinSet ℓ) → Type (lsuc ℓ)
𝔖ᶠ F = ⟨ F ⟩ ≡ ⟨ F ⟩

signᶠ : ∀ {ℓ} → (F : FinSet ℓ) → 𝔖ᶠ F → ori'≃₂ F ≡ ori'≃₂ F
signᶠ {ℓ = ℓ} F σ = congS ori'≃₂ eq
  where
  eq : PathP (λ _ → Σ[ X ∈ Type ℓ ] (isFinSet X)) F F
  eq = Σ≡Prop (λ _ → isPropIsFinSet) σ

εᶠ : ∀ {ℓ} → (F : FinSet ℓ) → 𝔖ᶠ F → Bool
εᶠ F = +ₜ≃ (ori'≃₂ F) .fst ∘ pathToEquiv ∘ congS fst ∘ signᶠ F

-- Alternative definitions (they do not compute)

signbis : {n : ℕ} → 𝔖 n → ori (Fin n , isFinSetFin) ≡ ori (Fin n , isFinSetFin)
signbis {n = n} σ = congS ori (pσF σ)

signter : {n : ℕ} → 𝔖 n → ori≃ (Fin n , isFinSetFin) ≡ ori≃ (Fin n , isFinSetFin)
signter {n = n} σ = congS ori≃ (pσF σ)

signtet : {n : ℕ} → 𝔖 n → ori' (Fin n , isFinSetFin) ≡ ori' (Fin n , isFinSetFin)
signtet {n = n} σ = congS ori' (pσF σ)

εbis : {n : ℕ} → 𝔖 n → Bool
εbis {n} = +ₜ≃ (ori (Fin n , isFinSetFin)) .fst ∘ pathToEquiv ∘ congS fst ∘ signbis {n = n}

εter : {n : ℕ} → 𝔖 n → Bool
εter {n} = +ₜ≃ (ori≃ (Fin n , isFinSetFin)) .fst ∘ pathToEquiv ∘ congS fst ∘ signter {n = n}

εtet : {n : ℕ} → 𝔖 n → Bool
εtet {n} = +ₜ≃ (ori' (Fin n , isFinSetFin)) .fst ∘ pathToEquiv ∘ congS fst ∘ signtet {n = n}
