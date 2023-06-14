open import Cubical.Data.Nat
open import Agda.Primitive
open import Cubical.Data.Bool
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sum renaming (rec to sumrec)
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Data.SumFin renaming (elim to finelim)
open import Cubical.Relation.Nullary
open import Sign.AbGrp
open import Sign.BinBiprod
open import Sign.FinBiprod

module Sign.FinSetSum where

private
  variable
    ℓ : Level
{-
⊕ₐ0 : Ab⨁ (0 , zrec {A = AbGrp ℓ})
⊕ₐ0 = nulₐ ,
  (((λ x → zrec x) , λ A → record {equiv-proof =
    λ y → (((0ₐ nulₐ A , isContr→isProp isContrΠ⊥ _ _)) ,
    λ z → Σ≡Prop (λ f → isContr→isOfHLevel 2 isContrΠ⊥ _ _) ((initNulₐ A .snd (fst z)))) }) ,
  ((λ x → zrec x) , λ A → record {equiv-proof =
    λ y → (((0ₐ A nulₐ , isContr→isProp isContrΠ⊥ _ _)) ,
    λ z → Σ≡Prop (λ f → isContr→isOfHLevel 2 isContrΠ⊥ _ _) ((finNulₐ A .snd (fst z)))) })) ,
  isContr→isProp (initNulₐ nulₐ) _ (idₐ nulₐ)
   ∙ {!sym (funTypeTransp ⟨_⟩ (λ _ → AbGrp ℓ)
                   (Σ≡Prop (λ _ → isPropIsFinSet) (ua (p ∙ₑ LiftEquiv) ⁻¹)) {!f!})!}
-}
