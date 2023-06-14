open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Sign.AbGrp
open import Sign.BinBiprod

module Sign.Monoidal where

private
  variable
    ℓ : Level

-- We prove here that (𝔸𝕓,⊕ₐ) is a monoidal symmetric category

-- First we show that ⊕ₐ defines a bifunctor

⊕ₐ→ : (X Y A B : AbGrp ℓ) → (X →ₐ Y) → (A →ₐ B) → (X ⊕ₐ A) →ₐ Y ⊕ₐ B
⊕ₐ→ X Y A B f g = ⟨⟩ᵇ (X ⊕ₐ A) Y B (∘ₐ (X ⊕ₐ A) X Y (π₁ X A) f) (∘ₐ (X ⊕ₐ A) A B (π₂ X A) g)

⊕ₐ→' : (X Y A B : AbGrp ℓ) → (X →ₐ Y) → (A →ₐ B) → (X ⊕ₐ A) →ₐ Y ⊕ₐ B
⊕ₐ→' X Y A B f g = []ᵇ X A (Y ⊕ₐ B) (∘ₐ X Y (Y ⊕ₐ B) f (κ₁ Y B)) (∘ₐ A B (Y ⊕ₐ B) g (κ₂ Y B))

-- Both definition coincide

⊕ₐ→∃! : (X Y A B : AbGrp ℓ) → (f : X →ₐ Y) (g : A →ₐ B) → ⊕ₐ→ X Y A B f g ≡ ⊕ₐ→' X Y A B f g
⊕ₐ→∃! X Y A B f g = ∃!UPκ X A (Y ⊕ₐ B) (∘ₐ X Y (Y ⊕ₐ B) f (κ₁ Y B)) (∘ₐ A B (Y ⊕ₐ B) g (κ₂ Y B))
  (⊕ₐ→ X Y A B f g)
  (⟨⟩∘⃖ X (X ⊕ₐ A) Y B (κ₁ X A) (∘ₐ (X ⊕ₐ A) X Y (π₁ X A) f) (∘ₐ (X ⊕ₐ A) A B (π₂ X A) g) ∙
  cong₂ (λ a b → ⟨⟩ᵇ X Y B a b) (sym (assocMorph X (X ⊕ₐ A) X Y (κ₁ X A) (π₁ X A) f) ∙
                                     cong (λ a → ∘ₐ X X Y a f) (κ₁∘π₁ X A) ∙ lUnitMorph X Y f)
                                (sym (assocMorph X (X ⊕ₐ A) A B (κ₁ X A) (π₂ X A) g) ∙
                                  cong (λ a → ∘ₐ X A B a g) (κ₁∘π₂ X A) ∙ lAbsMorph X A B g) ∙
  cong₂ (λ a b → ⟨⟩ᵇ X Y B a b) (sym (rUnitMorph X Y f)) (sym (rAbsMorph X Y B f)) ∙
  sym (⟨⟩∘⃖ X Y Y B f (idₐ Y) (0ₐ Y B)) ∙ cong (λ a → ∘ₐ X Y (Y ⊕ₐ B) f a) (⟨⟩ᵇκ₁ Y B))
  (⟨⟩∘⃖ A (X ⊕ₐ A) Y B (κ₂ X A) (∘ₐ (X ⊕ₐ A) X Y (π₁ X A) f) (∘ₐ (X ⊕ₐ A) A B (π₂ X A) g) ∙
    cong₂ (λ a b → ⟨⟩ᵇ A Y B a b) (sym (assocMorph A (X ⊕ₐ A) X Y (κ₂ X A) (π₁ X A) f) ∙
                                       cong (λ a → ∘ₐ A X Y a f) (κ₂∘π₁ X A) ∙ lAbsMorph A X Y f)
                                  (sym (assocMorph A (X ⊕ₐ A) A B (κ₂ X A) (π₂ X A) g) ∙
                                       cong (λ a → ∘ₐ A A B a g) (κ₂∘π₂ X A) ∙ lUnitMorph A B g) ∙
    cong₂ (λ a b → ⟨⟩ᵇ A Y B a b) (sym (rAbsMorph A B Y g)) (sym (rUnitMorph A B g)) ∙
    sym (⟨⟩∘⃖ A B Y B g (0ₐ B Y) (idₐ B)) ∙ cong (λ a → ∘ₐ A B (Y ⊕ₐ B) g a) (⟨⟩ᵇκ₂ Y B))

-- F(f∘g) ≡ F(f)∘F(g)

⊕ₐ∘ : (X Y Z A B C : AbGrp ℓ) → (f : X →ₐ Y) (g : A →ₐ B) (f' : Y →ₐ Z) (g' : B →ₐ C) →
  ∘ₐ (X ⊕ₐ A) (Y ⊕ₐ B) (Z ⊕ₐ C) (⊕ₐ→ X Y A B f g) (⊕ₐ→ Y Z B C f' g') ≡
  ⊕ₐ→ X Z A C (∘ₐ X Y Z f f') (∘ₐ A B C g g')
⊕ₐ∘ X Y Z A B C f g f' g' = ⟨⟩∘⃖ (X ⊕ₐ A) (Y ⊕ₐ B) Z C (⊕ₐ→ X Y A B f g)
  (∘ₐ (Y ⊕ₐ B) Y Z (π₁ Y B) f') (∘ₐ (Y ⊕ₐ B) B C (π₂ Y B) g') ∙
  cong₂ (λ a b → ⟨⟩ᵇ (X ⊕ₐ A) Z C a b)
    (sym (assocMorph (X ⊕ₐ A) (Y ⊕ₐ B) Y Z (⊕ₐ→ X Y A B f g) (π₁ Y B) f') ∙
    cong (λ a → ∘ₐ (X ⊕ₐ A) Y Z a f') (π⟨⟩l (X ⊕ₐ A) Y B (∘ₐ (X ⊕ₐ A) X Y (π₁ X A) f)
                                                         (∘ₐ (X ⊕ₐ A) A B (π₂ X A) g)) ∙
    assocMorph (X ⊕ₐ A) X Y Z (π₁ X A) f f')
    (sym (assocMorph (X ⊕ₐ A) (Y ⊕ₐ B) B C (⊕ₐ→ X Y A B f g) (π₂ Y B) g') ∙
    cong (λ a → ∘ₐ (X ⊕ₐ A) B C a g') (π⟨⟩r (X ⊕ₐ A) Y B (∘ₐ (X ⊕ₐ A) X Y (π₁ X A) f)
                                                         (∘ₐ (X ⊕ₐ A) A B (π₂ X A) g)) ∙
    assocMorph (X ⊕ₐ A) A B C (π₂ X A) g g')
    
-- F(id,id) ≡ id

⊕ₐid : (X A : AbGrp ℓ) → ⊕ₐ→ X X A A (idₐ X) (idₐ A) ≡ idₐ (X ⊕ₐ A)
⊕ₐid X A = cong₂ (λ a b → ⟨⟩ᵇ (X ⊕ₐ A) X A a b) (rUnitMorph (X ⊕ₐ A) X (π₁ X A))
                                                (rUnitMorph (X ⊕ₐ A) A (π₂ X A))
  ∙ ∃!UPπId X A (⟨⟩ᵇ (X ⊕ₐ A) X A (π₁ X A) (π₂ X A))
    (π⟨⟩l (X ⊕ₐ A) X A (π₁ X A) (π₂ X A)) (π⟨⟩r (X ⊕ₐ A) X A (π₁ X A) (π₂ X A))

-- 
