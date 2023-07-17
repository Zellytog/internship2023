open import Cubical.Data.Nat
open import Agda.Primitive
open import Cubical.Data.Bool
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.FinSet
open import Cubical.Data.SumFin
open import Cubical.Relation.Nullary
open import Sign.AbGrp.Base
open import Sign.AbGrp.BinBiprod
open import Sign.AbGrp.FinSetBiprod

-- In this module we show that Ab⨁ₛ is not only a proposition, but is also contractible,
-- as one would expect.

module Sign.AbGrp.FinBiprod where

private
  variable
    ℓ ℓ' : Level

-- We define a family of abelian groups indexed by 1,...,n

Finₐ : ∀ ℓ → Type (lsuc ℓ)
Finₐ ℓ = Σ[ n ∈ ℕ ] (Fin n → AbGrp ℓ)

-- There is however a way to convert it into a finite family

Finₐ→FinSetₐ : ∀ {ℓ} ℓ' → Finₐ ℓ → FinSetₐ ℓ ℓ'
Finₐ→FinSetₐ ℓ' (n , f) = (Lift {j = ℓ'} (Fin n) , (n , ∣ invEquiv LiftEquiv ∣₁)) , f ∘ lower

FinSetₐ→Finₐ : ∀ {ℓ ℓ'} → (X : FinSet ℓ') → (n : ℕ) → (⟨ X ⟩ ≡ Lift (Fin n)) →
  (⟨ X ⟩ → AbGrp ℓ) → Finₐ ℓ
FinSetₐ→Finₐ {ℓ = ℓ} X n e f = (n , subst (λ X → X → AbGrp ℓ) e f ∘ lift)

-- This recursion property means that proving a proposition for all FinSetₐ can be
-- done by proving it only for families indexed by 1,...,n

FinSetₐrec : ∀ {ℓ ℓ' ℓ''} → (B : FinSetₐ ℓ ℓ' → Type ℓ'') → (∀ f → isProp (B f)) →
  ((f : Finₐ ℓ) → B (Finₐ→FinSetₐ ℓ' f)) → ∀ f → B f
FinSetₐrec {ℓ} {ℓ'} B isPropB forallf ((X , (n , iseqn)) , f) =
  proprec (isPropB ((X , (n , iseqn)) , f))
    (λ p → subst B ((ΣPathP ((Σ≡Prop (λ _ → isPropIsFinSet) ( ua (p ∙ₑ LiftEquiv) ⁻¹) , 
      (symP (funTypeTransp ⟨_⟩ (λ _ → AbGrp ℓ) {x = (X , (n , iseqn))}
          {y = (Lift (Fin n) , (n , ∣ invEquiv LiftEquiv ∣₁))}
          (sym (Σ≡Prop (λ _ → isPropIsFinSet) (ua (p ∙ₑ LiftEquiv) ⁻¹))) f))))))
    (forallf (FinSetₐ→Finₐ (X , (n , iseqn)) n (ua (p ∙ₑ LiftEquiv)) f))) iseqn

lemmaLiftFin : (n : ℕ) → (x : Lift {j = ℓ'} (Fin (suc n))) → ¬ x ≡ lift fzero →
  Σ[ y ∈ Fin n ] x ≡ lift (fsuc y)
lemmaLiftFin n (lift fzero) p = zrec $ p refl
lemmaLiftFin n (lift (fsuc k)) p = k , refl

-- We define the biproduct of A₁,...,Aₙ by (...(A₁⊕A₂)⊕...)⊕Aₙ and the projection
-- (resp coprojection) by πᵢⁿ = (π₁)°⁽ⁱ⁻¹⁾∘π₂ and then prove that it is indeed the
-- biproduct of A₁,...,Aₙ

⨁ᶠ : (n : ℕ) → (f : Fin n → AbGrp ℓ) → AbGrp ℓ
⨁ᶠ 0 f = nulₐ
⨁ᶠ (suc n) f = (⨁ᶠ n (f ∘ fsuc)) ⊕ₐ (f fzero)

πᶠ : (n : ℕ) → (f : Fin n → AbGrp ℓ) → (x : Fin n) → (⨁ᶠ n f) →ₐ f x
πᶠ 0 f x = zrec x
πᶠ (suc n) f fzero = π₂ (⨁ᶠ n (f ∘ fsuc)) (f fzero)
πᶠ (suc n) f (fsuc x) = ∘ₐ (⨁ᶠ (suc n) f) (⨁ᶠ n (f ∘ fsuc)) (f (fsuc x))
  (π₁ (⨁ᶠ n (f ∘ fsuc)) (f fzero)) (πᶠ n (f ∘ fsuc) x)

κᶠ : (n : ℕ) → (f : Fin n → AbGrp ℓ) → (x : Fin n) → f x →ₐ (⨁ᶠ n f)
κᶠ 0 f x = zrec x
κᶠ (suc n) f fzero = κ₂ (⨁ᶠ n (f ∘ fsuc)) (f fzero)
κᶠ (suc n) f (fsuc x) = ∘ₐ (f $ fsuc x) (⨁ᶠ n (f ∘ fsuc)) (⨁ᶠ (suc n) f)
  (κᶠ n (f ∘ fsuc) x) (κ₁ (⨁ᶠ n (f ∘ fsuc)) (f fzero))

uπᶠ : ∀ {ℓ ℓ'} (n : ℕ) → (f : Fin n → AbGrp ℓ) →
  u×s (Finₐ→FinSetₐ ℓ' (n , f)) (⨁ᶠ n f , (λ x → πᶠ n f (lower x)))
uπᶠ {ℓ} {ℓ'} 0 f A .equiv-proof g = (0ₐ A nulₐ ,
  isOfHLevelRespectEquiv 1 (equivΠ LiftEquiv (λ _ → idEquiv _)) (isContr→isProp isContrΠ⊥)
  (distrib×s (Finₐ→FinSetₐ ℓ' (zero , f)) (nulₐ , (λ x → zrec (lower x))) A (0ₐ A nulₐ)) g) ,
  λ z → Σ≡Prop (λ f → (isOfHLevelRespectEquiv 2 (equivΠ LiftEquiv (λ _ → idEquiv _))
    (isContr→isOfHLevel 2 isContrΠ⊥) _ _)) (finNulₐ A .snd (fst z))
uπᶠ {ℓ} {ℓ'} (suc n) f A .equiv-proof g = (⟨⟩ᵇ A fs f0
  (⟨⟩ₚˢ (Finₐ→FinSetₐ ℓ' (n , f ∘ fsuc)) f× A (g ∘ lift ∘ fsuc ∘ lower))
  (g (lift fzero)), funExt (λ x → decRec
    (λ p → subst (λ b →
      (distrib×s (Finₐ→FinSetₐ ℓ' (suc n , f)) (⨁ᶠ (suc n) f , (λ x₁ → πᶠ (suc n) f (lower x₁))) A
      (⟨⟩ᵇ A fs f0 (⟨⟩ₚˢ (Finₐ→FinSetₐ ℓ' (n , (λ x₁ → f (fsuc x₁)))) f× A
      (λ x₁ → g (lift (fsuc (lower x₁))))) (g (lift fzero))) b) ≡ g b)
      (p ⁻¹) (π⟨⟩r A fs f0 (⟨⟩ₚˢ (Finₐ→FinSetₐ ℓ'(n , (λ x₁ → f (fsuc x₁)))) f× A
       (λ x₁ → g (lift (fsuc (lower x₁))))) (g (lift fzero))))
    ((λ p → subst (λ b →
      (distrib×s (Finₐ→FinSetₐ ℓ' (suc n , f)) (⨁ᶠ (suc n) f , (λ x₁ → πᶠ (suc n) f (lower x₁))) A
      (⟨⟩ᵇ A fs f0 (⟨⟩ₚˢ (Finₐ→FinSetₐ ℓ' (n , (λ x₁ → f (fsuc x₁)))) f× A
      (λ x₁ → g (lift (fsuc (lower x₁))))) (g (lift fzero))) b) ≡ g b)
      (lemmaLiftFin n x p .snd ⁻¹)
      (sym (assocMorph A (fs ⊕ₐ f0) fs ((f ∘ fsuc ∘ fst) (lemmaLiftFin n x p))
        (⟨⟩ᵇ A fs f0 (⟨⟩ₚˢ (Finₐ→FinSetₐ ℓ' (n , f ∘ fsuc)) f× A (g ∘ lift ∘ fsuc ∘ lower))
        (g (lift fzero))) (π₁ fs f0)
       (πᶠ n (f ∘ fsuc) (fst $ lemmaLiftFin n x p)))
       ∙ cong (λ a → ∘ₐ A fs ((f ∘ fsuc ∘ fst) (lemmaLiftFin n x p)) a
                (πᶠ n (f ∘ fsuc) (fst $ lemmaLiftFin n x p)))
         (π⟨⟩l A fs f0 (⟨⟩ₚˢ (Finₐ→FinSetₐ ℓ' (n , (λ x₁ → f (fsuc x₁)))) f× A
         (λ x₁ → g (lift (fsuc (lower x₁))))) (g (lift fzero)))
       ∙ cong (_$ ((lift ∘ fst) (lemmaLiftFin n x p)))
         (uπᶠ n (f ∘ fsuc) A .equiv-proof (g ∘ lift ∘ fsuc ∘ lower) .fst .snd))))
    ((isFinSet→Discrete ((suc n , ∣ invEquiv LiftEquiv ∣₁)) x (lift fzero))))) ,
  λ y → Σ≡Prop (λ z → isOfHLevelRespectEquiv 1 (funExtEquiv)
    (isPropΠ (λ x → isSet→ₐ A (f (lower x))
      (∘ₐ A (⨁ᶠ (suc n) f) (f (lower x)) z (πᶠ (suc n) f (lower x)))
      (g x)))) (sym (∃!UPπ A fs f0
        (⟨⟩ₚˢ (Finₐ→FinSetₐ ℓ' (n , (λ x → f (fsuc x)))) f× A (λ x → g (lift (fsuc (lower x)))))
        (g (lift fzero))
        (fst y)
      (cong fst (sym (uπᶠ n (f ∘ fsuc) A .equiv-proof (g ∘ lift ∘ fsuc ∘ lower) .snd
        (∘ₐ A (fs ⊕ₐ f0) fs (fst y) (π₁ fs f0) ,
          funExt (λ x → assocMorph A (fs ⊕ₐ f0) fs (f (fsuc (lower x))) (fst y)
            (π₁ fs f0) (πᶠ n (f ∘ fsuc) (lower x))
            ∙ cong (_$ ((lift ∘ fsuc ∘ lower) x)) (y .snd))))))
      (λ i → y .snd i (lift fzero))))
  where
  f0 = f fzero
  fs = (⨁ᶠ n (f ∘ fsuc))
  f× : Ab×s (Finₐ→FinSetₐ ℓ' (n , f ∘ fsuc))
  f× = ((fs , πᶠ n (f ∘ fsuc) ∘ lower), uπᶠ n (f ∘ fsuc))

uκᶠ : ∀ {ℓ ℓ'} (n : ℕ) → (f : Fin n → AbGrp ℓ) →
  u+s (Finₐ→FinSetₐ ℓ' (n , f)) (⨁ᶠ n f , (λ x → κᶠ n f (lower x)))
uκᶠ {ℓ} {ℓ'} 0 f A .equiv-proof g = (0ₐ nulₐ A ,
  isOfHLevelRespectEquiv 1 (equivΠ LiftEquiv (λ _ → idEquiv _)) (isContr→isProp isContrΠ⊥)
  (distrib+s (Finₐ→FinSetₐ ℓ' (zero , f)) (nulₐ , (λ x → zrec (lower x))) A (0ₐ nulₐ A)) g) ,
  λ z → Σ≡Prop (λ f → (isOfHLevelRespectEquiv 2 (equivΠ LiftEquiv (λ _ → idEquiv _))
    (isContr→isOfHLevel 2 isContrΠ⊥) _ _)) (initNulₐ A .snd (fst z))
uκᶠ {ℓ} {ℓ'} (suc n) f A .equiv-proof g = (([]ᵇ fs f0 A
  ([]ᶜˢ (Finₐ→FinSetₐ ℓ' (n , f ∘ fsuc)) f+ A (g ∘ lift ∘ fsuc ∘ lower))
  (g (lift fzero)), funExt (λ x → decRec
    (λ p → subst (λ b →
      (distrib+s (Finₐ→FinSetₐ ℓ' (suc n , f)) (⨁ᶠ (suc n) f , (λ x₁ → κᶠ (suc n) f (lower x₁))) A
      ([]ᵇ fs f0 A ([]ᶜˢ (Finₐ→FinSetₐ ℓ' (n , (λ x₁ → f (fsuc x₁)))) f+ A
      (λ x₁ → g (lift (fsuc (lower x₁))))) (g (lift fzero))) b) ≡ g b)
      (p ⁻¹) (κ[]r fs f0 A ([]ᶜˢ (Finₐ→FinSetₐ ℓ' (n , (λ x₁ → f (fsuc x₁)))) f+ A
       (λ x₁ → g (lift (fsuc (lower x₁))))) (g (lift fzero))))
    ((λ p → subst (λ b →
      (distrib+s (Finₐ→FinSetₐ ℓ' (suc n , f)) (⨁ᶠ (suc n) f , (λ x₁ → κᶠ (suc n) f (lower x₁))) A
      ([]ᵇ fs f0 A ([]ᶜˢ (Finₐ→FinSetₐ ℓ' (n , (λ x₁ → f (fsuc x₁)))) f+ A
      (λ x₁ → g (lift (fsuc (lower x₁))))) (g (lift fzero))) b) ≡ g b)
      (lemmaLiftFin n x p .snd ⁻¹)
      (assocMorph ((f ∘ fsuc ∘ fst) (lemmaLiftFin n x p)) fs (fs ⊕ₐ f0) A
        (κᶠ n (f ∘ fsuc) (fst $ lemmaLiftFin n x p)) (κ₁ fs f0)
        ([]ᵇ fs f0 A ([]ᶜˢ (Finₐ→FinSetₐ ℓ' (n , f ∘ fsuc)) f+ A (g ∘ lift ∘ fsuc ∘ lower))
        (g (lift fzero)))
       ∙ cong (λ a → ∘ₐ ((f ∘ fsuc ∘ fst) (lemmaLiftFin n x p)) fs A
                (κᶠ n (f ∘ fsuc) (fst $ lemmaLiftFin n x p)) a)
         (κ[]l fs f0 A ([]ᶜˢ (Finₐ→FinSetₐ ℓ' (n , (λ x₁ → f (fsuc x₁)))) f+ A
         (λ x₁ → g (lift (fsuc (lower x₁))))) (g (lift fzero)))
       ∙ cong (_$ ((lift ∘ fst) (lemmaLiftFin n x p)))
         (uκᶠ n (f ∘ fsuc) A .equiv-proof (g ∘ lift ∘ fsuc ∘ lower) .fst .snd))))
    (isFinSet→Discrete (suc n , ∣ invEquiv LiftEquiv ∣₁) x (lift fzero))))) ,
  λ y → Σ≡Prop (λ z → isOfHLevelRespectEquiv 1 (funExtEquiv)
    (isPropΠ (λ x → isSet→ₐ (f (lower x)) A
      (∘ₐ (f (lower x)) (⨁ᶠ (suc n) f) A (κᶠ (suc n) f (lower x)) z)
      (g x)))) (sym (∃!UPκ fs f0 A
        ([]ᶜˢ (Finₐ→FinSetₐ ℓ' (n , (λ x → f (fsuc x)))) f+ A (λ x → g (lift (fsuc (lower x)))))
        (g (lift fzero))
        (fst y) (cong fst (sym (uκᶠ n (f ∘ fsuc) A .equiv-proof (g ∘ lift ∘ fsuc ∘ lower) .snd
        (∘ₐ fs (fs ⊕ₐ f0) A (κ₁ fs f0) (fst y) ,
          funExt (λ x → sym (assocMorph (f (fsuc (lower x))) fs (fs ⊕ₐ f0) A
            (κᶠ n (f ∘ fsuc) (lower x)) (κ₁ fs f0) (fst y))
            ∙ cong (_$ ((lift ∘ fsuc ∘ lower) x)) (y .snd))))))
        (λ i → y .snd i (lift fzero))))
  where
  f0 = f fzero
  fs = (⨁ᶠ n (f ∘ fsuc))
  f+ : Ab+s (Finₐ→FinSetₐ ℓ' (n , f ∘ fsuc))
  f+ = ((fs , κᶠ n (f ∘ fsuc) ∘ lower), uκᶠ n (f ∘ fsuc))

-- To show the compatibility, we define δFinₐ which works as δFinₛ but is much more easy to compute,
-- and we prove that for a family A₁,...,Aₙ it defines the same function

δFinₐ : (n : ℕ) → (f : Fin n → AbGrp ℓ) → (a b : Fin n) → f a →ₐ f b
δFinₐ 0 f a b = zrec a
δFinₐ (suc n) f fzero fzero = idₐ (f fzero)
δFinₐ (suc n) f (fsuc k) fzero = 0ₐ (f (fsuc k)) (f fzero)
δFinₐ (suc n) f fzero (fsuc k) = 0ₐ (f fzero) (f (fsuc k))
δFinₐ (suc n) f (fsuc k) (fsuc p) = δFinₐ n (f ∘ fsuc) k p

δFinₛ≡δFinₐ : ∀ {ℓ ℓ'} → (n : ℕ) → (f : Fin n → AbGrp ℓ) → (a b : Fin n) →
  δFinₛ (Finₐ→FinSetₐ ℓ' (n , f)) (lift a) (lift b) ≡ δFinₐ n f a b
δFinₛ≡δFinₐ 0 f a = zrec a
δFinₛ≡δFinₐ (suc n) f fzero fzero =  cong
  (λ a → decRec (J (λ b → λ p → f fzero →ₐ f b) (idₐ (f fzero)))
  (λ _ → 0ₐ (f fzero) (f fzero)) a)
    (isPropDec ((isFinSet→isSet (suc n , ∣ idEquiv _ ∣₁) fzero fzero))
      (isFinSet→Discrete (suc n , ∣ idEquiv _ ∣₁) fzero fzero)
    (yes refl))
  ∙ JRefl (λ b → λ p → f fzero →ₐ f b) (idₐ (f fzero))
δFinₛ≡δFinₐ (suc n) f (fsuc k) fzero = cong
  (λ a → decRec (J (λ b → λ p → f (fsuc k) →ₐ f b) (idₐ (f (fsuc k))))
  (λ _ → 0ₐ (f (fsuc k)) (f fzero)) a)
    (isPropDec (isFinSet→isSet (suc n , ∣ idEquiv _ ∣₁) (fsuc k) fzero)
      (isFinSet→Discrete (suc n , ∣ idEquiv _ ∣₁) (fsuc k) fzero)
    (no (snotz ∘ cong toℕ)))
δFinₛ≡δFinₐ (suc n) f fzero (fsuc k) = cong
  (λ a → decRec (J (λ b → λ p → f fzero →ₐ f b) (idₐ (f fzero)))
  (λ _ → 0ₐ (f fzero) (f (fsuc k))) a)
    (isPropDec (isFinSet→isSet (suc n , ∣ idEquiv _ ∣₁) fzero (fsuc k))
      (isFinSet→Discrete (suc n , ∣ idEquiv _ ∣₁) fzero (fsuc k))
    (no (znots ∘ cong toℕ)))
δFinₛ≡δFinₐ {ℓ} {ℓ'} (suc n) f (fsuc k) (fsuc p) = decRec
  (λ q → (cong
  (λ a → decRec (J (λ b → λ p → f (fsuc k) →ₐ f (lower b)) (idₐ (f (fsuc k))))
  (λ _ → 0ₐ (f (fsuc k)) (f (fsuc p))) a)
    ((isPropDec (isFinSet→isSet (suc n , ∣ invEquiv LiftEquiv ∣₁) (lift (fsuc k)) (lift (fsuc p)))
      (isFinSet→Discrete (suc n , ∣ invEquiv LiftEquiv ∣₁) (lift (fsuc k)) (lift (fsuc p)))
    ((yes (cong (lift ∘ fsuc) q))))) ∙ cong
  (λ a → decRec (J (λ b → λ p → f (fsuc k) →ₐ f (fsuc (lower {j = ℓ'} b))) (idₐ (f (fsuc k))))
  (λ _ → 0ₐ (f (fsuc k)) (f (fsuc p))) a)
    (isPropDec (isFinSet→isSet (n , ∣ invEquiv LiftEquiv ∣₁) (lift k) (lift p))
      (yes (cong lift q))
        (isFinSet→Discrete (n , ∣ invEquiv LiftEquiv ∣₁) (lift k) (lift p))))
      ∙ δFinₛ≡δFinₐ n (f ∘ fsuc) k p)
    (λ q → (cong
  (λ a → decRec (J (λ b → λ p → f (fsuc k) →ₐ f (lower b)) (idₐ (f (fsuc k))))
  (λ _ → 0ₐ (f (fsuc k)) (f (fsuc p))) a)
    ((isPropDec (isFinSet→isSet (suc n , ∣ invEquiv LiftEquiv ∣₁) (lift (fsuc k)) (lift (fsuc p)))
      (isFinSet→Discrete (suc n , ∣ invEquiv LiftEquiv ∣₁) (lift (fsuc k)) (lift (fsuc p)))
    ((no (λ r → q (((toℕ-injective ∘ injSuc)) (cong (toℕ ∘ lower) r))))))) ∙ cong
  (λ a → decRec (J (λ b → λ p → f (fsuc k) →ₐ f (fsuc (lower {j = ℓ'} b))) (idₐ (f (fsuc k))))
  (λ _ → 0ₐ (f (fsuc k)) (f (fsuc p))) a)
    (isPropDec (isFinSet→isSet (n , ∣ invEquiv LiftEquiv ∣₁) (lift k) (lift p))
      (no (λ r → q (cong lower r)))
        (isFinSet→Discrete (n , ∣ invEquiv LiftEquiv ∣₁) (lift k) (lift p))))
  ∙ δFinₛ≡δFinₐ n (f ∘ fsuc) k p)
  (isFinSet→Discrete (n , ∣ idEquiv _ ∣₁) k p)

compκπᶠ : ∀ {ℓ} {ℓ'} → (n : ℕ) → (f : Fin n → AbGrp ℓ) → compπκs (Finₐ→FinSetₐ ℓ' (n , f)) (⨁ᶠ n f)
  ((κᶠ n f ∘ lower , uκᶠ n f) , (πᶠ n f ∘ lower , uπᶠ n f))
compκπᶠ {ℓ} {ℓ'} 0 f = isContr→isProp (initNulₐ nulₐ) _ _
compκπᶠ {ℓ} {ℓ'} (suc n) f = cong fst (isContr→isProp (uκᶠ (suc n) f ⨁f .equiv-proof (κf ∘ lower))
  ([]ᶠ ((⨁f , κᶠ (suc n) f ∘ lower) , uκᶠ (suc n) f) ⨁f (λ x →
    ⟨⟩ᶠ ((⨁f , πᶠ (suc n) f ∘ lower) , uπᶠ (suc n) f) (f (lower x))
      (λ y → δFinₛ (Finₐ→FinSetₐ ℓ' (suc n , f)) x y)) , funExt (λ x →
      cong (_$ x) (uκᶠ (suc n) f ⨁f .equiv-proof (λ z → ⟨⟩ᶠ ((⨁f , πᶠ (suc n) f ∘ lower) ,
        uπᶠ (suc n) f) (f (lower z)) (λ y → δFinₛ (Finₐ→FinSetₐ ℓ' (suc n , f)) z y)) .fst .snd)
      ∙  cong fst (uπᶠ (suc n) f (f (lower x)) .equiv-proof
        (λ y → δFinₛ (Finₐ→FinSetₐ ℓ' (suc n , f)) x y) .snd (κf (lower x) , funExt (λ y →
        κⁱ∘πʲ (lower x) (lower y)
      )))))
    (idₐ ⨁f , funExt (λ x → rUnitMorph (f (lower x)) ⨁f (κf (lower x)))))
  where
  ⨁f = ⨁ᶠ (suc n) f
  κf = κᶠ (suc n) f
  πf = πᶠ (suc n) f
  f0 = f fzero
  fs = ⨁ᶠ n (f ∘ fsuc)
  []ᶠ = []ᶜˢ (Finₐ→FinSetₐ ℓ' (suc n , f))
  ⟨⟩ᶠ = ⟨⟩ₚˢ (Finₐ→FinSetₐ ℓ' (suc n , f))
  ⨁fr : Ab⨁ₛ (Finₐ→FinSetₐ ℓ' (n , f ∘ fsuc))
  ⨁fr = ⨁ᶠ n (f ∘ fsuc) , (
    (κᶠ n (f ∘ fsuc) ∘ lower , uκᶠ n (f ∘ fsuc)) ,
    (πᶠ n (f ∘ fsuc) ∘ lower , uπᶠ n (f ∘ fsuc))) ,
    compκπᶠ n (f ∘ fsuc)
  κⁱ∘πʲ : (x y : Fin (suc n)) →
    ∘ₐ (f x) ⨁f (f y) (κf x) (πf y) ≡ δFinₛ (Finₐ→FinSetₐ ℓ' (suc n , f)) (lift x) (lift y)
  κⁱ∘πʲ fzero fzero = κ₂∘π₂ fs f0 ∙ sym (δFinₛ≡δFinₐ {ℓ} {ℓ'} (suc n) f fzero fzero)
  κⁱ∘πʲ fzero (fsuc k) = ((sym (assocMorph (f fzero) ⨁f (⨁fr .fst) (f (fsuc k))
        (κ₂ fs f0) (π₁ fs f0) (πᶠ n (f ∘ fsuc) k))
    ∙ cong (λ a → ∘ₐ (f fzero) (⨁fr .fst) (f (fsuc k)) a (πᶠ n (f ∘ fsuc) k)) (κ₂∘π₁ fs f0))
    ∙ lAbsMorph (f fzero) (⨁fr .fst) (f (fsuc k)) (πᶠ n (f ∘ fsuc) k)
    ∙ sym (δFinₛ≡δFinₐ {ℓ} {ℓ'} (suc n) f fzero (fsuc k)))
  κⁱ∘πʲ (fsuc k) fzero = assocMorph (f (fsuc k)) (⨁fr .fst) ⨁f (f fzero)
        (κᶠ n (f ∘ fsuc) k) (κ₁ fs f0) (π₂ fs f0)
    ∙ cong (λ a → ∘ₐ (f (fsuc k)) (⨁fr .fst) (f fzero) (κᶠ n (f ∘ fsuc) k) a) (κ₁∘π₂ fs f0)
    ∙ rAbsMorph (f (fsuc k)) (⨁fr .fst) (f fzero) (κᶠ n (f ∘ fsuc) k)
    ∙ sym (δFinₛ≡δFinₐ {ℓ} {ℓ'} (suc n) f (fsuc k) fzero)
  κⁱ∘πʲ (fsuc k) (fsuc p) = assocMorph (f (fsuc k)) (⨁fr .fst) ⨁f (f (fsuc p))
    (κᶠ n (f ∘ fsuc) k) (κ₁ fs f0) (πf (fsuc p))
    ∙ cong (λ a → ∘ₐ (f (fsuc k)) (⨁fr .fst) (f (fsuc p)) (κᶠ n (f ∘ fsuc) k) a)
      (sym (assocMorph (⨁fr .fst) ⨁f (⨁fr .fst) (f (fsuc p)) (κ₁ fs f0) (π₁ fs f0)
        (πᶠ n (f ∘ fsuc) p)))
    ∙ cong (λ a → ∘ₐ (f (fsuc k)) (⨁fr .fst) (f (fsuc p)) (κᶠ n (f ∘ fsuc) k) a)
      (cong (λ b → ∘ₐ (⨁fr .fst) (⨁fr .fst) (f (fsuc p)) b (πᶠ n (f ∘ fsuc) p)) (κ₁∘π₁ fs f0)
        ∙ lUnitMorph (⨁fr .fst) (f (fsuc p)) (πᶠ n (f ∘ fsuc) p))
    ∙ κᵢ∘πᵢ (Finₐ→FinSetₐ ℓ' (n , f ∘ fsuc)) ⨁fr (lift k) (lift p)
    ∙ δFinₛ≡δFinₐ n (f ∘ fsuc) k p ∙ sym (δFinₛ≡δFinₐ (suc n) f (fsuc k) (fsuc p))

-- By recursion on FinSetₐ we can thus, as Ab⨁ₛ is a proposition, construct an element of
-- Ab⨁ₛ for any f : Finₐ and thus any f : FinSetₐ

Ab⨁ᶠ : (f : Finₐ ℓ) → Ab⨁ₛ (Finₐ→FinSetₐ ℓ' f)
Ab⨁ᶠ f = ⨁ᶠ (fst f) (snd f) , (
  (κᶠ (fst f) (snd f) ∘ lower , uκᶠ (fst f) (snd f)) ,
  (πᶠ (fst f) (snd f) ∘ lower , uπᶠ (fst f) (snd f))) ,
  compκπᶠ (fst f) (snd f)

isContrAb⨁ₛ : (f : FinSetₐ ℓ ℓ') → isContr (Ab⨁ₛ f)
isContrAb⨁ₛ f = FinSetₐrec Ab⨁ₛ isPropAb⨁ₛ Ab⨁ᶠ f , isPropAb⨁ₛ f _

-- We rephrase the previous functions with only f as a parameter

module _ (f : FinSetₐ ℓ ℓ') where

  ⨁ₐ : AbGrp ℓ
  ⨁ₐ = isContrAb⨁ₛ f .fst .fst

  ⨁ₜ : Ab⨁ₛ f
  ⨁ₜ = isContrAb⨁ₛ f .fst

  πᵢ : (x : ⟨ fst f ⟩) → ⨁ₐ →ₐ snd f x
  πᵢ = πˢ f ⨁ₜ

  κᵢ : (x : ⟨ fst f ⟩) → snd f x →ₐ ⨁ₐ
  κᵢ = κˢ f ⨁ₜ

⟨⟩ᶠ : (A : AbGrp ℓ) → (f : FinSetₐ ℓ ℓ') → ((x : ⟨ fst f ⟩) → A →ₐ snd f x) → A →ₐ ⨁ₐ f
⟨⟩ᶠ A f g = ⟨⟩ˢ f A (⨁ₜ f) g

π⟨⟩ᵢ : (A : AbGrp ℓ) → (f : FinSetₐ ℓ ℓ') → (g : (x : ⟨ fst f ⟩) → A →ₐ snd f x) → (x : ⟨ fst f ⟩) →
  ∘ₐ A (⨁ₐ f) (snd f x) (⟨⟩ᶠ A f g) (πᵢ f x) ≡ g x
π⟨⟩ᵢ A f = ⟨⟩πs f A (⨁ₜ f)

∃!UPπf : (A : AbGrp ℓ) → (f : FinSetₐ ℓ ℓ') → (g : (x : ⟨ fst f ⟩) → A →ₐ snd f x) → (h : A →ₐ ⨁ₐ f) →
  ((x : ⟨ fst f ⟩) → ∘ₐ A (⨁ₐ f) (snd f x) h (πᵢ f x) ≡ g x) → h ≡ ⟨⟩ᶠ A f g
∃!UPπf A f = ∃!UPπs f A (⨁ₜ f)

∃!UPπfId : (f : FinSetₐ ℓ ℓ') → (g : ⨁ₐ f →ₐ ⨁ₐ f) →
  ((x : ⟨ fst f ⟩) → ∘ₐ (⨁ₐ f) (⨁ₐ f) (snd f x) g (πᵢ f x) ≡ πᵢ f x) → g ≡ idₐ (⨁ₐ f)
∃!UPπfId f = ∃!UPπsId f (⨁ₜ f)

⟨⟩⃖f : (A B : AbGrp ℓ) (f : FinSetₐ ℓ ℓ') → (g : A →ₐ B) → (h : (x : ⟨ fst f ⟩) → B →ₐ snd f x) →
  ∘ₐ A B (⨁ₐ f) g (⟨⟩ᶠ B f h) ≡ ⟨⟩ᶠ A f (λ x → ∘ₐ A B (snd f x) g (h x))
⟨⟩⃖f A B f = ⟨⟩⃖s f A B (⨁ₜ f)

[]ᶠ : (f : FinSetₐ ℓ ℓ') → (A : AbGrp ℓ) → ((x : ⟨ fst f ⟩) → snd f x →ₐ A) → ⨁ₐ f →ₐ A
[]ᶠ f A g = []ˢ f (⨁ₜ f) A g

κ[]ᵢ : (f : FinSetₐ ℓ ℓ') → (A : AbGrp ℓ) → (g : (x : ⟨ fst f ⟩) → snd f x →ₐ A) → (x : ⟨ fst f ⟩) →
  ∘ₐ (snd f x) (⨁ₐ f) A (κᵢ f x) ([]ᶠ f A g) ≡ g x
κ[]ᵢ f = []κs f (⨁ₜ f)

∃!UPκf : (f : FinSetₐ ℓ ℓ') (A : AbGrp ℓ) → (g : (x : ⟨ fst f ⟩) → snd f x →ₐ A) → (h : ⨁ₐ f →ₐ A) →
  ((x : ⟨ fst f ⟩) → ∘ₐ (snd f x) (⨁ₐ f) A (κᵢ f x) h ≡ g x) → h ≡ []ᶠ f A g
∃!UPκf f = ∃!UPκs f (⨁ₜ f)

∃!UPκfId : (f : FinSetₐ ℓ ℓ') (g : ⨁ₐ f →ₐ ⨁ₐ f) →
  ((x : ⟨ fst f ⟩) → ∘ₐ (snd f x) (⨁ₐ f) (⨁ₐ f) (κᵢ f x) g ≡ κᵢ f x) → g ≡ idₐ (⨁ₐ f)
∃!UPκfId f = ∃!UPκsId f (⨁ₜ f)

[]⃗f : (f : FinSetₐ ℓ ℓ') (A B : AbGrp ℓ) → (g : (x : ⟨ fst f ⟩) → snd f x →ₐ A) → (h : A →ₐ B) →
  ∘ₐ (⨁ₐ f) A B ([]ᶠ f A g) h ≡ []ᶠ f B (λ x → ∘ₐ (snd f x) A B (g x) h)
[]⃗f f = []⃗s f (⨁ₜ f)
