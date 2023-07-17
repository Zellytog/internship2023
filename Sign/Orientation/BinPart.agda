{-# OPTIONS --allow-unsolved-metas #-}
open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool renaming (isProp≤ to isProp≤Bool)
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Induction
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to sumrec ; elim to sumelim)
open import Cubical.Data.SumFin renaming (Fin to ℱin)
open import Cubical.Data.Fin
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order renaming (_≟_ to _≟ₙ_)
open import Cubical.Data.Unit
open import Cubical.Foundations.Everything
open import Cubical.Functions.Embedding
open import Cubical.Functions.Involution
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Cubical.Relation.Nullary
open import Sign.TwoTorsors
open import Sign.Orientation.FinPart

module Sign.Orientation.BinPart where

infixr 30 _≐_

private
  variable
    ℓ : Level

ℙᵈ₂ : ℕ → Type₀
ℙᵈ₂ n = Σ[ x ∈ Fin n ] (Fin (fst x))

_≐_ : ℕ → ℕ → Bool
0 ≐ 0 = true
0 ≐ (suc n) = false
(suc n) ≐ 0 = false
(suc n) ≐ (suc m) = n ≐ m

dis∨ : (b₀ b₁ : Bool) → b₀ or b₁ ≡ true → (b₀ ≡ true) ⊎ (b₁ ≡ true)
dis∨ false false e = zrec (false≢true e)
dis∨ false true e = inr refl
dis∨ true b e = inl refl

=→≐ : (m : ℕ) → m ≐ m ≡ true
=→≐ 0 = refl
=→≐ (suc n) = =→≐ n

≐→= : (n m : ℕ) → n ≐ m ≡ true → n ≡ m
≐→= 0 0 e = refl
≐→= 0 (suc m) e = zrec (false≢true e)
≐→= (suc n) 0 e = zrec (false≢true e)
≐→= (suc n) (suc m) e = cong suc (≐→= n m e)

module _ (n : ℕ) (((m , e) , k , e') : ℙᵈ₂ n) where

  disℙᵈ₂ : ∀ p → isProp ((m ≐ p ≡ true) ⊎ (k ≐ p ≡ true))
  disℙᵈ₂ p (inl r) (inl s) = cong inl (isSetBool (m ≐ p) true r s)
  disℙᵈ₂ p (inl r) (inr s) = zrec (¬m<m (subst (λ a → k < a) (≐→= m p r ∙ sym (≐→= k p s)) e'))
  disℙᵈ₂ p (inr r) (inl s) = zrec (¬m<m (subst (λ a → a < m) (≐→= k p r ∙ sym (≐→= m p s)) e'))
  disℙᵈ₂ p (inr r) (inr s) = cong inr (isSetBool (k ≐ p) true r s)

  ℙᵈ₂→ℙᵈ : ℙᵈ (Fin n)
  ℙᵈ₂→ℙᵈ (q , e'') = (m ≐ q) or (k ≐ q)
  
  ℙᵈ₂→isℙᵈᵢ : fiber ℙᵈ₂→ℙᵈ true → ℱin 2
  ℙᵈ₂→isℙᵈᵢ ((p , e'') , f) = sumrec (λ _ → inl tt) (λ _ → inr $ inl tt) (dis∨ (m ≐ p) (k ≐ p) f)

  ℙᵈ₂→inv : ℱin 2 → fiber ℙᵈ₂→ℙᵈ true
  ℙᵈ₂→inv (inl tt) = (m , e) , cong (λ a → a or (k ≐ m)) (=→≐ m)
  ℙᵈ₂→inv (inr (inl tt)) = (k , <-trans e' e) , cong (λ a → (m ≐ k) or a) (=→≐ k) ∙ or-zeroʳ (m ≐ k)

  invLeftℙᵈ₂ : ∀ x → ℙᵈ₂→isℙᵈᵢ (ℙᵈ₂→inv x) ≡ x
  invLeftℙᵈ₂ (inl tt) = cong (sumrec (λ _ → inl tt) (λ _ → inr $ inl tt))
    (disℙᵈ₂ m (dis∨ (m ≐ m) (k ≐ m) (snd (ℙᵈ₂→inv (inl tt)))) (inl (=→≐ m)))
  invLeftℙᵈ₂ (inr (inl tt)) = cong (sumrec (λ _ → inl tt) (λ _ → inr $ inl tt))
    (disℙᵈ₂ k (dis∨ (m ≐ k) (k ≐ k) (snd (ℙᵈ₂→inv (inr (inl tt))))) (inr (=→≐ k)))

  invRightℙᵈ₂ : ∀ x → ℙᵈ₂→inv (ℙᵈ₂→isℙᵈᵢ x) ≡ x
  invRightℙᵈ₂ ((p , e'') , f) = Σ≡Prop (λ x₁ → isSetBool (ℙᵈ₂→ℙᵈ x₁) true) (Σ≡Prop (λ x → isProp≤)
    (sumrec
      (λ r → cong (fst ∘ fst ∘ ℙᵈ₂→inv ∘ sumrec (λ _ → inl tt) (λ _ → inr $ inl tt))
        (disℙᵈ₂ p (dis∨ (m ≐ p) (k ≐ p) f) (inl r)) ∙ ≐→= m p r)
      (λ r → cong (fst ∘ fst ∘ ℙᵈ₂→inv ∘ sumrec (λ _ → inl tt) (λ _ → inr $ inl tt))
        (disℙᵈ₂ p (dis∨ (m ≐ p) (k ≐ p) f) (inr r)) ∙ ≐→= k p r)
    (dis∨ (m ≐ p) (k ≐ p) f)))

  isℙᵈᵢℙᵈ₂ : fiber ℙᵈ₂→ℙᵈ true ≃ ℱin 2
  isℙᵈᵢℙᵈ₂ = isoToEquiv (record {
    fun = ℙᵈ₂→isℙᵈᵢ ;
    inv = ℙᵈ₂→inv ;
    leftInv = invRightℙᵈ₂ ;
    rightInv = invLeftℙᵈ₂ })

  ℙᵈ₂→ℙᵈᵢ : ℙᵈᵢ 2 (Fin n)
  ℙᵈ₂→ℙᵈᵢ = ℙᵈ₂→ℙᵈ , ∣ isℙᵈᵢℙᵈ₂ ∣₁

module _ (n : ℕ) ((P , bl) : ℙᵈᵢ 2 (Fin n)) where

  Part2 : Type lzero
  Part2 = Σ[ f ∈ (ℱin 2 ≃ fiber P true)] f .fst (inl tt) .fst .fst < f .fst (inr $ inl tt) .fst .fst

  invFin2→ : ℱin 2 → ℱin 2
  invFin2→ (inl tt) = inr (inl tt)
  invFin2→ (inr (inl tt)) = inl tt
  
  invFin2invol : isInvolution invFin2→
  invFin2invol (inl tt) = refl
  invFin2invol (inr (inl tt)) = refl
  
  invFin2 : ℱin 2 ≃ ℱin 2
  invFin2 = invFin2→ , involIsEquiv invFin2invol

  invFin2isFlip : invFin2→ ≡ flipTors (ℱin 2 , ∣ SumFin2≃Bool ∣₁)
  invFin2isFlip i (inl tt) = inr (inl tt)
  invFin2isFlip i (inr (inl tt)) = inl tt

  invifnec : ((e , e≃) : ℱin 2 ≃ fiber P true) →
    Trichotomy ((e (inl tt)) .fst .fst) ((e (inr (inl tt))) .fst .fst) →
    Σ[ f ∈ (ℱin 2 ≃ fiber P true)] (f .fst (inl tt) .fst .fst < f .fst (inr $ inl tt) .fst .fst)
  invifnec (e , e≃) (lt p₃) = (e , e≃) , p₃
  invifnec (e , e≃) (eq p₃) = zrec (lower (⊎Path.encode (inl tt) (inr (inl tt))
    (isEmbedding→Inj (isEquiv→isEmbedding e≃) (inl tt) (inr (inl tt))
       (Σ≡Prop (λ x → isSetBool (P x) true) (Σ≡Prop (λ n → isProp≤) p₃)))))
  invifnec (e , e≃) (gt p₃) = invFin2 ∙ₑ (e , e≃) , p₃

  isPropPart2 : isProp Part2
  isPropPart2 ((e , e≃) , e≡) ((f , f≃) , f≡) = sumrec
    (λ p → Σ≡Prop (λ x → isProp≤) p)
    (λ p → zrec (¬m<m (<-trans
      (subst (f (inr (inl tt)) .fst .fst <_)
      (cong (fst ∘ fst) (cong (λ α → e (α (inl tt))) invFin2isFlip
      ∙ ≃comFlip (ℱin 2 , ∣ SumFin2≃Bool ∣₁)
      (fiber P true , ∣ invEquiv (e , e≃) ∙ₑ SumFin2≃Bool ∣₁) (e , e≃) (inl tt)
      ∙ cong (flipTors (fiber P true , ∣ invEquiv (e , e≃) ∙ₑ SumFin2≃Bool ∣₁))
      (cong ((_$ inl tt) ∘ fst) p
      ∙ sym (cong ((_$ inl tt) ∘ fst) (flipOn≃ (ℱin 2 , ∣ SumFin2≃Bool ∣₁)
      (fiber P true , ∣ invEquiv (e , e≃) ∙ₑ SumFin2≃Bool ∣₁) (f , f≃)))
      ∙ cong (λ α → f (α (inl tt))) (sym invFin2isFlip))
      ∙ sym (≃comFlip (ℱin 2 , ∣ SumFin2≃Bool ∣₁)
      (fiber P true , ∣ invEquiv (e , e≃) ∙ₑ SumFin2≃Bool ∣₁) (f , f≃) (inr (inl tt)))
      ∙ cong (λ α → f (α (inr (inl tt)))) (sym invFin2isFlip)))
      (subst (_< e (inr (inl tt)) .fst .fst) (cong (fst ∘ fst) (cong ((_$ inl tt) ∘ fst) p
      ∙ sym (cong ((_$ inl tt) ∘ fst) (flipOn≃ (ℱin 2 , ∣ SumFin2≃Bool ∣₁)
      (fiber P true , ∣ invEquiv (e , e≃) ∙ₑ SumFin2≃Bool ∣₁) (f , f≃)))
      ∙ cong (λ α → f (α (inl tt))) (sym invFin2isFlip))) e≡)) f≡)))
    (dichotomyTors
      ((ℱin 2 , ∣ SumFin2≃Bool ∣₁) ≃ₜ (fiber P true , ∣ invEquiv (e , e≃) ∙ₑ SumFin2≃Bool ∣₁))
      (e , e≃) (f , f≃))

  takePart2 : Part2
  takePart2 = proprec isPropPart2 (λ p → invifnec (invEquiv p)
    (invEquiv p .fst (inl tt) .fst .fst ≟ₙ invEquiv p .fst (inr (inl tt)) .fst .fst)) bl

  ℙᵈᵢ→ℙᵈ₂ : ℙᵈ₂ n
  ℙᵈᵢ→ℙᵈ₂ = (takePart2 .fst .fst (inr $ inl tt) .fst .fst ,
    takePart2 .fst .fst (inr $ inl tt) .fst .snd) ,
    takePart2 .fst .fst (inl tt) .fst .fst , takePart2 .snd

ℙᵈ₂→Part2→ : (n : ℕ) → (P : ℙᵈ₂ n) → ℱin 2 → fiber (ℙᵈ₂→ℙᵈᵢ n P .fst) true
ℙᵈ₂→Part2→ n ((m₁ , p₁) , m₂ , p₂) (inl tt) = (m₂ , <-trans p₂ p₁) ,
  cong (λ a → (m₁ ≐ m₂) or a) (=→≐ m₂) ∙ or-zeroʳ (m₁ ≐ m₂)
ℙᵈ₂→Part2→ n ((m₁ , p₁) , m₂ , p₂) (inr (inl tt)) = (m₁ , p₁) ,
  cong (λ a → a or (m₂ ≐ m₁)) (=→≐ m₁)

ℙᵈ₂→Part2← : (n : ℕ) → (P : ℙᵈ₂ n) → fiber (ℙᵈ₂→ℙᵈᵢ n P .fst) true → ℱin 2
ℙᵈ₂→Part2← n ((m₁ , p₁) , m₂ , p₂) ((p , e) , f) =
  sumrec (λ _ → inr (inl tt)) (λ _ → inl tt) (dis∨ (m₁ ≐ p) (m₂ ≐ p) f)

ℙᵈ₂→Part2←→ : (n : ℕ) → (P : ℙᵈ₂ n) → ∀ x → ℙᵈ₂→Part2→ n P (ℙᵈ₂→Part2← n P x) ≡ x
ℙᵈ₂→Part2←→ n ((m₁ , p₁) , m₂ , p₂) ((m₃ , p₃) , p) = 
  Σ≡Prop (λ x₁ → isSetBool (ℙᵈ₂→ℙᵈᵢ n ((m₁ , p₁) , m₂ , p₂) .fst x₁) true)
  (Σ≡Prop (λ x → isProp≤)
    (sumrec
      (λ r → cong (fst ∘ fst ∘ ℙᵈ₂→Part2→ n ((m₁ , p₁) , m₂ , p₂)
        ∘ sumrec (λ _ → inr (inl tt)) (λ _ → inl tt))
        (disℙᵈ₂ n ((m₁ , p₁) , m₂ , p₂)
        m₃ (dis∨ (m₁ ≐ m₃) (m₂ ≐ m₃) p) (inl r)) ∙ ≐→= m₁ m₃ r)
      (λ r → cong (fst ∘ fst ∘ ℙᵈ₂→Part2→ n ((m₁ , p₁) , m₂ , p₂)
        ∘ sumrec (λ _ → inr (inl tt)) (λ _ → inl tt))
        (disℙᵈ₂ n ((m₁ , p₁) , m₂ , p₂)
        m₃ (dis∨ (m₁ ≐ m₃) (m₂ ≐ m₃) p) (inr r)) ∙ ≐→= m₂ m₃ r)
    (dis∨ (m₁ ≐ m₃) (m₂ ≐ m₃) p)))

ℙᵈ₂→Part2→← : (n : ℕ) → (P : ℙᵈ₂ n) → ∀ x → ℙᵈ₂→Part2← n P (ℙᵈ₂→Part2→ n P x) ≡ x
ℙᵈ₂→Part2→← n ((m₁ , p₁) , m₂ , p₂) (inl tt) = cong
  (sumrec (λ _ → inr (inl tt)) (λ _ → inl tt))
  (disℙᵈ₂ n ((m₁ , p₁) , m₂ , p₂) m₂ (dis∨ (m₁ ≐ m₂) (m₂ ≐ m₂)
  (ℙᵈ₂→Part2→ n ((m₁ , p₁) , m₂ , p₂) (inl tt) .snd)) (inr (=→≐ m₂)))
ℙᵈ₂→Part2→← n ((m₁ , p₁) , m₂ , p₂) (inr (inl tt)) = cong
  (sumrec (λ _ → inr (inl tt)) (λ _ → inl tt))
  (disℙᵈ₂ n ((m₁ , p₁) , m₂ , p₂) m₁ (dis∨ (m₁ ≐ m₁) (m₂ ≐ m₁)
  (ℙᵈ₂→Part2→ n ((m₁ , p₁) , m₂ , p₂) (inr (inl tt)) .snd)) (inl (=→≐ m₁)))

ℙᵈ₂→Part2 : (n : ℕ) → (P : ℙᵈ₂ n) → Part2 n (ℙᵈ₂→ℙᵈᵢ n P)
ℙᵈ₂→Part2 n P .fst = isoToEquiv (record {
  fun = ℙᵈ₂→Part2→ n P ;
  inv = ℙᵈ₂→Part2← n P ;
  leftInv = ℙᵈ₂→Part2→← n P ;
  rightInv = ℙᵈ₂→Part2←→ n P })
ℙᵈ₂→Part2 n ((m₁ , p₁) , m₂ , p₂) .snd = p₂

isoℙᵈᵢℙᵈ₂ : (n : ℕ) → Iso (ℙᵈᵢ 2 (Fin n)) (ℙᵈ₂ n)
isoℙᵈᵢℙᵈ₂ n .Iso.fun = ℙᵈᵢ→ℙᵈ₂ n
isoℙᵈᵢℙᵈ₂ n .Iso.inv = ℙᵈ₂→ℙᵈᵢ n
isoℙᵈᵢℙᵈ₂ n .Iso.leftInv (P , bl) = Σ≡Prop (λ _ → isPropPropTrunc)
  (funExt (λ a → sumrec
    (λ p → {!!} ∙ sym p)
    (λ p → {!!} ∙ sym p)
  (dichotomyBool (P a))))
isoℙᵈᵢℙᵈ₂ n .Iso.rightInv ((m₁ , p₁) , m₂ , p₂) = congS
  (λ α → (α .fst .fst (inr (inl tt)) .fst .fst , α .fst .fst (inr (inl tt)) .fst .snd),
  α .fst .fst (inl tt) .fst .fst , α .snd) equa1
  where
  equa1 : takePart2 n (ℙᵈ₂→ℙᵈᵢ n ((m₁ , p₁) , m₂ , p₂)) ≡ ℙᵈ₂→Part2 n ((m₁ , p₁) , m₂ , p₂)
  equa1 = isPropPart2 n (ℙᵈ₂→ℙᵈᵢ n ((m₁ , p₁) , m₂ , p₂))
    (takePart2 n (ℙᵈ₂→ℙᵈᵢ n ((m₁ , p₁) , m₂ , p₂))) (ℙᵈ₂→Part2 n ((m₁ , p₁) , m₂ , p₂))

ℙᵈᵢ≃ℙᵈ₂ : (n : ℕ) → ℙᵈᵢ 2 (Fin n) ≃ ℙᵈ₂ n
ℙᵈᵢ≃ℙᵈ₂ n = isoToEquiv (isoℙᵈᵢℙᵈ₂ n)

Fin→ℱin : (n : ℕ) → Fin n → ℱin n
Fin→ℱin 0 (n , p) = zrec (¬-<-zero p)
Fin→ℱin (suc n) (0 , p) = inl tt
Fin→ℱin (suc n) (suc m , p) = inr (Fin→ℱin n (m , pred-≤-pred p))

ℱin→Fin : (n : ℕ) → ℱin n → Fin n
ℱin→Fin 0 x = zrec x
ℱin→Fin (suc n) (inl tt) = Cubical.Data.Fin.fzero
ℱin→Fin (suc n) (inr x) = Cubical.Data.Fin.fsuc (ℱin→Fin n x)

Fin→ℱin→Fin : (n : ℕ) → ∀ x → ℱin→Fin n (Fin→ℱin n x) ≡ x
Fin→ℱin→Fin 0 (n , p) = zrec (¬-<-zero p)
Fin→ℱin→Fin (suc n) (0 , p) = Σ≡Prop (λ _ → isProp≤) refl
Fin→ℱin→Fin (suc n) (suc m , p) = Σ≡Prop (λ _ → isProp≤)
  (cong (suc ∘ fst) (Fin→ℱin→Fin n (m , pred-≤-pred p)))

ℱin→Fin→ℱin : (n : ℕ) → ∀ x → Fin→ℱin n (ℱin→Fin n x) ≡ x
ℱin→Fin→ℱin 0 x = zrec x
ℱin→Fin→ℱin (suc n) (inl tt) = refl
ℱin→Fin→ℱin (suc n) (inr x) = cong inr (cong (Fin→ℱin n) (Σ≡Prop (λ _ → isProp≤) refl)
  ∙ (ℱin→Fin→ℱin n x))

Fin≃ℱin : (n : ℕ) → Fin n ≃ ℱin n
Fin≃ℱin n = isoToEquiv (record {
  fun = Fin→ℱin n ;
  inv = ℱin→Fin n ;
  leftInv = Fin→ℱin→Fin n ;
  rightInv = ℱin→Fin→ℱin n})

isFinOrdℙᵈ₂ : (n : ℕ) → isFinOrd (ℙᵈ₂ n)
isFinOrdℙᵈ₂ n = isFinOrdΣ (Fin n) (n , Fin≃ℱin n) (λ x → Fin (x .fst))
  (λ x → fst x , Fin≃ℱin (x .fst))

isFinOrdℙᵈᵢ₂ : (n : ℕ) → isFinOrd (ℙᵈᵢ 2 (Fin n))
isFinOrdℙᵈᵢ₂ n = finord2 .fst , ℙᵈᵢ≃ℙᵈ₂ n ∙ₑ finord2 .snd
  where
  finord2 = isFinOrdℙᵈ₂ n

isFinℙᵈ₂ : ∀ {ℓ} → (X : FinSet ℓ) → isFinSet (ℙᵈᵢ 2 ⟨ X ⟩)
isFinℙᵈ₂ (X , n , isFinX) = finord2 .fst , proprec isPropPropTrunc
  (λ e → ∣ invEquiv (ℙᵈᵢ≃ X (Fin n) 2 (e ∙ₑ invEquiv (Fin≃ℱin n))) ∙ₑ finord2 .snd ∣₁) isFinX
  where
  finord2 = isFinOrdℙᵈᵢ₂ n

{-
test : Fin 3 → Bool
test (0 , _) = true
test (1 , _) = true
test (2 , _) = false
test (suc (suc (suc n)) , p) = zrec (¬-<-zero (<-k+-cancel {k = 3} p))

test→ : ℱin 2 → fiber test true
test→ (inl tt) = 0 , refl
test→ (inr (inl tt)) = 1 , refl

test← : fiber test true → ℱin 2
test← ((0 , _) , _) = inl tt
test← ((1 , _) , _) = inr (inl tt)
test← ((2 , _) , p) = zrec (false≢true p)
test← ((suc (suc (suc n)) , p) , _) = zrec (¬-<-zero (<-k+-cancel {k = 3} p))

test←→ : ∀ x → test← (test→ x) ≡ x
test←→ (inl tt) = refl
test←→ (inr (inl tt)) = refl

test→← : ∀ x → test→ (test← x) ≡ x
test→← ((0 , _) , _) = Σ≡Prop (λ x → isSetBool (test x) true) (Σ≡Prop (λ _ → isProp≤) refl)
test→← ((1 , _) , _) = Σ≡Prop (λ x → isSetBool (test x) true) (Σ≡Prop (λ _ → isProp≤) refl)
test→← ((2 , _) , p) = zrec (false≢true p)
test→← ((suc (suc (suc n)) , p), _ ) = zrec (¬-<-zero (<-k+-cancel {k = 3} p))

testℙᵈ₂ : ℙᵈᵢ 2 (Fin 3)
testℙᵈ₂ = test , ∣ isoToEquiv (record {fun = test← ; inv = test→ ; leftInv = test→← ;
  rightInv = test←→ }) ∣₁
  -}
