open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Induction
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to sumrec ; elim to sumelim)
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Foundations.Everything
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Functions.Embedding
open import Cubical.Functions.Involution
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Cubical.Relation.Nullary
open import Cubical.Structures.Pointed
open import Sign.TwoTorsors.Base
open import Sign.TwoTorsors.Sum
open import Sign.TwoTorsors.EquivTors

module Sign.TwoTorsors.FinSum where

private
  variable
    ℓ ℓ' : Level

Finₜ : ∀ ℓ ℓ' → FinSet ℓ' → Type (ℓ-max (ℓ-suc ℓ) ℓ')
Finₜ ℓ ℓ' (F , _) = F → TwoTorsor ℓ

module _ {ℓ : Level} {ℓ' : Level} (F : FinSet ℓ') (f : Finₜ ℓ ℓ' F) where

  elmtFam : Type (ℓ-max ℓ ℓ')
  elmtFam = (i : ⟨ F ⟩) → ⟨ f i ⟩

  replaceIndex : (i : ⟨ F ⟩) → (⟨ f i ⟩ → ⟨ f i ⟩) → elmtFam → elmtFam
  replaceIndex i g h j = decRec (J (λ y → λ p → ⟨ f y ⟩) (g (h i)))
    (λ _ → h j) (isFinSet→Discrete (F .snd) i j)

  linearFun : (X : TwoTorsor ℓ) → (elmtFam → ⟨ X ⟩) → Type (ℓ-max ℓ ℓ')
  linearFun X g = (xs : elmtFam) (b : Bool) → (i : ⟨ F ⟩) →
    (g (replaceIndex i (+ₜₐ (f i) b) xs) ≡ +ₜₐ X b (g xs))

  Σᵀ : Type (ℓ-max (lsuc ℓ) ℓ')
  Σᵀ = Σ[ X ∈ (Σ[ X ∈ TwoTorsor ℓ ] (elmtFam → ⟨ X ⟩))] (linearFun (fst X) (snd X))

  isProplin : (X : TwoTorsor ℓ) → (+ˣ : elmtFam → ⟨ X ⟩) → isProp (linearFun X +ˣ)
  isProplin X +ˣ = isPropΠ (λ xs → isPropΠ (λ b → isPropΠ (λ i → isSetTors X
    (+ˣ (replaceIndex i (+ₜₐ (f i) b) xs)) (+ₜₐ X b (+ˣ xs)))))

𝔽inₜ : ∀ ℓ ℓ' → (n : ℕ) → Type (ℓ-max (lsuc ℓ) ℓ')
𝔽inₜ ℓ ℓ' n = Finₜ ℓ ℓ' (𝔽in n)

replace𝔽in : ∀ {ℓ ℓ'} → (n : ℕ) → (f : 𝔽inₜ ℓ ℓ' n) → (i : ⟨ 𝔽in {ℓ = ℓ'} n ⟩) → (⟨ f i ⟩ → ⟨ f i ⟩) →
  ((i : ⟨ 𝔽in {ℓ = ℓ'} n ⟩) → ⟨ f i ⟩) → (j : ⟨ 𝔽in {ℓ = ℓ'} n ⟩) → ⟨ f j ⟩
replace𝔽in 0 f i = zrec (lower i)
replace𝔽in (suc n) f (inl tt*) g h (inl tt*) = g (h (inl tt*))
replace𝔽in (suc n) f (inl tt*) g h (inr j) = h (inr j)
replace𝔽in (suc n) f (inr i) g h (inl tt*) = h (inl tt*)
replace𝔽in (suc n) f (inr i) g h (inr j) = replace𝔽in n (f ∘ inr) i g (h ∘ inr) j

replace𝔽in≡Index : ∀ {ℓ ℓ'} → (n : ℕ) → (f : 𝔽inₜ ℓ ℓ' n) → (i : ⟨ 𝔽in {ℓ = ℓ'} n ⟩) →
  (g : ⟨ f i ⟩ → ⟨ f i ⟩) → (h : (i : ⟨ 𝔽in {ℓ = ℓ'} n ⟩) → ⟨ f i ⟩) → (j : ⟨ 𝔽in {ℓ = ℓ'} n ⟩) →
  replaceIndex (𝔽in {ℓ = ℓ'} n) f i g h j ≡ replace𝔽in n f i g h j
replace𝔽in≡Index 0 f i = zrec (lower i)
replace𝔽in≡Index (suc n) f (inl tt*) g h (inl tt*) = cong
  (λ a → decRec (J (λ y → λ p → ⟨ f y ⟩) (g (h (inl tt*)))) (λ _ → h (inl tt*)) a)
  (isPropDec (isFinSet→isSet (𝔽in (suc n) .snd) (inl tt*) (inl tt*))
    (isFinSet→Discrete (𝔽in (suc n) .snd) (inl tt*) (inl tt*)) (yes refl))
  ∙ JRefl (λ y → λ p → ⟨ f y ⟩) (g (h (inl tt*)))
replace𝔽in≡Index (suc n) f (inr i) g h (inl tt*) = cong
  (λ a → decRec (J (λ y → λ p → ⟨ f y ⟩) (g (h (inr i)))) (λ _ → h (inl tt*)) a)
  (isPropDec (isFinSet→isSet (𝔽in (suc n) .snd) (inr i) (inl tt*))
    (isFinSet→Discrete (𝔽in (suc n) .snd) (inr i) (inl tt*))
    (no (lower ∘ (⊎Path.encode (inr i) (inl tt*)))))
replace𝔽in≡Index (suc n) f (inl tt*) g h (inr j) = cong
  (λ a → decRec (J (λ y → λ p → ⟨ f y ⟩) (g (h (inl tt*)))) (λ _ → h (inr j)) a)
  (isPropDec (isFinSet→isSet (𝔽in (suc n) .snd) (inl tt*) (inr j))
    (isFinSet→Discrete (𝔽in (suc n) .snd) (inl tt*) (inr j))
    (no (lower ∘ (⊎Path.encode (inl tt*) (inr j)))))
replace𝔽in≡Index (suc n) f (inr i) g h (inr j) = decRec
  (λ p → cong (λ a → decRec (J (λ y → λ p → ⟨ f y ⟩) (g (h (inr i)))) (λ _ → h (inr j)) a)
    (isPropDec (isFinSet→isSet (𝔽in (suc n) .snd) (inr i) (inr j))
      (isFinSet→Discrete (𝔽in (suc n) .snd) (inr i) (inr j))
      (yes (cong inr p)))
    ∙ cong (λ a → decRec (J (λ y → λ p → ⟨ f (inr y) ⟩) (g (h (inr i)))) (λ _ → h (inr j)) a)
    (isPropDec (isFinSet→isSet (𝔽in n .snd) i j)
      (yes p)
      (isFinSet→Discrete (𝔽in n .snd) i j))
    ∙ replace𝔽in≡Index n (f ∘ inr) i g (h ∘ inr) j)
  (λ p → cong (λ a → decRec (J (λ y → λ p → ⟨ f y ⟩) (g (h (inr i)))) (λ _ → h (inr j)) a)
    (isPropDec (isFinSet→isSet (𝔽in (suc n) .snd) (inr i) (inr j))
      (isFinSet→Discrete (𝔽in (suc n) .snd) (inr i) (inr j))
      (no ((p $_) ∘ isEmbedding→Inj isEmbedding-inr i j)))
    ∙ cong (λ a → decRec (J (λ y → λ p → ⟨ f (inr y) ⟩) (g (h (inr i)))) (λ _ → h (inr j)) a)
    (isPropDec (isFinSet→isSet (𝔽in n .snd) i j)
      (no p)
      (isFinSet→Discrete (𝔽in n .snd) i j))
    ∙ replace𝔽in≡Index n (f ∘ inr) i g (h ∘ inr) j)
  (isFinSet→Discrete (𝔽in n .snd) i j)

isMerelyConst : ∀ {ℓ ℓ'} → (n : ℕ) → (f : 𝔽inₜ ℓ ℓ' n) → ∥ f ≡ (λ _ → ∙ₜ) ∥₁
isMerelyConst 0 f = ∣ isContr→isProp isContrΠ⊥* f (λ _ → ∙ₜ) ∣₁
isMerelyConst (suc n) f = proprec isPropPropTrunc (λ p → proprec isPropPropTrunc (λ q →
  ∣ funExt (sumelim (λ a → Σ≡Prop (λ _ → isPropPropTrunc) (ua (p ∙ₑ LiftEquiv)))
    (λ b → cong (_$ b) q)) ∣₁) (isMerelyConst n (f ∘ inr))) (f (inl tt*) .snd)

centerConst : ∀ {ℓ ℓ'} → (n : ℕ) → Σᵀ (𝔽in {ℓ = ℓ'} n) (λ _ → ∙ₜ {ℓ = ℓ})
centerConst n .fst .fst = ∙ₜ
centerConst 0 .fst .snd = λ _ → lift false
centerConst 0 .snd xs b i = zrec (lower i)
centerConst (suc n) .fst .snd f = lift
  (lower (centerConst n .fst .snd (f ∘ inr)) ⊕ lower (f (inl tt*)))
centerConst {ℓ = ℓ} {ℓ' = ℓ'} (suc n) .snd xs b = sumelim
  (λ a → cong₂ (λ α β → lift (lower (centerConst n .fst .snd α) ⊕ lower (β)))
    (funExt (λ x → replace𝔽in≡Index (suc n) (λ _ → ∙ₜ) (inl a) (+ₜₐ ∙ₜ b) xs (inr x)))
    (replace𝔽in≡Index (suc n) (λ _ → ∙ₜ) (inl a) (+ₜₐ ∙ₜ b) xs (inl tt*))
    ∙ cong (lift ∘ (lower (centerConst n .fst .snd (λ x → xs (inr x))) ⊕_) ∘ lower)
      (+∙ₜ {ℓ = ℓ} b (lower {i = lzero} (xs (inl tt*))))
    ∙ cong lift (⊕-assoc
      (lower (centerConst n .fst .snd (λ x → xs (inr x)))) b (lower (xs (inl tt*))))
    ∙ cong (λ α → lift (α ⊕ lower (xs (inl tt*)))) (⊕-comm
      (lower (centerConst n .fst .snd (λ x → xs (inr x)))) b)
    ∙ cong lift (sym (⊕-assoc
      b (lower (centerConst n .fst .snd (xs ∘ inr))) (lower (xs (inl tt*)))))
    ∙ sym (+∙ₜ b (lower (centerConst n .fst .snd (xs ∘ inr)) ⊕ (lower (xs (inl tt*))))))
  (λ a → cong₂ (λ α β → lift (lower (centerConst n .fst .snd α) ⊕ lower β))
    (funExt (λ x → replace𝔽in≡Index (suc n) (λ _ → ∙ₜ) (inr a) (+ₜₐ ∙ₜ b) xs (inr x)))
    (replace𝔽in≡Index (suc n) (λ _ → ∙ₜ) (inr a) (+ₜₐ ∙ₜ b) xs (inl tt*))
    ∙ cong (lift ∘ (_⊕ lower (xs (inl tt*))) ∘ lower ∘ (centerConst n .fst .snd))
      (funExt (λ x → sym (replace𝔽in≡Index n (λ _ → ∙ₜ) a (+ₜₐ ∙ₜ b) (xs ∘ inr) x)))
    ∙ cong (lift ∘ (_⊕ lower (xs (inl tt*))) ∘ lower) (centerConst n .snd (xs ∘ inr) b a)
    ∙ cong (lift {j = ℓ} ∘ (_⊕ lower (xs (inl tt*))) ∘ lower)
      (+∙ₜ {ℓ = ℓ} b (lower (centerConst n .fst .snd (xs ∘ inr))))
    ∙ cong lift (sym (⊕-assoc b (lower (centerConst n .fst .snd (xs ∘ inr))) (lower (xs (inl tt*)))))
    ∙ sym (+∙ₜ b (lower (centerConst n .fst .snd (λ x → xs (inr x))) ⊕ lower (xs (inl tt*)))))

pathToConst : ∀ {ℓ ℓ'} → (n : ℕ) → (((Z , +ᶻ) , islinZ) : Σᵀ (𝔽in {ℓ = ℓ'} n) (λ _ → ∙ₜ {ℓ = ℓ})) →
  Lift {j = ℓ} Bool ≃ ⟨ Z ⟩
pathToConst n ((Z , +ᶻ) , islinZ) .fst = (λ α → +ₜₐ Z α (+ᶻ (λ _ → lift false))) ∘ lower
pathToConst n ((Z , +ᶻ) , islinZ) .snd = (invEquiv LiftEquiv
  ∙ₑ ((λ b → +ₜₐ Z b (+ᶻ (λ _ → lift false))) , isTrans+ₜ Z (+ᶻ (λ _ → lift false)))) .snd

takeSubSum : ∀ {ℓ ℓ'} → (n : ℕ) → (Σᵀ (𝔽in {ℓ = ℓ'} (suc n)) (λ _ → ∙ₜ {ℓ = ℓ})) →
  Σᵀ (𝔽in {ℓ = ℓ'} n) (λ _ → ∙ₜ {ℓ = ℓ})
takeSubSum n ((Z , +ᶻ) , islinZ) .fst .fst = Z
takeSubSum n ((Z , +ᶻ) , islinZ) .fst .snd x = +ᶻ (sumrec (λ _ → lift false) x)
takeSubSum n ((Z , +ᶻ) , islinZ) .snd xs b i = cong +ᶻ (funExt (sumelim
  (λ a → sym (replace𝔽in≡Index (suc n) (λ _ → ∙ₜ) (inr i) (+ₜₐ ∙ₜ b)
    (sumrec (λ _ → lift false) xs) (inl a)))
  λ a → replace𝔽in≡Index n (λ _ → ∙ₜ) i (+ₜₐ ∙ₜ b) xs a ∙ refl
    ∙ sym (replace𝔽in≡Index (suc n) (λ _ → ∙ₜ) (inr i) (+ₜₐ ∙ₜ b)
      (sumrec (λ _ → lift false) xs) (inr a))))
  ∙ islinZ (sumrec (λ _ → lift false) xs) b (inr i)

contrConst2 : ∀ {ℓ ℓ'} → (n : ℕ) → (X : Σᵀ (𝔽in {ℓ = ℓ'} n) (λ _ → ∙ₜ {ℓ = ℓ})) → centerConst n ≡ X
contrConst2 n ((Z , +ᶻ), islinZ) = Σ≡Prop (λ x → isProplin (𝔽in n) (λ _ → ∙ₜ) (fst x) (snd x)) (ΣPathP
  (path , toPathP (fromPathP (funTypeTransp (λ _ → elmtFam (𝔽in n) (λ _ → ∙ₜ)) ⟨_⟩ path
    (centerConst n .fst .snd))
    ∙ cong (λ α → transport (ua (pathToConst n ((Z , +ᶻ) , islinZ))) ∘ centerConst n .fst .snd ∘ α)
      (funExt transportRefl)
    ∙ funExt (λ x →
      uaβ (pathToConst n ((Z , +ᶻ) , islinZ)) (centerConst n .fst .snd x)
      ∙ lemma n ((Z , +ᶻ) , islinZ) x))))
  where
  path : ∙ₜ ≡ Z
  path = Σ≡Prop (λ _ → isPropPropTrunc) (ua (pathToConst n ((Z , +ᶻ) , islinZ)))
  lemma : ∀ {ℓ ℓ'} (n : ℕ) → (((Z , +ᶻ), islinZ) : Σᵀ (𝔽in {ℓ = ℓ'} n) (λ _ → ∙ₜ {ℓ = ℓ})) →
    (x : elmtFam (𝔽in n) (λ _ → ∙ₜ)) →
    equivFun (pathToConst n ((Z , +ᶻ) , islinZ)) (centerConst n .fst .snd x) ≡ +ᶻ x
  lemma 0 ((Z , +ᶻ) , islinZ) x = cong ((_$ +ᶻ (λ _ → lift false)) ∘ fst) (+ₜ0 Z)
    ∙ cong +ᶻ (isContr→isProp isContrΠ⊥* (λ _ → lift false) x)
  lemma {ℓ} {ℓ'} (suc n) ((Z , +ᶻ) , islinZ) x =
    cong ((_$ (+ᶻ (λ _ → lift false))) ∘ fst)
      (sym (assoc+ₜ Z (lower (centerConst n .fst .snd (x ∘ inr))) (lower (x (inl tt*)))))
    ∙ cong (+ₜₐ Z (lower (x (inl tt*))) ∘ +ₜₐ Z (lower (centerConst n .fst .snd (x ∘ inr))) ∘ +ᶻ)
      (funExt (sumelim
        {C = λ a → (λ (_ : ⟨ 𝔽in {ℓ = ℓ'} (suc n) ⟩) → lift false) a
        ≡ sumrec (λ _ → lift false) (λ _ → lift false) a}
      (λ _ → refl) λ _ → refl))
    ∙ cong (+ₜₐ Z (lower (x (inl tt*)))) (lemma n (takeSubSum n ((Z , +ᶻ) , islinZ)) (x ∘ inr))
    ∙ sym (islinZ (sumrec (λ _ → lift false) (x ∘ inr)) (lower (x (inl tt*))) (inl tt*))
    ∙ cong +ᶻ (funExt
      (sumelim
        (λ a → replace𝔽in≡Index (suc n) (λ _ → ∙ₜ) (inl tt*) (+ₜₐ ∙ₜ (lower (x (inl tt*))))
          (sumrec (λ _ → lift false) (x ∘ inr)) (inl a) ∙ +∙ₜ (lower (x (inl tt*))) false
          ∙ cong lift (⊕-identityʳ (lower (x (inl tt*)))))
        (λ a → replace𝔽in≡Index (suc n) (λ _ → ∙ₜ) (inl tt*) (+ₜₐ ∙ₜ (lower (x (inl tt*))))
          (sumrec (λ _ → lift false) (x ∘ inr)) (inr a))))

isContrConst : ∀ {ℓ ℓ'} → (n : ℕ) → isContr (Σᵀ (𝔽in {ℓ = ℓ'} n) (λ _ → ∙ₜ {ℓ = ℓ}))
isContrConst n = centerConst n , contrConst2 n

isContrSum𝔽in : ∀ {ℓ ℓ'} → (n : ℕ) → (f : 𝔽inₜ ℓ ℓ' n) → isContr (Σᵀ (𝔽in {ℓ = ℓ'} n) f)
isContrSum𝔽in n f = proprec isPropIsContr (λ p → subst (isContr ∘ Σᵀ (𝔽in n)) (sym p)
  (isContrConst n)) (isMerelyConst n f)

isMerelyEq𝔽inₜ : ∀ {ℓ ℓ'} → (F : FinSet ℓ') → ∥ Finₜ ℓ ℓ' F ≃ 𝔽inₜ ℓ ℓ' (F .snd .fst) ∥₁
isMerelyEq𝔽inₜ (F , n , isFinF) = proprec isPropPropTrunc
  (λ p → ∣ equiv→ (p ∙ₑ invEquiv (𝔽in≃Fin n)) (idEquiv _) ∣₁) isFinF

isContrSum : ∀ {ℓ ℓ'} → (F : FinSet ℓ') → (f : Finₜ ℓ ℓ' F) → isContr (Σᵀ F f)
isContrSum {ℓ} {ℓ'} (F , n , isFinF) f = proprec isPropIsContr (λ p →
  subst (λ X → isContr (Σᵀ {ℓ = ℓ} {ℓ' = ℓ'} (fst X) (snd X))) (ΣPathP
    {x = 𝔽in {ℓ = ℓ'} n , f ∘ fst (𝔽in≃Fin n ∙ₑ invEquiv p)} {y = (F , n , isFinF) , f}
    (Σ≡Prop (λ x → isPropIsFinSet) (ua (𝔽in≃Fin n ∙ₑ invEquiv p)) ,
    symP ((funTypeTransp (idfun _) (λ _ → TwoTorsor ℓ)
      (sym (ua (𝔽in≃Fin n ∙ₑ invEquiv p))) f) ▷ (cong (_∘ (f ∘ transport (sym (sym
        (ua (𝔽in≃Fin n ∙ₑ invEquiv p)))))) (funExt transportRefl)
        ∙ cong (f ∘_) (sym (cong transport (symInvoP (sym (sym (ua (𝔽in≃Fin n ∙ₑ invEquiv p))))))
        ∙ funExt (uaβ (𝔽in≃Fin n ∙ₑ invEquiv p)))))))
  (isContrSum𝔽in n (f ∘ fst (𝔽in≃Fin n ∙ₑ invEquiv p)))) isFinF

Σ₂ᵀ : ∀ {ℓ ℓ'} → (F : FinSet ℓ') → (f : Finₜ ℓ ℓ' F) → TwoTorsor ℓ
Σ₂ᵀ F f = isContrSum F f .fst .fst .fst

replaceFin : ∀ {ℓ} → (n : ℕ) → (f : Finₜ ℓ lzero (Fin n , isFinSetFin)) → (i : Fin n) →
  (⟨ f i ⟩ → ⟨ f i ⟩) → ((i : Fin n) → ⟨ f i ⟩) → (j : Fin n) → ⟨ f j ⟩
replaceFin 0 f i = zrec i
replaceFin (suc n) f fzero g xs fzero = g (xs fzero)
replaceFin (suc n) f fzero g xs (fsuc j) = xs (fsuc j)
replaceFin (suc n) f (fsuc i) g xs fzero = xs fzero
replaceFin (suc n) f (fsuc i) g xs (fsuc j) = replaceFin n (f ∘ inr) i g (xs ∘ inr) j

replaceFin≡Index : ∀ {ℓ} → (n : ℕ) → (f : Finₜ ℓ lzero (Fin n , isFinSetFin)) → (i : Fin n) →
  (g : ⟨ f i ⟩ → ⟨ f i ⟩) → (xs : (i : Fin n) → ⟨ f i ⟩) → (j : Fin n) →
  replaceIndex (Fin n , isFinSetFin) f i g xs j ≡ replaceFin n f i g xs j
replaceFin≡Index 0 f i = zrec i
replaceFin≡Index (suc n) f fzero g xs fzero = cong
  (λ a → decRec (J (λ y → λ p → ⟨ f y ⟩) (g (xs fzero))) (λ _ → xs fzero) a)
  (isPropDec (isFinSet→isSet isFinSetFin fzero fzero)
    (isFinSet→Discrete isFinSetFin fzero fzero) (yes refl))
  ∙ JRefl (λ y → λ p → ⟨ f y ⟩) (g (xs fzero))
replaceFin≡Index (suc n) f (fsuc i) g xs fzero = cong
  (λ a → decRec (J (λ y → λ p → ⟨ f y ⟩) (g (xs (fsuc i)))) (λ _ → xs fzero) a)
  (isPropDec (isFinSet→isSet isFinSetFin (fsuc i) fzero)
    (isFinSet→Discrete isFinSetFin (fsuc i) fzero)
    (no (lower ∘ (⊎Path.encode (fsuc i) fzero))))
replaceFin≡Index (suc n) f fzero g xs (fsuc j) = cong
  (λ a → decRec (J (λ y → λ p → ⟨ f y ⟩) (g (xs fzero))) (λ _ → xs (fsuc j)) a)
  (isPropDec (isFinSet→isSet isFinSetFin fzero (fsuc j))
    (isFinSet→Discrete isFinSetFin fzero (fsuc j))
    (no (lower ∘ (⊎Path.encode fzero (fsuc j)))))
replaceFin≡Index (suc n) f (fsuc i) g xs (fsuc j) = decRec
  (λ p → cong (λ a → decRec (J (λ y → λ p → ⟨ f y ⟩) (g (xs (fsuc i)))) (λ _ → xs (fsuc j)) a)
    (isPropDec (isFinSet→isSet isFinSetFin (fsuc i) (fsuc j))
      (isFinSet→Discrete isFinSetFin (fsuc i) (fsuc j))
      (yes (cong fsuc p)))
    ∙ cong (λ a → decRec (J (λ y → λ p → ⟨ f (fsuc y) ⟩) (g (xs (fsuc i)))) (λ _ → xs (fsuc j)) a)
    (isPropDec (isFinSet→isSet isFinSetFin i j)
      (yes p)
      (isFinSet→Discrete isFinSetFin i j))
    ∙ replaceFin≡Index n (f ∘ inr) i g (xs ∘ inr) j)
  (λ p → cong (λ a → decRec (J (λ y → λ p → ⟨ f y ⟩) (g (xs (fsuc i)))) (λ _ → xs (fsuc j)) a)
    (isPropDec (isFinSet→isSet isFinSetFin (fsuc i) (fsuc j))
      (isFinSet→Discrete isFinSetFin (fsuc i) (fsuc j))
      (no ((p $_) ∘ isEmbedding→Inj isEmbedding-inr i j)))
    ∙ cong (λ a → decRec (J (λ y → λ p → ⟨ f (fsuc y) ⟩) (g (xs (fsuc i)))) (λ _ → xs (fsuc j)) a)
    (isPropDec (isFinSet→isSet isFinSetFin i j)
      (no p)
      (isFinSet→Discrete isFinSetFin i j))
    ∙ replaceFin≡Index n (f ∘ inr) i g (xs ∘ inr) j)
  (isFinSet→Discrete isFinSetFin i j)

module _ {ℓ : Level} (binFun : (X Y : TwoTorsor ℓ) → +²ᵀ X Y) where

  ΣFin : (n : ℕ) → (f : Finₜ ℓ lzero (Fin n , isFinSetFin)) → TwoTorsor ℓ
  ΣFin 0 f = ∙ₜ
  ΣFin (suc n) f = binFun (ΣFin n (f ∘ inr)) (f fzero) .fst .fst

  ΣFin→ : (n : ℕ) → (f : Finₜ ℓ lzero (Fin n , isFinSetFin)) →
    (xs : elmtFam (Fin n , isFinSetFin) f) → ⟨ ΣFin n f ⟩
  ΣFin→ 0 f xs = lift false
  ΣFin→ (suc n) f xs = binFun (ΣFin n (f ∘ inr)) (f fzero) .fst .snd
    (ΣFin→ n (f ∘ inr) (xs ∘ inr)) (xs fzero)

  linΣFin→ : (n : ℕ) → (f : Finₜ ℓ lzero (Fin n , isFinSetFin)) →
    (xs : elmtFam (Fin n , isFinSetFin) f) → (b : Bool) (i : Fin n) →
    ΣFin→ n f (replaceIndex (Fin n , isFinSetFin) f i (+ₜₐ (f i) b) xs)
    ≡ +ₜₐ (ΣFin n f) b (ΣFin→ n f xs)
  linΣFin→ 0 f xs b i = zrec i
  linΣFin→ (suc n) f xs b fzero = cong (ΣFin→ (suc n) f)
    (funExt (λ j → replaceFin≡Index (suc n) f fzero (+ₜₐ (f fzero) b) xs j))
    ∙ binFun (ΣFin n (f ∘ fsuc)) (f fzero) .snd (ΣFin→ n (f ∘ fsuc) (xs ∘ fsuc)) (xs fzero) b .snd
  linΣFin→ (suc n) f xs b (fsuc i) = cong (ΣFin→ (suc n) f)
    (funExt (λ j → replaceFin≡Index (suc n) f (fsuc i) (+ₜₐ (f (fsuc i)) b) xs j))
    ∙ cong (λ α → binFun (ΣFin n (f ∘ fsuc)) (f fzero) .fst .snd (ΣFin→ n (f ∘ fsuc) α) (xs fzero))
    (funExt (λ j → sym (replaceFin≡Index n (f ∘ fsuc) i (+ₜₐ (f (fsuc i)) b) (xs ∘ fsuc) j)))
    ∙ cong (λ α → binFun (ΣFin n (f ∘ fsuc)) (f fzero) .fst .snd α (xs fzero))
    (linΣFin→ n (f ∘ fsuc) (xs ∘ fsuc) b i)
    ∙ binFun (ΣFin n (f ∘ fsuc)) (f fzero) .snd (ΣFin→ n (f ∘ fsuc) (xs ∘ fsuc)) (xs fzero) b .fst

  ΣFinₜ : (n : ℕ) → (f : Finₜ ℓ lzero (Fin n , isFinSetFin)) → Σᵀ (Fin n , isFinSetFin) f
  ΣFinₜ n f = (ΣFin n f , ΣFin→ n f) , linΣFin→ n f

module _ {ℓ : Level} {ℓ' : Level} (F : Type ℓ') (n : ℕ) (e : Fin n → F) (e≃ : isEquiv e)
  (f : F → TwoTorsor ℓ)
  (takeΣ : Σᵀ (Fin n , isFinSetFin) (f ∘ e))where

  ΣFinSet : TwoTorsor ℓ
  ΣFinSet = takeΣ .fst .fst

  ΣFinSet→ : ((i : F) → ⟨ f i ⟩) → ⟨ ΣFinSet ⟩
  ΣFinSet→ xs = takeΣ .fst .snd (xs ∘ e)

  linΣFinSet→ : (p : ∥ F ≃ Fin n ∥₁) → (xs : (i : F) → ⟨ f i ⟩) → (b : Bool) (i : F) →
    ΣFinSet→ (replaceIndex (F , n , p) f i (+ₜₐ (f i) b) xs) ≡ +ₜₐ ΣFinSet b (ΣFinSet→ xs)
  linΣFinSet→ p xs b i = cong (λ a → ΣFinSet→ (replaceIndex (F , n , p) f a
    (+ₜₐ (f a) b) xs)) (sym (e≃ .equiv-proof i .fst .snd))
    ∙ cong (takeΣ .fst .snd) (lemma e (isEquiv→isEmbedding e≃) (e≃ .equiv-proof i .fst .fst)
      (λ i → +ₜₐ (f i) b) xs)
    ∙ takeΣ .snd (xs ∘ e) b (e≃ .equiv-proof i .fst .fst)
    where
    lemma : (g : Fin n → F) → (isEmbedding g)→ (i : Fin n) → (h : (i : F) → ⟨ f i ⟩ → ⟨ f i ⟩) →
      (xs : (i : F) → ⟨ f i ⟩) →
      replaceIndex (F , n , p) f (g i) (h (g i)) xs ∘ g
      ≡ replaceIndex (Fin n , isFinSetFin) (f ∘ g) i (h (g i)) (xs ∘ g)
    lemma g ge i h xs = funExt (λ j → decRec
      (λ q → cong (decRec (J (λ y p → ⟨ f y ⟩) (h (g i) (xs (g i)))) (λ _ → xs (g j)))
        (isPropDec (isFinSet→isSet (n , p) (g i) (g j)) (isFinSet→Discrete (n , p) (g i) (g j))
        (yes (cong g q)))
        ∙ cong (decRec (J (λ y p → ⟨ f (g y) ⟩) (h (g i) (xs (g i)))) (λ _ → xs (g j)))
        (isPropDec (isFinSet→isSet isFinSetFin i j) (yes q) (isFinSet→Discrete isFinSetFin i j)))
      (λ q → cong (decRec (J (λ y p → ⟨ f y ⟩) (h (g i) (xs (g i)))) (λ _ → xs (g j)))
        (isPropDec (isFinSet→isSet (n , p) (g i) (g j)) (isFinSet→Discrete (n , p) (g i) (g j))
        (no ((q $_) ∘ isEmbedding→Inj ge i j)))
        ∙ cong (decRec (J (λ y p → ⟨ f (g y) ⟩) (h (g i) (xs (g i)))) (λ _ → xs (g j)))
        (isPropDec (isFinSet→isSet isFinSetFin i j) (no q) (isFinSet→Discrete isFinSetFin i j)))
      (isFinSet→Discrete isFinSetFin i j))

  ΣFinSetₜ : (p : ∥ F ≃ Fin n ∥₁) → Σᵀ (F , n , p) f
  ΣFinSetₜ p = (ΣFinSet , ΣFinSet→) , linΣFinSet→ p

module _ {ℓ ℓ' : Level} (binFun : (X Y : TwoTorsor ℓ) → +²ᵀ X Y) where

  Σᵀᶠ : (F : FinSet ℓ') → (f : Finₜ ℓ ℓ' F) → Σᵀ F f
  Σᵀᶠ (F , n , isFinF) f = proprec (isContr→isProp (isContrSum (F , n , isFinF) f))
    (λ p → ΣFinSetₜ {ℓ = ℓ} {ℓ' = ℓ'} F n (invEquiv p .fst) (invEquiv p .snd) f
      (ΣFinₜ {ℓ = ℓ} binFun n (f ∘ (invEquiv p .fst))) isFinF)
    isFinF

Σᵀᶠ≃ : ∀ {ℓ ℓ'} → (F : FinSet ℓ') → (f : Finₜ ℓ ℓ' F) → TwoTorsor ℓ
Σᵀᶠ≃ F f = Σᵀᶠ is+²ᵀ≃ₜ F f .fst .fst
