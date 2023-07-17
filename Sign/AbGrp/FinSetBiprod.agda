open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.Relation.Nullary
open import Sign.AbGrp.Base

-- We construct the structure of finite biproduct, i.e. biproduct indexed by a finite set
-- and prove that this type is a proposition, along with the usual functions regarding its
-- product and coproduct structure

module Sign.AbGrp.FinSetBiprod where

private
  variable
    ℓ ℓ' : Level

-- A finite family of abelian groups is a function from FinSet ℓ to AbGrp ℓ

FinSetₐ : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
FinSetₐ ℓ ℓ' = Σ[ X ∈ FinSet ℓ' ] (⟨ X ⟩ → AbGrp ℓ)

-- The definition of Ab× and Ab+ are adapted to finite family, same with Ab⊕

FinSetPre× : ∀ {ℓ ℓ'} → FinSetₐ ℓ ℓ' → Type (ℓ-max (lsuc ℓ) ℓ')
FinSetPre× {ℓ = ℓ} f = Σ[ Z ∈ AbGrp ℓ ] ((x : ⟨ fst f ⟩) → Z →ₐ (snd f x))

FinSetPre+ : ∀ {ℓ ℓ'} → FinSetₐ ℓ ℓ' → Type (ℓ-max (lsuc ℓ) ℓ')
FinSetPre+ {ℓ = ℓ} f = Σ[ Z ∈ AbGrp ℓ ] ((x : ⟨ fst f ⟩) → (snd f x) →ₐ Z)

module _ (f : FinSetₐ ℓ ℓ') where

  -- δFinₛ is a function which represent 0₀ x y if x ≢ y and 1ₐ x if x ≢ y

  δFinₛ : (a b : ⟨ fst f ⟩) → snd f a →ₐ snd f b
  δFinₛ a b = decRec (J (λ b → λ p → snd f a →ₐ snd f b) (idₐ (snd f a)))
    (λ _ → 0ₐ (snd f a) (snd f b)) (isFinSet→Discrete (f .fst .snd) a b)

  distrib×s : (Z : FinSetPre× f) → (A : AbGrp ℓ) →
    (A →ₐ (fst Z)) → (x : ⟨ fst f ⟩) → A →ₐ (snd f x)
  distrib×s Z A p x = ∘ₐ A (Z .fst) (snd f x) p (Z .snd x)

  distrib+s : (Z : FinSetPre+ f) → (A : AbGrp ℓ) →
    ((fst Z) →ₐ A) → (x : ⟨ fst f ⟩) → (snd f x) →ₐ A
  distrib+s Z A p x = ∘ₐ (snd f x) (Z .fst) A (Z .snd x) p
  
  u×s : FinSetPre× f → Type (ℓ-max (lsuc ℓ) ℓ')
  u×s Z = (A : AbGrp ℓ) → isEquiv (distrib×s Z A)

  u+s : FinSetPre+ f → Type (ℓ-max (lsuc ℓ) ℓ')
  u+s Z = (A : AbGrp ℓ) → isEquiv (distrib+s Z A)

  uπκs : AbGrp ℓ → Type (ℓ-max (lsuc ℓ) ℓ')
  uπκs Z = (Σ[ p ∈ ((x : ⟨ fst f ⟩) → (snd f x) →ₐ Z) ]
               (u+s (Z , p)))
         × (Σ[ p ∈ ((x : ⟨ fst f ⟩) → Z →ₐ (snd f x)) ]
               (u×s (Z , p)))

  Ab×s : Type (ℓ-max (lsuc ℓ) ℓ')
  Ab×s = Σ[ Z ∈ (FinSetPre× f) ] (u×s Z)

  Ab+s : Type (ℓ-max (lsuc ℓ) ℓ')
  Ab+s = Σ[ Z ∈ (FinSetPre+ f) ] (u+s Z)

  ⟨⟩ₚˢ : (Z : Ab×s) → (A : AbGrp ℓ) → ((x : ⟨ fst f ⟩) → A →ₐ (snd f x)) →
    A →ₐ (Z .fst .fst)
  ⟨⟩ₚˢ Z A g = Z .snd A .equiv-proof g .fst .fst

  []ᶜˢ : (Z : Ab+s) → (A : AbGrp ℓ) → ((x : ⟨ fst f ⟩) → (snd f x) →ₐ A) →
    (Z .fst .fst) →ₐ A
  []ᶜˢ Z A g = Z .snd A .equiv-proof g .fst .fst

  compπκs : (Z : AbGrp ℓ) → (p : uπκs Z) → Type ℓ
  compπκs Z p = []ᶜˢ ((Z , p .fst .fst) , p .fst .snd) Z (λ x →
    ⟨⟩ₚˢ ((Z , p .snd .fst) , p .snd .snd) (snd f x) (λ y → δFinₛ x y))
    ≡ idₐ Z

  Ab⨁ₛ : Type (ℓ-max (lsuc ℓ) ℓ')
  Ab⨁ₛ = Σ[ Z ∈ AbGrp ℓ ]
    (Σ[ p ∈ (uπκs Z)] (compπκs Z p))

  Ab⨁→Ab×s : Ab⨁ₛ → Ab×s
  Ab⨁→Ab×s Z = (Z .fst , Z .snd .fst .snd .fst) , Z .snd .fst .snd .snd

  Ab⨁→Ab+s : Ab⨁ₛ → Ab+s
  Ab⨁→Ab+s Z = (Z .fst , Z .snd .fst .fst .fst) , Z .snd .fst .fst .snd

  isPropComps : (Z : AbGrp ℓ) → (p : uπκs Z) → isProp (compπκs Z p)
  isPropComps Z p = isSet→ₐ Z Z _ _

  ⌈_⌋ˢ : Ab⨁ₛ → AbGrp ℓ
  ⌈_⌋ˢ = fst

  πˢ : (Z : Ab⨁ₛ) → (x : ⟨ fst f ⟩) → ⌈ Z ⌋ˢ →ₐ snd f x
  πˢ = fst ∘ snd ∘ fst ∘ snd

  ⟨⟩ˢ : (A : AbGrp ℓ) → (Z : Ab⨁ₛ) → ((x : ⟨ fst f ⟩) → A →ₐ (snd f x)) →
    A →ₐ ⌈ Z ⌋ˢ
  ⟨⟩ˢ A Z g = (Ab⨁→Ab×s Z) .snd A .equiv-proof g .fst .fst

  κˢ : (Z : Ab⨁ₛ) → (x : ⟨ fst f ⟩) → snd f x →ₐ ⌈ Z ⌋ˢ
  κˢ = fst ∘ fst ∘ fst ∘ snd

  []ˢ : (Z : Ab⨁ₛ) → (A : AbGrp ℓ) → ((x : ⟨ fst f ⟩) → (snd f x) →ₐ A) →
    ⌈ Z ⌋ˢ →ₐ A
  []ˢ Z A g = (Ab⨁→Ab+s Z) .snd A .equiv-proof g .fst .fst

  ⟨⟩πs : (A : AbGrp ℓ) (Z : Ab⨁ₛ) → (g : (x : ⟨ fst f ⟩) → A →ₐ snd f x) → (x : ⟨ fst f ⟩) →
    ∘ₐ A ⌈ Z ⌋ˢ (snd f x) (⟨⟩ˢ A Z g) (πˢ Z x) ≡ g x
  ⟨⟩πs A Z g x = cong (_$ x) (Z .snd .fst .snd .snd A .equiv-proof g .fst .snd)

  ∃!UPπs : (A : AbGrp ℓ) (Z : Ab⨁ₛ) → (g : (x : ⟨ fst f ⟩) → A →ₐ snd f x) → (h : A →ₐ ⌈ Z ⌋ˢ) →
    ((x : ⟨ fst f ⟩) → ∘ₐ A ⌈ Z ⌋ˢ (snd f x) h (πˢ Z x) ≡ g x) → h ≡ ⟨⟩ˢ A Z g
  ∃!UPπs A Z g h p = cong fst (sym ((Ab⨁→Ab×s Z) .snd A .equiv-proof g .snd (h , funExt p)))

  ∃!UPπsId : (Z : Ab⨁ₛ) → (g : ⌈ Z ⌋ˢ →ₐ ⌈ Z ⌋ˢ) →
    ((x : ⟨ fst f ⟩) → ∘ₐ ⌈ Z ⌋ˢ ⌈ Z ⌋ˢ (snd f x) g (πˢ Z x) ≡ πˢ Z x) →
    g ≡ idₐ ⌈ Z ⌋ˢ
  ∃!UPπsId Z g p = cong fst (isContr→isProp (Z .snd .fst .snd .snd ⌈ Z ⌋ˢ .equiv-proof (πˢ Z))
    (g , funExt p) (idₐ ⌈ Z ⌋ˢ , funExt (λ x → lUnitMorph ⌈ Z ⌋ˢ (snd f x) (πˢ Z x))))

  ⟨⟩⃖s : (A B : AbGrp ℓ) (Z : Ab⨁ₛ) → (g : A →ₐ B) → (h : (x : ⟨ fst f ⟩) → B →ₐ snd f x) →
    ∘ₐ A B ⌈ Z ⌋ˢ g (⟨⟩ˢ B Z h) ≡ ⟨⟩ˢ A Z (λ x → ∘ₐ A B (snd f x) g (h x))
  ⟨⟩⃖s A B Z g h = ∃!UPπs A Z (λ x → ∘ₐ A B (snd f x) g (h x))
    (∘ₐ A B ⌈ Z ⌋ˢ g (⟨⟩ˢ B Z h))
    (λ x →
    assocMorph A B ⌈ Z ⌋ˢ (snd f x) g (⟨⟩ˢ B Z h) (πˢ Z x) ∙ cong (λ a → ∘ₐ A B (snd f x) g a)
      (⟨⟩πs B Z h x))

  []κs : (Z : Ab⨁ₛ) (A : AbGrp ℓ) → (g : (x : ⟨ fst f ⟩) → snd f x →ₐ A) → (x : ⟨ fst f ⟩) →
    ∘ₐ (snd f x) ⌈ Z ⌋ˢ A (κˢ Z x) ([]ˢ Z A g) ≡ g x
  []κs Z A g x = cong (_$ x) ((Ab⨁→Ab+s Z) .snd A .equiv-proof g .fst .snd)

  ∃!UPκs : (Z : Ab⨁ₛ) (A : AbGrp ℓ) → (g : (x : ⟨ fst f ⟩) → snd f x →ₐ A) → (h : ⌈ Z ⌋ˢ →ₐ A) →
    ((x : ⟨ fst f ⟩) → ∘ₐ (snd f x) ⌈ Z ⌋ˢ A (κˢ Z x) h ≡ g x) → h ≡ []ˢ Z A g
  ∃!UPκs Z A g h p = cong fst (sym ((Ab⨁→Ab+s Z) .snd A .equiv-proof g .snd (h , funExt p)))

  ∃!UPκsId : (Z : Ab⨁ₛ) (g : ⌈ Z ⌋ˢ →ₐ ⌈ Z ⌋ˢ) →
    ((x : ⟨ fst f ⟩) → ∘ₐ (snd f x) ⌈ Z ⌋ˢ ⌈ Z ⌋ˢ (κˢ Z x) g ≡ κˢ Z x) →
    g ≡ idₐ ⌈ Z ⌋ˢ
  ∃!UPκsId Z g p = cong fst (isContr→isProp (Z .snd .fst .fst .snd ⌈ Z ⌋ˢ .equiv-proof (κˢ Z))
    (g , funExt p) (idₐ ⌈ Z ⌋ˢ , funExt (λ x → rUnitMorph (snd f x) ⌈ Z ⌋ˢ (κˢ Z x))))

  []⃗s : (Z : Ab⨁ₛ) (A B : AbGrp ℓ) → (g : (x : ⟨ fst f ⟩) → snd f x →ₐ A) → (h : A →ₐ B) →
    ∘ₐ ⌈ Z ⌋ˢ A B ([]ˢ Z A g) h ≡ []ˢ Z B (λ x → ∘ₐ (snd f x) A B (g x) h)
  []⃗s Z A B g h = ∃!UPκs Z B (λ x → ∘ₐ (snd f x) A B (g x) h)
    (∘ₐ ⌈ Z ⌋ˢ A B ([]ˢ Z A g) h)
    (λ x →
    sym (assocMorph (snd f x) ⌈ Z ⌋ˢ A B (κˢ Z x) ([]ˢ Z A g) h) ∙ cong (λ a → ∘ₐ (snd f x) A B a h)
      ([]κs Z A g x))

  -- We prove that δFinₛ is equivalent to κ ∘ π

  is⟨⟩κs : (A : Ab⨁ₛ) → (x : ⟨ fst f ⟩) → ⟨⟩ˢ (snd f x) A (λ y → δFinₛ x y) ≡ κˢ A x
  is⟨⟩κs A x = sym ([]κs A ⌈ A ⌋ˢ (λ x → ⟨⟩ˢ (snd f x) A (λ y → δFinₛ x y)) x) ∙
    cong (λ a → ∘ₐ (snd f x) ⌈ A ⌋ˢ ⌈ A ⌋ˢ (κˢ A x) a) (A .snd .snd) ∙
    rUnitMorph (snd f x) ⌈ A ⌋ˢ (κˢ A x)

  κᵢ∘πᵢ : (A : Ab⨁ₛ) → (x y : ⟨ fst f ⟩) →
    ∘ₐ (snd f x) ⌈ A ⌋ˢ (snd f y) (κˢ A x) (πˢ A y) ≡ δFinₛ x y
  κᵢ∘πᵢ A x y =  cong (λ a → ∘ₐ (snd f x) ⌈ A ⌋ˢ (snd f y) a (πˢ A y)) (sym (is⟨⟩κs A x)) ∙
    ⟨⟩πs (snd f x) A (λ y → δFinₛ x y) y

  -- We make the equivalences between two biproducts A and Z, respectively through their
  -- product and coproduct structure

  fˣs : (Z : Ab⨁ₛ) → (A : Ab⨁ₛ) → ⌈ Z ⌋ˢ →ₐ ⌈ A ⌋ˢ
  fˣs Z A = ⟨⟩ˢ ⌈ Z ⌋ˢ A (πˢ Z)

  lemmafˣs : (Z A : Ab⨁ₛ) →
    (λ x → ∘ₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (snd f x) (fˣs Z A) (πˢ A x)) ≡ πˢ Z
  lemmafˣs Z A = (Ab⨁→Ab×s A) .snd ⌈ Z ⌋ˢ .equiv-proof (πˢ Z) .fst .snd

  ≃ₐ×s : (Z A : Ab⨁ₛ) → ⌈ Z ⌋ˢ ≃ₐ ⌈ A ⌋ˢ
  ≃ₐ×s Z A = Isoₐ→≃ₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (record {
    funₐ = fˣs Z A ;
    invₐ = fˣs A Z ;
    leftInvₐ = ∃!UPπsId Z (∘ₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ ⌈ Z ⌋ˢ (fˣs Z A) (fˣs A Z)) (λ x →
      (assocMorph ⌈ Z ⌋ˢ ⌈ A ⌋ˢ ⌈ Z ⌋ˢ (snd f x) (fˣs Z A) (fˣs A Z) (πˢ Z x)
        ∙ cong (λ a → ∘ₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (snd f x) (fˣs Z A) (a x)) (lemmafˣs A Z)
        ∙ cong (_$ x) (lemmafˣs Z A))) ;
    rightInvₐ = ∃!UPπsId A (∘ₐ ⌈ A ⌋ˢ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (fˣs A Z) (fˣs Z A)) (λ x →
      (assocMorph ⌈ A ⌋ˢ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (snd f x) (fˣs A Z) (fˣs Z A) (πˢ A x)
        ∙ cong (λ a → ∘ₐ ⌈ A ⌋ˢ ⌈ Z ⌋ˢ (snd f x) (fˣs A Z) (a x)) (lemmafˣs Z A)
        ∙ cong (_$ x) (lemmafˣs A Z))) })

  f⁺s : (Z A : Ab⨁ₛ) → ⌈ Z ⌋ˢ →ₐ ⌈ A ⌋ˢ
  f⁺s Z A = []ˢ Z ⌈ A ⌋ˢ (κˢ A)

  lemmaf⁺s : (Z A : Ab⨁ₛ) →
    (λ x → ∘ₐ (snd f x) ⌈ A ⌋ˢ ⌈ Z ⌋ˢ (κˢ A x) (f⁺s A Z)) ≡ κˢ Z
  lemmaf⁺s Z A = (Ab⨁→Ab+s A) .snd ⌈ Z ⌋ˢ .equiv-proof (κˢ Z) .fst .snd

  ≃ₐ+s : (Z A : Ab⨁ₛ) → ⌈ Z ⌋ˢ ≃ₐ ⌈ A ⌋ˢ
  ≃ₐ+s Z A = Isoₐ→≃ₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (record {
    funₐ = f⁺s Z A ;
    invₐ = f⁺s A Z ;
    leftInvₐ = ∃!UPκsId Z (∘ₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ ⌈ Z ⌋ˢ (f⁺s Z A) (f⁺s A Z)) (λ x →
      (sym (assocMorph (snd f x) ⌈ Z ⌋ˢ ⌈ A ⌋ˢ ⌈ Z ⌋ˢ (κˢ Z x) (f⁺s Z A) (f⁺s A Z))
        ∙ cong (λ a → ∘ₐ (snd f x) ⌈ A ⌋ˢ ⌈ Z ⌋ˢ (a x) (f⁺s A Z)) (lemmaf⁺s A Z)
        ∙ cong (_$ x) (lemmaf⁺s Z A))) ;
    rightInvₐ = ∃!UPκsId A (∘ₐ ⌈ A ⌋ˢ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (f⁺s A Z) (f⁺s Z A)) (λ x →
      (sym (assocMorph (snd f x) ⌈ A ⌋ˢ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (κˢ A x) (f⁺s A Z) (f⁺s Z A))
        ∙ cong (λ a → ∘ₐ (snd f x) ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (a x) (f⁺s Z A)) (lemmaf⁺s Z A)
        ∙ cong (_$ x) (lemmaf⁺s A Z))) })

  -- We prove that they coincide

  ≡≃ₐ+×s : (Z A : Ab⨁ₛ) → f⁺s Z A ≡ fˣs Z A
  ≡≃ₐ+×s Z A = sym (∃!UPκs Z ⌈ A ⌋ˢ (κˢ A) (⟨⟩ˢ ⌈ Z ⌋ˢ A (πˢ Z)) (λ x → 
    (cong (λ a → ∘ₐ (snd f x) ⌈ Z ⌋ˢ ⌈ A ⌋ˢ a (⟨⟩ˢ ⌈ Z ⌋ˢ A (πˢ Z)))
      ((sym (rUnitMorph (snd f x) ⌈ Z ⌋ˢ (κˢ Z x)))
        ∙ cong (λ a → ∘ₐ (snd f x) ⌈ Z ⌋ˢ ⌈ Z ⌋ˢ (κˢ Z x) a) (sym (Z .snd .snd)) ∙
      []κs Z ⌈ Z ⌋ˢ (λ x → ⟨⟩ˢ (snd f x) Z (λ y → δFinₛ x y)) x) ∙
      ⟨⟩⃖s (snd f x) ⌈ Z ⌋ˢ A (⟨⟩ˢ (snd f x) Z (δFinₛ x)) (πˢ Z) ∙
      cong (λ a → ⟨⟩ˢ (snd f x) A a)
        (funExt (λ x₁ → (⟨⟩πs (snd f x) Z (δFinₛ x) x₁)))
        ∙ is⟨⟩κs A x)))

  ≡≡ₐ+×s : (Z A : Ab⨁ₛ) → ≃ₐ+s Z A ≡ ≃ₐ×s Z A
  ≡≡ₐ+×s Z A = invEquiv (≡≃ₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (≃ₐ+s Z A) (≃ₐ×s Z A)) .fst (≡≃ₐ+×s Z A)

  Pathπ×s : (Z A : Ab⨁ₛ) → PathP (λ i → (x : ⟨ fst f ⟩) → uaₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (≃ₐ×s Z A) i →ₐ snd f x)
    (Z .snd .fst .snd .fst) (A .snd .fst .snd .fst)
  Pathπ×s Z A = funExt (λ x → toPathP ((→A≡ ⌈ A ⌋ˢ (snd f x) (
    fromPathP (funTypeTransp (λ X → ⌈ X ⌋) (λ _ → ⌈ snd f x ⌋)
      (uaₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (≃ₐ×s Z A)) (Z .snd .fst .snd .fst x .fst))
      ∙ cong (λ a → a ∘ Z .snd .fst .snd .fst x .fst ∘
        subst (λ X → ⌈ X ⌋) (sym (uaₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (≃ₐ×s Z A)))) (funExt (λ x → transportRefl x))
      ∙ ∘-idʳ _ ∙ cong (λ a → Z .snd .fst .snd .fst x .fst ∘ a)
      (cong transport (sym (uaInvEquiv (fst (≃ₐ×s Z A)))) ∙ funExt (uaβ (invEquiv (fst (≃ₐ×s Z A)))))
      ∙ cong (fst ∘ (_$ x)) (lemmafˣs A Z)))))

  Pathκ+s : (Z A : Ab⨁ₛ) → PathP (λ i → (x : ⟨ fst f ⟩) → snd f x →ₐ uaₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (≃ₐ+s Z A) i)
    (Z .snd .fst .fst .fst) (A .snd .fst .fst .fst)
  Pathκ+s Z A = funExt (λ x → toPathP ((→A≡ (snd f x) ⌈ A ⌋ˢ (
    fromPathP (funTypeTransp (λ _ → ⌈ snd f x ⌋) (λ X → ⌈ X ⌋)
      (uaₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (≃ₐ+s Z A)) (Z .snd .fst .fst .fst x .fst))
      ∙ cong (λ a → subst (λ X → ⌈ X ⌋) (uaₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (≃ₐ+s Z A)) ∘
        Z .snd .fst .fst .fst x .fst ∘ a) (funExt (λ x → transportRefl x))
      ∙ ∘-idʳ _ ∙ cong (λ a → a ∘ Z .snd .fst .fst .fst x .fst)
      (funExt (uaβ (fst (≃ₐ+s Z A)))) ∙ cong (fst ∘ (_$ x)) (lemmaf⁺s A Z)))))

  Pathκ×s : (Z A : Ab⨁ₛ) → PathP (λ i → (x : ⟨ fst f ⟩) → snd f x →ₐ uaₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (≃ₐ×s Z A) i)
    (Z .snd .fst .fst .fst) (A .snd .fst .fst .fst)
  Pathκ×s Z A = subst (λ e → PathP (λ i → (x : ⟨ fst f ⟩) → snd f x →ₐ e i)
                         (Z .snd .fst .fst .fst) (A .snd .fst .fst .fst))
          (cong (uaₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ) (≡≡ₐ+×s Z A)) (Pathκ+s Z A)

  -- Merging all the equalities, we deduce that Ab⨁ₛ is a proposition

  isPropAb⨁ₛ : isProp Ab⨁ₛ
  isPropAb⨁ₛ Z A = ΣPathP (uaₐ ⌈ Z ⌋ˢ ⌈ A ⌋ˢ (≃ₐ×s Z A) , ΣPathPProp (λ p → isPropComps ⌈ A ⌋ˢ p)
    (ΣPathP (
      ΣPathPProp (λ _ → isPropΠ (λ _ → isPropIsEquiv _)) (Pathκ×s Z A) ,
      ΣPathPProp (λ _ → isPropΠ (λ _ → isPropIsEquiv _)) (Pathπ×s Z A))))
