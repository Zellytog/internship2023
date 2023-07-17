open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Sigma
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Sign.AbGrp.Base

-- We prove here that the biproduct ⊕ in 𝔸𝕓 can be defined and that it is contractible

module Sign.AbGrp.BinBiprod where

infixr 35 _⊕ₐ_ _⊕ₜ_

private
  variable
    ℓ : Level

module _ (X : AbGrp ℓ) (Y : AbGrp ℓ) where

-- Definitions and properties about product in 𝔸𝕓

  pre× : Type (lsuc ℓ)
  pre× = Σ[ Z ∈ AbGrp ℓ ] ((Z →ₐ X) × (Z →ₐ Y))

  distrib× : (Z : pre×) → (A : AbGrp ℓ) → (A →ₐ fst Z) → (A →ₐ X) × (A →ₐ Y)
  distrib× Z A f = ∘ₐ A (fst Z) X f (Z .snd .fst) , ∘ₐ A (fst Z) Y f (Z .snd .snd)
  
  universal× : (Z : pre×) → Type (lsuc ℓ)
  universal× Z = (A : AbGrp ℓ) → isEquiv (distrib× Z A)

  Ab× : Type (lsuc ℓ)
  Ab× = Σ[ Z ∈ pre× ] (universal× Z)

  ⌈_⌋ₚ : Ab× → AbGrp ℓ
  ⌈_⌋ₚ = fst ∘ fst

  πₐ : (Z : Ab×) → (⌈ Z ⌋ₚ →ₐ X) × (⌈ Z ⌋ₚ →ₐ Y)
  πₐ = snd ∘ fst

  πₐ₁ : (Z : Ab×) → ⌈ Z ⌋ₚ →ₐ X
  πₐ₁ = fst ∘ snd ∘ fst

  πₐ₂ : (Z : Ab×) → ⌈ Z ⌋ₚ →ₐ Y
  πₐ₂ = snd ∘ snd ∘ fst

  ⟨⟩ₚ : (A : AbGrp ℓ) (Z : Ab×) → (A →ₐ X) → (A →ₐ Y) → A →ₐ ⌈ Z ⌋ₚ
  ⟨⟩ₚ A Z f g = Z .snd A .equiv-proof (f , g) .fst .fst

  projPairingl : (A : AbGrp ℓ) (Z : Ab×) → (f : A →ₐ X) → (g : A →ₐ Y) →
    ∘ₐ A ⌈ Z ⌋ₚ X (⟨⟩ₚ A Z f g) (πₐ₁ Z) ≡ f
  projPairingl A Z f g = cong fst (Z .snd A .equiv-proof (f , g) .fst .snd)

  projPairingr : (A : AbGrp ℓ) (Z : Ab×) → (f : A →ₐ X) → (g : A →ₐ Y) →
    ∘ₐ A ⌈ Z ⌋ₚ Y (⟨⟩ₚ A Z f g) (πₐ₂ Z) ≡ g
  projPairingr A Z f g = cong snd (Z .snd A .equiv-proof (f , g) .fst .snd)

  unicityUPProj : (A : AbGrp ℓ) (Z : Ab×) → (f : A →ₐ X) → (g : A →ₐ Y) → (h : A →ₐ ⌈ Z ⌋ₚ) →
    ∘ₐ A ⌈ Z ⌋ₚ X h (πₐ₁ Z) ≡ f → ∘ₐ A ⌈ Z ⌋ₚ Y h (πₐ₂ Z) ≡ g →
    h ≡ ⟨⟩ₚ A Z f g
  unicityUPProj A Z f g h p q = cong fst (sym (Z .snd A .equiv-proof (f , g) .snd (h , ≡-× p q)))

  unicityUPProjId : (Z : Ab×) → (f : ⌈ Z ⌋ₚ →ₐ ⌈ Z ⌋ₚ) →
    ∘ₐ ⌈ Z ⌋ₚ ⌈ Z ⌋ₚ X f (πₐ₁ Z) ≡ πₐ₁ Z → ∘ₐ ⌈ Z ⌋ₚ ⌈ Z ⌋ₚ Y f (πₐ₂ Z) ≡ πₐ₂ Z →
    f ≡ idₐ ⌈ Z ⌋ₚ
  unicityUPProjId Z f p q = cong fst (isContr→isProp (Z .snd (Z .fst .fst) .equiv-proof (Z .fst .snd))
    (f , ≡-× p q) (idₐ (Z .fst .fst) , ≡-× (lUnitMorph ⌈ Z ⌋ₚ X (πₐ₁ Z))
                                           (lUnitMorph ⌈ Z ⌋ₚ Y (πₐ₂ Z))))

  pairingPreComp : (A : AbGrp ℓ) (B : AbGrp ℓ) (Z : Ab×) → (f : A →ₐ B) → (g : B →ₐ X) (h : B →ₐ Y) →
    ∘ₐ A B ⌈ Z ⌋ₚ f (⟨⟩ₚ B Z g h) ≡ ⟨⟩ₚ A Z (∘ₐ A B X f g) (∘ₐ A B Y f h)
  pairingPreComp A B Z f g h = unicityUPProj A Z (∘ₐ A B X f g) (∘ₐ A B Y f h)
    (∘ₐ A B ⌈ Z ⌋ₚ f (⟨⟩ₚ B Z g h))
    (assocMorph A B ⌈ Z ⌋ₚ X f (⟨⟩ₚ B Z g h) (πₐ₁ Z) ∙ cong (λ a → ∘ₐ A B X f a)
      (projPairingl B Z g h))
    (assocMorph A B ⌈ Z ⌋ₚ Y f (⟨⟩ₚ B Z g h) (πₐ₂ Z) ∙ cong (λ a → ∘ₐ A B Y f a)
      (projPairingr B Z g h))

-- Definitions and properties about coproduct in 𝔸𝕓

  pre+ : Type (lsuc ℓ)
  pre+ = Σ[ Z ∈ AbGrp ℓ ] ((X →ₐ Z) × (Y →ₐ Z))

  distrib+ : (Z : pre+) → (A : AbGrp ℓ) → (fst Z →ₐ A) → (X →ₐ A) × (Y →ₐ A)
  distrib+ Z A f = ∘ₐ X (fst Z) A (Z .snd .fst) f , ∘ₐ Y (fst Z) A (Z .snd .snd) f

  universal+ : (Z : pre+) → Type (lsuc ℓ)
  universal+ Z = (A : AbGrp ℓ) → isEquiv (distrib+ Z A)

  Ab+ : Type (lsuc ℓ)
  Ab+ = Σ[ Z ∈ pre+ ] (universal+ Z)

  ⌈_⌋ᶜ : Ab+ → AbGrp ℓ
  ⌈_⌋ᶜ = fst ∘ fst

  κₐ : (Z : Ab+) → (X →ₐ ⌈ Z ⌋ᶜ) × (Y →ₐ ⌈ Z ⌋ᶜ)
  κₐ = snd ∘ fst

  κₐ₁ : (Z : Ab+) → X →ₐ ⌈ Z ⌋ᶜ
  κₐ₁ = fst ∘ snd ∘ fst

  κₐ₂ : (Z : Ab+) → Y →ₐ ⌈ Z ⌋ᶜ
  κₐ₂ = snd ∘ snd ∘ fst

  []ᶜ : (Z : Ab+) (A : AbGrp ℓ) → (X →ₐ A) → (Y →ₐ A) → ⌈ Z ⌋ᶜ →ₐ A
  []ᶜ Z A f g = Z .snd A .equiv-proof (f , g) .fst .fst

  projCopairingl : (Z : Ab+) (A : AbGrp ℓ) → (f : X →ₐ A) → (g : Y →ₐ A) →
    ∘ₐ X ⌈ Z ⌋ᶜ A (κₐ₁ Z) ([]ᶜ Z A f g) ≡ f
  projCopairingl Z A f g = cong fst (Z .snd A .equiv-proof (f , g) .fst .snd)

  projCopairingr : (Z : Ab+) (A : AbGrp ℓ) → (f : X →ₐ A) → (g : Y →ₐ A) →
    ∘ₐ Y ⌈ Z ⌋ᶜ A (κₐ₂ Z) ([]ᶜ Z A f g) ≡ g
  projCopairingr Z A f g = cong snd (Z .snd A .equiv-proof (f , g) .fst .snd)

  unicityUPCoproj : (Z : Ab+) (A : AbGrp ℓ) → (f : X →ₐ A) → (g : Y →ₐ A) →
    (h : ⌈ Z ⌋ᶜ →ₐ A) → ∘ₐ X ⌈ Z ⌋ᶜ A (κₐ₁ Z) h ≡ f → ∘ₐ Y ⌈ Z ⌋ᶜ A (κₐ₂ Z) h ≡ g → h ≡ []ᶜ Z A f g
  unicityUPCoproj Z A f g h p q = cong fst (sym (Z .snd A .equiv-proof (f , g) .snd (h , ≡-× p q)))

  unicityUPCoprojId : (Z : Ab+) (f : ⌈ Z ⌋ᶜ →ₐ ⌈ Z ⌋ᶜ) →
    ∘ₐ X ⌈ Z ⌋ᶜ ⌈ Z ⌋ᶜ (κₐ₁ Z) f ≡ κₐ₁ Z → ∘ₐ Y ⌈ Z ⌋ᶜ ⌈ Z ⌋ᶜ (κₐ₂ Z) f ≡ κₐ₂ Z →
    f ≡ idₐ ⌈ Z ⌋ᶜ
  unicityUPCoprojId Z f p q = cong fst (isContr→isProp (Z .snd ⌈ Z ⌋ᶜ .
    equiv-proof (Z .fst .snd)) (f , ≡-× p q)
    (idₐ ⌈ Z ⌋ᶜ , ≡-× (rUnitMorph X ⌈ Z ⌋ᶜ (κₐ₁ Z)) (rUnitMorph Y ⌈ Z ⌋ᶜ (κₐ₂ Z))))

  copairingPostComp : (Z : Ab+) (A B : AbGrp ℓ) → (f : X →ₐ A) (g : Y →ₐ A) → (h : A →ₐ B) →
    ∘ₐ ⌈ Z ⌋ᶜ A B ([]ᶜ Z A f g) h ≡ []ᶜ Z B (∘ₐ X A B f h) (∘ₐ Y A B g h)
  copairingPostComp Z A B g h f = unicityUPCoproj Z B (∘ₐ X A B g f) (∘ₐ Y A B h f)
    (∘ₐ ⌈ Z ⌋ᶜ A B ([]ᶜ Z A g h) f)
    (sym (assocMorph X ⌈ Z ⌋ᶜ A B (κₐ₁ Z) ([]ᶜ Z A g h) f) ∙
      cong (λ a → ∘ₐ X A B a f) (projCopairingl Z A g h))
    (sym (assocMorph Y ⌈ Z ⌋ᶜ A B (κₐ₂ Z) ([]ᶜ Z A g h) f) ∙
      cong (λ a → ∘ₐ Y A B a f) (projCopairingr Z A g h))

-- Definitions and properties about biproduct in 𝔸𝕓

  Univₚᶜ : (Z : AbGrp ℓ) → Type (lsuc ℓ)
  Univₚᶜ Z = (Σ[ p ∈ ((Z →ₐ X) × (Z →ₐ Y))] (universal× (Z , p))) ×
             (Σ[ p ∈ ((X →ₐ Z) × (Y →ₐ Z))] (universal+ (Z , p)))

  compₚᶜ : (Z : AbGrp ℓ) → (p : Univₚᶜ Z) → Type ℓ
  compₚᶜ Z p = []ᶜ ((Z , p .snd .fst) , p .snd .snd) Z
    (⟨⟩ₚ X ((Z , p .fst .fst), p .fst .snd) (idₐ X) (0ₐ X Y))
    (⟨⟩ₚ Y ((Z , p .fst .fst), p .fst .snd) (0ₐ Y X) (idₐ Y)) ≡ idₐ Z

  isPropCompₚᶜ : (Z : AbGrp ℓ) (p : Univₚᶜ Z) → isProp (compₚᶜ Z p)
  isPropCompₚᶜ Z p = isSet→ₐ Z Z _ _

  Ab⊕ : Type (lsuc ℓ)
  Ab⊕ = Σ[ Z ∈ AbGrp ℓ ] (Σ[ p ∈ (Univₚᶜ Z)] (compₚᶜ Z p))

  ⌈_⌋ᵇ : (Z : Ab⊕) → AbGrp ℓ
  ⌈_⌋ᵇ = fst

  πᵇ : (Z : Ab⊕) → (⌈ Z ⌋ᵇ →ₐ X) × (⌈ Z ⌋ᵇ →ₐ Y)
  πᵇ = fst ∘ fst ∘ fst ∘ snd

  πᵇ₁ : (Z : Ab⊕) → ⌈ Z ⌋ᵇ →ₐ X
  πᵇ₁ = fst ∘ fst ∘ fst ∘ fst ∘ snd

  πᵇ₂ : (Z : Ab⊕) → ⌈ Z ⌋ᵇ →ₐ Y
  πᵇ₂ = snd ∘ fst ∘ fst ∘ fst ∘ snd

  κᵇ : (Z : Ab⊕) → (X →ₐ ⌈ Z ⌋ᵇ) × (Y →ₐ ⌈ Z ⌋ᵇ)
  κᵇ = fst ∘ snd ∘ fst ∘ snd

  κᵇ₁ : (Z : Ab⊕) → X →ₐ ⌈ Z ⌋ᵇ
  κᵇ₁ = fst ∘ fst ∘ snd ∘ fst ∘ snd

  κᵇ₂ : (Z : Ab⊕) → Y →ₐ ⌈ Z ⌋ᵇ
  κᵇ₂ = snd ∘ fst ∘ snd ∘ fst ∘ snd

  Ab⊕→Ab× : Ab⊕ → Ab×
  Ab⊕→Ab× Z = (⌈ Z ⌋ᵇ , (πᵇ₁ Z , πᵇ₂ Z)) , Z .snd .fst .fst .snd

  Ab⊕→Ab+ : Ab⊕ → Ab+
  Ab⊕→Ab+ Z = (⌈ Z ⌋ᵇ , (κᵇ₁ Z , κᵇ₂ Z)) , Z .snd .fst .snd .snd

  is⟨⟩κ₁ : (A : Ab⊕) → ⟨⟩ₚ X (Ab⊕→Ab× A) (idₐ X) (0ₐ X Y) ≡ κᵇ₁ A
  is⟨⟩κ₁ A = sym (projCopairingl (Ab⊕→Ab+ A) ⌈ A ⌋ᵇ (⟨⟩ₚ X (Ab⊕→Ab× A) (idₐ X) (0ₐ X Y))
    (⟨⟩ₚ Y (Ab⊕→Ab× A) (0ₐ Y X) (idₐ Y))) ∙
    cong (λ a → ∘ₐ X ⌈ A ⌋ᵇ ⌈ A ⌋ᵇ (κᵇ₁ A) a) (A .snd .snd) ∙ rUnitMorph X ⌈ A ⌋ᵇ (κᵇ₁ A)

  is⟨⟩κ₂ : (A : Ab⊕) → ⟨⟩ₚ Y (Ab⊕→Ab× A) (0ₐ Y X) (idₐ Y) ≡ κᵇ₂ A
  is⟨⟩κ₂ A = sym (projCopairingr (Ab⊕→Ab+ A) ⌈ A ⌋ᵇ (⟨⟩ₚ X (Ab⊕→Ab× A) (idₐ X) (0ₐ X Y))
    (⟨⟩ₚ Y (Ab⊕→Ab× A) (0ₐ Y X) (idₐ Y))) ∙
    cong (λ a → ∘ₐ Y ⌈ A ⌋ᵇ ⌈ A ⌋ᵇ (κᵇ₂ A) a) (A .snd .snd) ∙ rUnitMorph Y ⌈ A ⌋ᵇ (κᵇ₂ A)

-- Construction of the biproduct

  ab⊕cparam : (X : AbGrp ℓ) → (Y : AbGrp ℓ) → AbGrp ℓ
  ab⊕cparam X Y = (⌈ X ⌋ × ⌈ Y ⌋ ,
    ((∙ₐ X , ∙ₐ Y) ,
    (λ x → λ y → proprec isPropPropTrunc (λ e → proprec isPropPropTrunc (λ e' →
      ∣ ≡-× e e' ∣₁) (∥≡∥ₐ Y (snd x) (snd y))) (∥≡∥ₐ X (fst x) (fst y))) ,
    isGroupoid× (groupAb X) (groupAb Y) ,
    ( (λ x → λ i → ((≡∙ₐ X (fst x)) i .fst) × ((≡∙ₐ Y (snd x)) i .fst) ,
                   (((≡∙ₐ X (fst x)) i .snd) , ((≡∙ₐ Y (snd x)) i .snd))) ,
    λ j → λ i → (≡∙ₐr X j i .fst × ≡∙ₐr Y j i .fst , ≡∙ₐr X j i .snd , ≡∙ₐr Y j i .snd)) ))

  ab⊕c : AbGrp ℓ
  ab⊕c = ab⊕cparam X Y

  decomp⊕ : (x : ⌈ ab⊕c ⌋) → x ≡ +ₐ ab⊕c (fst x , ∙ₐ Y) (∙ₐ X , snd x)
  decomp⊕ x = ≡-× (sym (actAbIdr X (fst x))) (sym (actAbIdl Y (snd x)))

  -- Construction of the product structure

  πc : (ab⊕c →ₐ X) × (ab⊕c →ₐ Y)
  πc = (fst , refl) , (snd , refl)

  πc₁ : ab⊕c →ₐ X
  πc₁ = πc .fst

  πc₂ : ab⊕c →ₐ Y
  πc₂ = πc .snd

  Pre×c : pre×
  Pre×c = ab⊕c , πc

  fact×c : (A : AbGrp ℓ) → (A →ₐ X) → (A →ₐ Y) → (A →ₐ ab⊕c)
  fact×c A f g = (λ x → fst f x , fst g x) , cong₂ (λ a b → a , b) (snd f) (snd g)

  univ×c : universal× Pre×c
  univ×c A = isoToIsEquiv (record {fun = distrib× Pre×c A ;
    inv = λ p → fact×c A (fst p) (snd p) ;
    rightInv = λ p → ≡-× (→A≡ A X (funExt (λ _ → refl))) (→A≡ A Y (funExt (λ _ → refl))) ;
    leftInv = λ h → →A≡ A ab⊕c (funExt (λ _ → refl)) })
    
  take× : Ab×
  take× = Pre×c , univ×c

  fˣ : (Z : Ab×) → (A : Ab×) → ⌈ Z ⌋ₚ →ₐ ⌈ A ⌋ₚ
  fˣ Z A = ⟨⟩ₚ ⌈ Z ⌋ₚ A (πₐ₁ Z) (πₐ₂ Z)
  
  lemmafˣ : (Z : Ab×) (A : Ab×) →
    (∘ₐ ⌈ Z ⌋ₚ ⌈ A ⌋ₚ X (fˣ Z A) (πₐ₁ A) , ∘ₐ ⌈ Z ⌋ₚ ⌈ A ⌋ₚ Y (fˣ Z A) (πₐ₂ A)) ≡ πₐ Z
  lemmafˣ Z A = A .snd ⌈ Z ⌋ₚ .equiv-proof (πₐ Z) .fst .snd
  
  ≃Ab× : (A : Ab×) → ⌈ ⌈ take× ⌋ₚ ⌋ ≃ ⌈ ⌈ A ⌋ₚ ⌋
  ≃Ab× A = isoToEquiv (record {
    fun = fˣ prod A .fst ;
    inv = fˣ A prod .fst ;
    rightInv = λ x → cong (λ f → fst f x)
      (unicityUPProjId A (∘ₐ ⌈ A ⌋ₚ ⌈ prod ⌋ₚ ⌈ A ⌋ₚ (fˣ A prod) (fˣ prod A))
      (assocMorph ⌈ A ⌋ₚ ⌈ prod ⌋ₚ ⌈ A ⌋ₚ X (fˣ A prod) (fˣ prod A) (πₐ₁ A)
        ∙ cong (λ a → ∘ₐ ⌈ A ⌋ₚ ⌈ prod ⌋ₚ X (fˣ A prod) (fst a)) (lemmafˣ prod A)
        ∙ cong fst (lemmafˣ A prod))
      (assocMorph ⌈ A ⌋ₚ ⌈ prod ⌋ₚ ⌈ A ⌋ₚ Y (fˣ A prod) (fˣ prod A) (πₐ₂ A)
        ∙ cong (λ a → ∘ₐ ⌈ A ⌋ₚ ⌈ prod ⌋ₚ Y (fˣ A prod) (snd a)) (lemmafˣ prod A)
        ∙ cong snd (lemmafˣ A prod))) ;
    leftInv = λ x → cong (λ f → fst f x)
      ( unicityUPProjId prod (∘ₐ ⌈ prod ⌋ₚ ⌈ A ⌋ₚ ⌈ prod ⌋ₚ (fˣ prod A) (fˣ A prod))
      (assocMorph ⌈ prod ⌋ₚ ⌈ A ⌋ₚ ⌈ prod ⌋ₚ X (fˣ prod A) (fˣ A prod) (πₐ₁ prod)
        ∙ cong (λ a → ∘ₐ ⌈ prod ⌋ₚ ⌈ A ⌋ₚ X (fˣ prod A) (fst a)) (lemmafˣ A prod)
        ∙ cong fst (lemmafˣ prod A))
      (assocMorph ⌈ prod ⌋ₚ ⌈ A ⌋ₚ ⌈ prod ⌋ₚ Y (fˣ prod A) (fˣ A prod) (πₐ₂ prod)
        ∙ cong (λ a → ∘ₐ ⌈ prod ⌋ₚ ⌈ A ⌋ₚ Y (fˣ prod A) (snd a)) (lemmafˣ A prod)
        ∙ cong snd (lemmafˣ prod A)))})
    where
    prod : Ab×
    prod = take×

  isContrProd : isContr Ab×
  isContrProd = (take× , λ A → Σ≡Prop (λ _ → isPropΠ (λ A → isPropIsEquiv _))
    (ΣPathTransport→PathΣ _ _ (uaₐ (⌈ take× ⌋ₚ) (⌈ A ⌋ₚ) (≃Ab× A , fˣ take× A .snd) , ≡-×
    (→A≡ ⌈ A ⌋ₚ X (fromPathP (funTypeTransp (λ X → X) (λ _ → fst X) (ua (≃Ab× A)) fst)
      ∙ cong (λ x → x ∘ fst ∘ transport (sym (ua (≃Ab× A)))) (funExt (λ x → transportRefl x))
      ∙ ∘-idʳ _ ∙ cong (λ x → fst ∘ x) (cong transport (sym (uaInvEquiv (≃Ab× A)))
      ∙  funExt (uaβ (invEquiv (≃Ab× A)))) ∙ cong (fst ∘ fst) (lemmafˣ A take×)))
    (→A≡ ⌈ A ⌋ₚ Y (fromPathP (funTypeTransp (λ X → X) (λ _ → fst Y) (ua (≃Ab× A)) (snd))
      ∙ cong (λ x → x ∘ snd ∘ transport (sym (ua (≃Ab× A)))) (funExt (λ x → transportRefl x))
      ∙ ∘-idʳ _ ∙ cong (λ x → snd ∘ x) (cong transport (sym (uaInvEquiv (≃Ab× A)))
      ∙  funExt (uaβ (invEquiv (≃Ab× A)))) ∙ cong (fst ∘ snd) (lemmafˣ A take×))) )))
    
  -- Construction of the coproduct structure
  
  κc : (X →ₐ ab⊕c) × (Y →ₐ ab⊕c)
  κc = ((λ x → x , ∙ₐ Y) , refl) , ((λ y → ∙ₐ X , y) , refl)

  κc₁ : X →ₐ ab⊕c
  κc₁ = κc .fst

  κc₂ : Y →ₐ ab⊕c
  κc₂ = κc .snd

  Pre+c : pre+
  Pre+c = ab⊕c , κc

  fact+c : (A : AbGrp ℓ) → (X →ₐ A) → (Y →ₐ A) → (ab⊕c →ₐ A)
  fact+c A f g = ((λ x → +ₐ A (fst f (fst x)) (fst g (snd x))) ,
    (cong₂ (λ a b → +ₐ A a b) (snd f) (snd g) ∙ actAbIdr A (∙ₐ A)))

  univ+c : universal+ Pre+c
  univ+c A = isoToIsEquiv (record { fun = distrib+ Pre+c A ;
    inv = λ p → fact+c A (fst p) (snd p) ;
    rightInv = λ p → ≡-× (→A≡ X A
      (funExt (λ x → cong (λ a → +ₐ A (p .fst .fst x) a) (p .snd .snd)
        ∙ actAbIdr A (p .fst .fst x))))
      (→A≡ Y A
      (funExt (λ y → cong (λ a → +ₐ A a (p .snd .fst y)) (p .fst .snd)
        ∙ actAbIdl A (p .snd .fst y)))); 
    leftInv = λ h → →A≡ ab⊕c A ((funExt λ x → →ₐ+ ab⊕c A h (fst x , ∙ₐ Y) (∙ₐ X , snd x)
      ∙ sym (cong (fst h) (decomp⊕ x)))) })

  take+ : Ab+
  take+ = Pre+c , univ+c

  f⁺ : (Z : Ab+) → (A : Ab+) → ⌈ Z ⌋ᶜ →ₐ ⌈ A ⌋ᶜ
  f⁺ Z A = []ᶜ Z ⌈ A ⌋ᶜ (κₐ₁ A) (κₐ₂ A)

  lemmaf⁺ : (Z : Ab+) (A : Ab+) →
    (∘ₐ X ⌈ A ⌋ᶜ ⌈ Z ⌋ᶜ (κₐ₁ A) (f⁺ A Z), ∘ₐ Y ⌈ A ⌋ᶜ ⌈ Z ⌋ᶜ (κₐ₂ A) (f⁺ A Z)) ≡ κₐ Z
  lemmaf⁺ Z A = A .snd ⌈ Z ⌋ᶜ .equiv-proof (κₐ Z) .fst .snd

  ≃Ab+ : (A : Ab+) → ⌈ ⌈ take+ ⌋ᶜ ⌋ ≃ ⌈ ⌈ A ⌋ᶜ ⌋
  ≃Ab+ A = isoToEquiv (record {
    fun = f⁺ take+ A .fst ;
    inv = f⁺ A take+ .fst ;
    rightInv = λ x → cong (λ f → fst f x)
      (unicityUPCoprojId A (∘ₐ ⌈ A ⌋ᶜ ⌈ take+ ⌋ᶜ ⌈ A ⌋ᶜ (f⁺ A take+) (f⁺ take+ A))
      (sym (assocMorph X ⌈ A ⌋ᶜ ⌈ take+ ⌋ᶜ ⌈ A ⌋ᶜ (κₐ₁ A) (f⁺ A take+) (f⁺ take+ A))
        ∙ cong (λ a → ∘ₐ X ⌈ take+ ⌋ᶜ ⌈ A ⌋ᶜ (fst a) (f⁺ take+ A)) (lemmaf⁺ take+ A)
        ∙ cong fst (lemmaf⁺ A take+))
      (sym (assocMorph Y ⌈ A ⌋ᶜ ⌈ take+ ⌋ᶜ ⌈ A ⌋ᶜ (κₐ₂ A) (f⁺ A take+) (f⁺ take+ A))
        ∙ cong (λ a → ∘ₐ Y ⌈ take+ ⌋ᶜ ⌈ A ⌋ᶜ (snd a) (f⁺ take+ A)) (lemmaf⁺ take+ A)
        ∙ cong snd (lemmaf⁺ A take+))) ;
    leftInv = λ x → cong (λ f → fst f x)
      (unicityUPCoprojId take+ (∘ₐ ⌈ take+ ⌋ᶜ ⌈ A ⌋ᶜ ⌈ take+ ⌋ᶜ (f⁺ take+ A) (f⁺ A take+))
      (sym (assocMorph X ⌈ take+ ⌋ᶜ ⌈ A ⌋ᶜ ⌈ take+ ⌋ᶜ (κₐ₁ take+) (f⁺ take+ A) (f⁺ A take+))
        ∙ cong (λ a → ∘ₐ X ⌈ A ⌋ᶜ ⌈ take+ ⌋ᶜ (fst a) (f⁺ A take+)) (lemmaf⁺ A take+)
        ∙ cong fst (lemmaf⁺ take+ A))
      (sym (assocMorph Y ⌈ take+ ⌋ᶜ ⌈ A ⌋ᶜ ⌈ take+ ⌋ᶜ (κₐ₂ take+) (f⁺ take+ A) (f⁺ A take+))
        ∙ cong (λ a → ∘ₐ Y ⌈ A ⌋ᶜ ⌈ take+ ⌋ᶜ (snd a)(f⁺ A take+)) (lemmaf⁺ A take+)
        ∙ cong snd (lemmaf⁺ take+ A)))})
    
  isContrCoprod : isContr Ab+
  isContrCoprod = take+ , λ A → Σ≡Prop (λ _ → isPropΠ (λ A → isPropIsEquiv _))
    (ΣPathTransport→PathΣ _ _ (uaₐ ab⊕c ⌈ A ⌋ᶜ (≃Ab+ A , f⁺ take+ A .snd) , ≡-×
    (→A≡ X ⌈ A ⌋ᶜ (fromPathP (funTypeTransp (λ _ → fst X) (λ X → X) (ua (≃Ab+ A)) (λ x → x , ∙ₐ Y))
      ∙ cong (λ x → transport (ua (≃Ab+ A)) ∘ (λ x → x , ∙ₐ Y) ∘ x) (funExt (λ x → transportRefl x))
      ∙ cong (λ x → transport (ua (≃Ab+ A)) ∘ x) (∘-idˡ _)
      ∙ cong (λ x → x ∘ (λ x → x , ∙ₐ Y)) (funExt (uaβ (≃Ab+ A)))
      ∙ cong (fst ∘ fst) (lemmaf⁺ A take+)))
    (→A≡ Y ⌈ A ⌋ᶜ (fromPathP (funTypeTransp (λ _ → fst Y) (λ X → X) (ua (≃Ab+ A)) (λ y → ∙ₐ X , y))
      ∙ cong (λ x → transport (ua (≃Ab+ A)) ∘ (λ y → ∙ₐ X , y) ∘ x) (funExt (λ x → transportRefl x))
      ∙ cong (λ x → transport (ua (≃Ab+ A)) ∘ x) (∘-idˡ _)
      ∙ cong (λ x → x ∘ (λ y → ∙ₐ X , y)) (funExt (uaβ (≃Ab+ A)))
      ∙ cong (fst ∘ snd) (lemmaf⁺ A take+))) ))

  -- Merging the product and coproduct structures

  take⊕ : Ab⊕
  take⊕ = ab⊕c , ((πc , univ×c) , (κc , univ+c)) , →A≡ ab⊕c ab⊕c (funExt (λ x → sym (decomp⊕ x)))

  module _ (A : Ab⊕) where

    equalEquiv+× : f⁺ take+ (Ab⊕→Ab+ A) ≡ fˣ take× (Ab⊕→Ab× A)
    equalEquiv+× = sym (unicityUPCoproj take+ ⌈ A ⌋ᵇ (κᵇ₁ A) (κᵇ₂ A) (⟨⟩ₚ ab⊕c (Ab⊕→Ab× A) πc₁ πc₂)
      (cong (λ a → ∘ₐ X ab⊕c ⌈ A ⌋ᵇ a (⟨⟩ₚ ab⊕c (Ab⊕→Ab× A) πc₁ πc₂))
        ((sym (rUnitMorph X ab⊕c (κc₁))) ∙ cong (λ a → ∘ₐ X ab⊕c ab⊕c κc₁ a) (sym (take⊕ .snd .snd)) ∙
        projCopairingl take+ ab⊕c (⟨⟩ₚ X take× (idₐ X) (0ₐ X Y)) (⟨⟩ₚ Y take× (0ₐ Y X) (idₐ Y))) ∙
        pairingPreComp X ab⊕c (Ab⊕→Ab× A) (⟨⟩ₚ X take× (idₐ X) (0ₐ X Y)) πc₁ πc₂ ∙
        cong₂ (λ a b → ⟨⟩ₚ X (Ab⊕→Ab× A) a b)
          (projPairingl X take× (idₐ X) (0ₐ X Y)) (projPairingr X take× (idₐ X) (0ₐ X Y)) ∙ is⟨⟩κ₁ A)
      (cong (λ a → ∘ₐ Y ab⊕c ⌈ A ⌋ᵇ a (⟨⟩ₚ ab⊕c (Ab⊕→Ab× A) πc₁ πc₂))
        ((sym (rUnitMorph Y ab⊕c (κc₂))) ∙ cong (λ a → ∘ₐ Y ab⊕c ab⊕c κc₂ a) (sym (take⊕ .snd .snd)) ∙
        projCopairingr take+ ab⊕c (⟨⟩ₚ X take× (idₐ X) (0ₐ X Y)) (⟨⟩ₚ Y take× (0ₐ Y X) (idₐ Y))) ∙
        pairingPreComp Y ab⊕c (Ab⊕→Ab× A) (⟨⟩ₚ Y take× (0ₐ Y X) (idₐ Y)) πc₁ πc₂ ∙
        cong₂ (λ a b → ⟨⟩ₚ Y (Ab⊕→Ab× A) a b)
          (projPairingl Y take× (0ₐ Y X) (idₐ Y)) (projPairingr Y take× (0ₐ Y X) (idₐ Y)) ∙ is⟨⟩κ₂ A))

    ≡≃ₐ+× : PathP (λ _ → ab⊕c ≃ₐ ⌈ A ⌋ᵇ)
      (≃Ab+ (Ab⊕→Ab+ A) , f⁺ take+ (Ab⊕→Ab+ A) .snd)
      (≃Ab× (Ab⊕→Ab× A) , fˣ take× (Ab⊕→Ab× A) .snd)
    ≡≃ₐ+× = invEquiv (≡≃ₐ ab⊕c ⌈ A ⌋ᵇ
      (≃Ab+ (Ab⊕→Ab+ A) , f⁺ take+ (Ab⊕→Ab+ A) .snd)
      (≃Ab× (Ab⊕→Ab× A) , fˣ take× (Ab⊕→Ab× A) .snd)) .fst equalEquiv+×

    Pathₐ+ : ab⊕c ≡ ⌈ A ⌋ᵇ
    Pathₐ+ = uaₐ ab⊕c ⌈ A ⌋ᵇ (≃Ab+ (Ab⊕→Ab+ A) , f⁺ take+ (Ab⊕→Ab+ A) .snd)

    Pathₐ× : ab⊕c ≡ ⌈ A ⌋ᵇ
    Pathₐ× = uaₐ ab⊕c ⌈ A ⌋ᵇ (≃Ab× (Ab⊕→Ab× A) , fˣ take× (Ab⊕→Ab× A) .snd)
    
    ≡≡+× : PathP (λ _ → ab⊕c ≡ ⌈ A ⌋ᵇ) Pathₐ+ Pathₐ×
    ≡≡+× = cong (uaₐ ab⊕c ⌈ A ⌋ᵇ) ≡≃ₐ+×

    Pathₐ+κ : PathP (λ i → (X →ₐ Pathₐ+ i) × (Y →ₐ Pathₐ+ i)) κc (κᵇ₁ A , κᵇ₂ A)
    Pathₐ+κ = PathPΣ (PathPΣ (snd isContrCoprod (Ab⊕→Ab+ A)) .fst) .snd

    Pathₐ×π : PathP (λ i → (Pathₐ× i →ₐ X) × (Pathₐ× i →ₐ Y)) πc (πᵇ₁ A , πᵇ₂ A)
    Pathₐ×π = PathPΣ (PathPΣ (snd isContrProd (Ab⊕→Ab× A)) .fst) .snd

    Pathₐ×πu : PathP (λ i → Σ[ p ∈ ((Pathₐ× i →ₐ X) × (Pathₐ× i →ₐ Y))] (universal× (Pathₐ× i , p)))
      (take⊕ .snd .fst .fst)
      (A .snd .fst .fst)
    Pathₐ×πu = ΣPathPProp (λ p → isPropΠ (λ Z → isPropIsEquiv (distrib× (⌈ A ⌋ᵇ , p) Z))) Pathₐ×π

    Pathₐ×κ : PathP (λ i → (X →ₐ Pathₐ× i) × (Y →ₐ Pathₐ× i)) κc (κᵇ₁ A , κᵇ₂ A)
    Pathₐ×κ = subst (λ e → PathP (λ i → (X →ₐ e i) × (Y →ₐ e i)) κc (κᵇ₁ A , κᵇ₂ A)) ≡≡+× Pathₐ+κ

    Pathₐ×κu : PathP (λ i → Σ[ p ∈ ((X →ₐ Pathₐ× i) × (Y →ₐ Pathₐ× i))] (universal+ (Pathₐ× i , p)))
      (take⊕ .snd .fst .snd)
      (A .snd .fst .snd)
    Pathₐ×κu = ΣPathPProp (λ p → isPropΠ (λ Z → isPropIsEquiv (distrib+ (⌈ A ⌋ᵇ , p) Z))) Pathₐ×κ

-- The idea is to use as path between take⊕ and A the path of the equivalence as products and
-- construct the other paths above it

  isContr⊕ₐ : isContr Ab⊕
  isContr⊕ₐ = take⊕ , λ A → ΣPathP (Pathₐ× A , ΣPathPProp (λ p → isPropCompₚᶜ ⌈ A ⌋ᵇ p)
    (ΣPathP (Pathₐ×πu A , Pathₐ×κu A)))

_⊕ₐ_ : (X Y : AbGrp ℓ) → AbGrp ℓ
X ⊕ₐ Y = ab⊕c X Y

_⊕ₜ_ : (X Y : AbGrp ℓ) → Ab⊕ X Y
X ⊕ₜ Y = take⊕ X Y

-- Redefinition of the basic properties but with only X and Y as parameters

module _ (X Y : AbGrp ℓ) where

  π₁ : X ⊕ₐ Y →ₐ X
  π₁ = πᵇ₁ X Y (X ⊕ₜ Y)

  π₂ : X ⊕ₐ Y →ₐ Y
  π₂ = πᵇ₂ X Y (X ⊕ₜ Y)

  κ₁ : X →ₐ X ⊕ₐ Y
  κ₁ = κᵇ₁ X Y (X ⊕ₜ Y)

  κ₂ : Y →ₐ X ⊕ₐ Y
  κ₂ = κᵇ₂ X Y (X ⊕ₜ Y)

⟨⟩ᵇ : (A X Y : AbGrp ℓ) → (A →ₐ X) → (A →ₐ Y) → A →ₐ X ⊕ₐ Y
⟨⟩ᵇ A X Y = ⟨⟩ₚ X Y A (take× X Y)
  
π⟨⟩l : (A X Y : AbGrp ℓ) → (f : A →ₐ X) → (g : A →ₐ Y) →
  ∘ₐ A (X ⊕ₐ Y) X (⟨⟩ᵇ A X Y f g) (π₁ X Y) ≡ f
π⟨⟩l A X Y = projPairingl X Y A (take× X Y)

π⟨⟩r : (A X Y : AbGrp ℓ) → (f : A →ₐ X) → (g : A →ₐ Y) →
  ∘ₐ A (X ⊕ₐ Y) Y (⟨⟩ᵇ A X Y f g) (π₂ X Y) ≡ g
π⟨⟩r A X Y = projPairingr X Y A (take× X Y)

∃!UPπ : (A X Y : AbGrp ℓ) → (f : A →ₐ X) → (g : A →ₐ Y) → (h : A →ₐ X ⊕ₐ Y) →
  ∘ₐ A (X ⊕ₐ Y) X h (π₁ X Y) ≡ f → ∘ₐ A (X ⊕ₐ Y) Y h (π₂ X Y) ≡ g →
  h ≡ ⟨⟩ᵇ A X Y f g
∃!UPπ A X Y = unicityUPProj X Y A (take× X Y)

∃!UPπId : (X Y : AbGrp ℓ) → (f : X ⊕ₐ Y →ₐ X ⊕ₐ Y) →
  ∘ₐ (X ⊕ₐ Y) (X ⊕ₐ Y) X f (π₁ X Y) ≡ π₁ X Y → ∘ₐ (X ⊕ₐ Y) (X ⊕ₐ Y) Y f (π₂ X Y) ≡ π₂ X Y →
  f ≡ idₐ (X ⊕ₐ Y)
∃!UPπId X Y = unicityUPProjId X Y (take× X Y)

⟨⟩∘⃖ : (A B X Y : AbGrp ℓ) → (f : A →ₐ B) → (g : B →ₐ X) (h : B →ₐ Y) →
  ∘ₐ A B (X ⊕ₐ Y) f (⟨⟩ᵇ B X Y g h) ≡ ⟨⟩ᵇ A X Y (∘ₐ A B X f g) (∘ₐ A B Y f h)
⟨⟩∘⃖ A B X Y = pairingPreComp X Y A B (take× X Y)

[]ᵇ : (X Y A : AbGrp ℓ) → (X →ₐ A) → (Y →ₐ A) → X ⊕ₐ Y →ₐ A
[]ᵇ X Y A = []ᶜ X Y (take+ X Y) A

κ[]l : (X Y A : AbGrp ℓ) → (f : X →ₐ A) → (g : Y →ₐ A) → ∘ₐ X (X ⊕ₐ Y) A (κ₁ X Y) ([]ᵇ X Y A f g) ≡ f
κ[]l X Y A = projCopairingl X Y (take+ X Y) A

κ[]r : (X Y A : AbGrp ℓ) → (f : X →ₐ A) → (g : Y →ₐ A) → ∘ₐ Y (X ⊕ₐ Y) A (κ₂ X Y) ([]ᵇ X Y A f g) ≡ g
κ[]r X Y A = projCopairingr X Y (take+ X Y) A

∃!UPκ : (X Y A : AbGrp ℓ) → (f : X →ₐ A) → (g : Y →ₐ A) → (h : X ⊕ₐ Y →ₐ A) →
  ∘ₐ X (X ⊕ₐ Y) A (κ₁ X Y) h ≡ f → ∘ₐ Y (X ⊕ₐ Y) A (κ₂ X Y) h ≡ g →
  h ≡ []ᵇ X Y A f g
∃!UPκ X Y A = unicityUPCoproj X Y (take+ X Y) A

∃!UPκId : (X Y : AbGrp ℓ) (f : X ⊕ₐ Y →ₐ X ⊕ₐ Y) →
  ∘ₐ X (X ⊕ₐ Y) (X ⊕ₐ Y) (κ₁ X Y) f ≡ κ₁ X Y → ∘ₐ Y (X ⊕ₐ Y) (X ⊕ₐ Y) (κ₂ X Y) f ≡ κ₂ X Y →
  f ≡ idₐ (X ⊕ₐ Y)
∃!UPκId X Y = unicityUPCoprojId X Y (take+ X Y)

[]∘⃗ : (X Y A B : AbGrp ℓ) → (f : X →ₐ A) (g : Y →ₐ A) → (h : A →ₐ B) →
  ∘ₐ (X ⊕ₐ Y) A B ([]ᵇ X Y A f g) h ≡ []ᵇ X Y B (∘ₐ X A B f h) (∘ₐ Y A B g h)
[]∘⃗ X Y A B = copairingPostComp X Y (take+ X Y) A B

⟨⟩ᵇκ₁ : (X Y : AbGrp ℓ) → ⟨⟩ᵇ X X Y (idₐ X) (0ₐ X Y) ≡ κ₁ X Y
⟨⟩ᵇκ₁ X Y = is⟨⟩κ₁ X Y (X ⊕ₜ Y)

⟨⟩ᵇκ₂ : (X Y : AbGrp ℓ) → ⟨⟩ᵇ Y X Y (0ₐ Y X) (idₐ Y) ≡ κ₂ X Y
⟨⟩ᵇκ₂ X Y = is⟨⟩κ₂ X Y (X ⊕ₜ Y)

κ₁∘π₁ : (X Y : AbGrp ℓ) → ∘ₐ X (X ⊕ₐ Y) X (κ₁ X Y) (π₁ X Y) ≡ idₐ X
κ₁∘π₁ X Y =  cong (λ a → ∘ₐ X (X ⊕ₐ Y) X a (π₁ X Y)) (sym (⟨⟩ᵇκ₁ X Y)) ∙
  π⟨⟩l X X Y (idₐ X) (0ₐ X Y)

κ₁∘π₂ : (X Y : AbGrp ℓ) → ∘ₐ X (X ⊕ₐ Y) Y (κ₁ X Y) (π₂ X Y) ≡ 0ₐ X Y
κ₁∘π₂ X Y =  cong (λ a → ∘ₐ X (X ⊕ₐ Y) Y a (π₂ X Y)) (sym (⟨⟩ᵇκ₁ X Y)) ∙
  π⟨⟩r X X Y (idₐ X) (0ₐ X Y)

κ₂∘π₁ : (X Y : AbGrp ℓ) → ∘ₐ Y (X ⊕ₐ Y) X (κ₂ X Y) (π₁ X Y) ≡ 0ₐ Y X
κ₂∘π₁ X Y =  cong (λ a → ∘ₐ Y (X ⊕ₐ Y) X a (π₁ X Y)) (sym (⟨⟩ᵇκ₂ X Y)) ∙
  π⟨⟩l Y X Y (0ₐ Y X) (idₐ Y)

κ₂∘π₂ : (X Y : AbGrp ℓ) → ∘ₐ Y (X ⊕ₐ Y) Y (κ₂ X Y) (π₂ X Y) ≡ idₐ Y
κ₂∘π₂ X Y =  cong (λ a → ∘ₐ Y (X ⊕ₐ Y) Y a (π₂ X Y)) (sym (⟨⟩ᵇκ₂ X Y)) ∙
  π⟨⟩r Y X Y (0ₐ Y X) (idₐ Y)

