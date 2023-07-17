open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.FinSet.Induction
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to sumrec ; elim to sumelim)
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Foundations.Everything
open import Cubical.Functions.Embedding
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Cubical.Relation.Nullary

module Sign.Orientation.FinPart where

private
  variable
    ℓ ℓ' : Level

ℙᵈ : Type ℓ → Type ℓ
ℙᵈ X = X → Bool

ℙᵈᵢ : (n : ℕ) → Type ℓ → Type ℓ
ℙᵈᵢ n X = Σ[ P ∈ ℙᵈ X ] ∥ (fiber P true) ≃ Fin n ∥₁

isFinℙᵈ : (X : Type ℓ) → isFinSet X → isFinSet (ℙᵈ X)
isFinℙᵈ X isFin = isFinSet→ (X , isFin) (Bool , isFinSetBool)

lemma : {k : ℕ} → (x : Fin (suc k)) → (x ≡ fzero) ⊎ (Σ[ y ∈ Fin k ] (inr y ≡ x))
lemma fzero = inl refl
lemma (fsuc x) = inr (x , refl)

module _
  (k n : ℕ)
  ((P , bl) : ℙᵈᵢ (suc k) (Fin (suc n)))
  where

  isTotProp : {x : Fin (suc n)} →
    (p q : (x ≡ fzero) ⊎ (Σ[ y ∈ Fin n ] (fsuc y ≡ x))) → p ≡ q
  isTotProp {x} (inl p) (inl q) = cong inl (isFinSet→isSet isFinSetFin x fzero p q)
  isTotProp (inl p) (inr (a , q)) = zrec (lower (Cubical.Data.Sum.⊎Path.encode (fzero) (fsuc a)
    (p ⁻¹ ∙ q ⁻¹)))
  isTotProp (inr (a , p)) (inl q) = zrec (lower (Cubical.Data.Sum.⊎Path.encode (fzero) (fsuc a)
    (q ⁻¹ ∙ p ⁻¹)))
  isTotProp {x} (inr (a , p)) (inr (b , q)) = cong inr
    (Σ≡Prop (λ z → isFinSet→isSet isFinSetFin (fsuc z) x)
    (isEmbedding→Inj isEmbedding-inr a b (p ∙ q ⁻¹)))

  decomp→equiv1lemma : (fiber P true ≃ Fin (suc k)) → (p : P fzero ≡ true) →
    Σ[ e ∈ (fiber P true ≃ Fin (suc k))] (e .fst (fzero , p) ≡ fzero)
  decomp→equiv1lemma e p .fst .fst (fzero , q) =
    e .fst (e .snd .equiv-proof fzero .fst .fst)
  decomp→equiv1lemma e p .fst .fst (fsuc x , q) = sumrec (λ _ → e .fst (fzero , p))
    inr (e .fst (fsuc x , q))
  decomp→equiv1lemma e p .fst .snd .equiv-proof fzero .fst = (fzero , p) ,
    e .snd .equiv-proof fzero .fst .snd
  decomp→equiv1lemma e p .fst .snd .equiv-proof fzero .snd ((fzero , q) , r) =
    Σ≡Prop (λ x → isSetFin (fst (decomp→equiv1lemma e p .fst) x) fzero)
    (Σ≡Prop (λ x → isSetBool (P x) true) refl)
  decomp→equiv1lemma e p .fst .snd .equiv-proof fzero .snd ((fsuc x , q) , r) =
    zrec (sumrec {C = ⊥}
    (λ eq → sumrec (λ s → lower (Cubical.Data.Sum.⊎Path.encode _ _
      (cong (fst ∘ fst) (isContr→isProp (e .snd .equiv-proof fzero)
        ((fzero , p) , s) ((fsuc x , q), eq)))))
      (λ (α , β) → lower (Cubical.Data.Sum.⊎Path.encode _ _
      (β ∙ cong (sumrec (λ _ → e .fst (fzero , p)) inr) (sym eq) ∙ r)))
      (lemma (e .fst (fzero , p))))
    (λ (y , eq) → lower (Cubical.Data.Sum.⊎Path.encode _ _
      (cong (sumrec (λ _ → e .fst (fzero , p)) inr) eq ∙ r)))
    (lemma (e .fst (inr x , q))))
  decomp→equiv1lemma e p .fst .snd .equiv-proof (fsuc x) .fst = sumrec
    (λ y → e .snd .equiv-proof fzero .fst .fst , sumrec
      (λ α → zrec (lower (Cubical.Data.Sum.⊎Path.encode _ _ (sym (e .snd .equiv-proof fzero .fst .snd)
        ∙ cong (e .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = e .snd .equiv-proof fzero .fst .fst}
        {v = e .snd .equiv-proof (fsuc x) .fst .fst} (α ∙ sym y))
        ∙ e .snd .equiv-proof (fsuc x) .fst .snd))))
      (λ (α , β) → cong (decomp→equiv1lemma e p .fst .fst)
        (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = e .snd .equiv-proof fzero .fst .fst}
        {v = fsuc α , cong P β ∙ e .snd .equiv-proof fzero .fst .fst .snd} (sym β))
        ∙ cong (λ a → sumrec (λ _ → e .fst (fzero , p)) inr (e .fst a))
        (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = fsuc α , cong P β ∙ e .snd .equiv-proof fzero .fst .fst .snd}
        {v = e .snd .equiv-proof fzero .fst .fst} β)
        ∙ cong (sumrec (λ _ → e .fst (fzero , p)) inr) (e .snd .equiv-proof fzero .fst .snd)
        ∙ cong (e .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true) {u = fzero , p}
        {v = e .snd .equiv-proof (fsuc x) .fst .fst} (sym y))
        ∙ e .snd .equiv-proof (fsuc x) .fst .snd)
      (lemma {k = n} (e .snd .equiv-proof fzero .fst .fst .fst)))
    (λ (y , eq) → e .snd .equiv-proof (fsuc x) .fst .fst ,
      cong (decomp→equiv1lemma e p .fst .fst)
      (sym (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
      {u = (fsuc y) , cong P eq ∙ e .snd .equiv-proof (fsuc x) .fst .fst .snd}
      {v = e .snd .equiv-proof (fsuc x) .fst .fst} eq)) ∙ cong (λ α →
      sumrec (λ _ → e .fst (fzero , p)) inr (e .fst α))
      (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
      {u = fsuc y , cong P eq ∙ e .snd .equiv-proof (fsuc x) . fst .fst .snd}
      {v = e .snd .equiv-proof (fsuc x) .fst .fst} eq)
      ∙ cong (sumrec (λ _ → e .fst (fzero , p)) inr) (e .snd .equiv-proof (fsuc x) .fst .snd))
    (lemma {k = n} (e .snd .equiv-proof (fsuc x) .fst .fst .fst))
  decomp→equiv1lemma e p .fst .snd .equiv-proof (fsuc x) .snd ((fzero , q) , r) =
    Σ≡Prop (λ x₁ → isSetFin (fst (decomp→equiv1lemma e p .fst) x₁) (fsuc x))
      (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
      (sumrec
    (λ γ → cong (fst ∘ fst) (cong (λ a → sumrec
      (λ y → e .snd .equiv-proof fzero .fst .fst ,
      sumrec
      (λ α → zrec (lower (Cubical.Data.Sum.⊎Path.encode _ _ (sym (e .snd .equiv-proof fzero .fst .snd)
      ∙ cong (e .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = e .snd .equiv-proof fzero .fst .fst}
        {v = e .snd .equiv-proof (fsuc x) .fst .fst} (α ∙ sym y))
        ∙ e .snd .equiv-proof (fsuc x) .fst .snd))))
      (λ (α , β) → cong (decomp→equiv1lemma e p .fst .fst)
       (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = e .snd .equiv-proof fzero .fst .fst}
        {v = fsuc α , cong P β ∙ e .snd .equiv-proof fzero .fst .fst .snd} (sym β))
        ∙ cong (λ a → sumrec (λ _ → e .fst (fzero , p)) inr (e .fst a))
        (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = fsuc α , cong P β ∙ e .snd .equiv-proof fzero .fst .fst .snd}
        {v = e .snd .equiv-proof fzero .fst .fst} β)
        ∙ cong (sumrec (λ _ → e .fst (fzero , p)) inr) (e .snd .equiv-proof fzero .fst .snd)
        ∙ cong (e .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true) {u = fzero , p}
        {v = e .snd .equiv-proof (fsuc x) .fst .fst} (sym y))
        ∙ e .snd .equiv-proof (fsuc x) .fst .snd
        )
      (lemma {k = n} (e .snd .equiv-proof fzero .fst .fst .fst)))
    (λ (y , eq) → e .snd .equiv-proof (fsuc x) .fst .fst ,
     cong (decomp→equiv1lemma e p .fst .fst)
      (sym (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
         {u = (fsuc y) , cong P eq ∙ e .snd .equiv-proof (fsuc x) .fst .fst .snd}
      {v = e .snd .equiv-proof (fsuc x) .fst .fst} eq)) ∙ cong (λ α →
      sumrec (λ _ → e .fst (fzero , p)) inr (e .fst α))
      (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
            {u = fsuc y , cong P eq ∙ e .snd .equiv-proof (fsuc x) . fst .fst .snd}
      {v = e .snd .equiv-proof (fsuc x) .fst .fst} eq)
      ∙ cong (sumrec (λ _ → e .fst (fzero , p)) inr) (e .snd .equiv-proof (fsuc x) .fst .snd))
      a) (isTotProp (lemma {k = n} (e .snd .equiv-proof (fsuc x) .fst .fst .fst)) (inl γ)))
      ∙ cong fst (isEmbedding→Inj (isEquiv→isEmbedding (e .snd)) (e .snd .equiv-proof fzero .fst .fst)
      (fzero , p) (r ∙ sym (e .snd .equiv-proof (fsuc x) .fst .snd)
      ∙ cong (e .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
      {u = e .snd .equiv-proof (fsuc x) .fst .fst} {v = fzero , p}  γ))))
      (λ (z₁ , eq₁) → zrec (lower (Cubical.Data.Sum.⊎Path.encode fzero (fsuc x)
        (sym (e .snd .equiv-proof fzero .fst .snd)
        ∙ r ∙ sym (e .snd .equiv-proof (fsuc x) .fst .snd)
        ∙ e .snd .equiv-proof (fsuc x) .fst .snd))))
    (lemma {k = n} (e .snd .equiv-proof (fsuc x) .fst .fst .fst))))
  decomp→equiv1lemma e p .fst .snd .equiv-proof (fsuc x) .snd ((inr y , q) , r) = Σ≡Prop
    (λ x₁ → isSetFin (fst (decomp→equiv1lemma e p .fst) x₁) (fsuc x)) (
    Σ≡Prop (λ x₁ → isSetBool (P x₁) true) (
    sumrec
      (λ eq₁ → cong (fst ∘ fst) (cong (λ a → sumrec
      (λ y → e .snd .equiv-proof fzero .fst .fst ,
      sumrec
      (λ α → zrec (lower (Cubical.Data.Sum.⊎Path.encode _ _ (sym (e .snd .equiv-proof fzero .fst .snd)
      ∙ cong (e .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = e .snd .equiv-proof fzero .fst .fst}
        {v = e .snd .equiv-proof (fsuc x) .fst .fst} (α ∙ sym y))
        ∙ e .snd .equiv-proof (fsuc x) .fst .snd))))
      (λ (α , β) → cong (decomp→equiv1lemma e p .fst .fst)
       (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = e .snd .equiv-proof fzero .fst .fst}
        {v = fsuc α , cong P β ∙ e .snd .equiv-proof fzero .fst .fst .snd} (sym β))
        ∙ cong (λ a → sumrec (λ _ → e .fst (fzero , p)) inr (e .fst a))
        (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = fsuc α , cong P β ∙ e .snd .equiv-proof fzero .fst .fst .snd}
        {v = e .snd .equiv-proof fzero .fst .fst} β)
        ∙ cong (sumrec (λ _ → e .fst (fzero , p)) inr) (e .snd .equiv-proof fzero .fst .snd)
        ∙ cong (e .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true) {u = fzero , p}
        {v = e .snd .equiv-proof (fsuc x) .fst .fst} (sym y))
        ∙ e .snd .equiv-proof (fsuc x) .fst .snd
        )
      (lemma {k = n} (e .snd .equiv-proof fzero .fst .fst .fst)))
    (λ (y , eq) → e .snd .equiv-proof (fsuc x) .fst .fst ,
     cong (decomp→equiv1lemma e p .fst .fst)
      (sym (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
         {u = (fsuc y) , cong P eq ∙ e .snd .equiv-proof (fsuc x) .fst .fst .snd}
      {v = e .snd .equiv-proof (fsuc x) .fst .fst} eq)) ∙ cong (λ α →
      sumrec (λ _ → e .fst (fzero , p)) inr (e .fst α))
      (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
            {u = fsuc y , cong P eq ∙ e .snd .equiv-proof (fsuc x) . fst .fst .snd}
      {v = e .snd .equiv-proof (fsuc x) .fst .fst} eq)
      ∙ cong (sumrec (λ _ → e .fst (fzero , p)) inr) (e .snd .equiv-proof (fsuc x) .fst .snd))
      a) (isTotProp (lemma {k = n} (e .snd .equiv-proof (fsuc x) .fst .fst .fst)) (inl eq₁)))
      ∙ sumrec
        (λ α → cong fst (isEmbedding→Inj (isEquiv→isEmbedding (e .snd))
        (e .snd .equiv-proof fzero .fst .fst) (fsuc y , q)
        (e .snd .equiv-proof fzero .fst .snd ∙ sym α)))
        (λ (β , γ) → zrec (lower (Cubical.Data.Sum.⊎Path.encode fzero (fsuc y)
        (cong fst (isEmbedding→Inj (isEquiv→isEmbedding (e .snd))
        (fzero , p) (fsuc y , q)
        (cong (e .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true) {u = (fzero , p)}
        {v = (e .snd .equiv-proof (fsuc x) .fst .fst)} (sym eq₁))
        ∙ (e .snd .equiv-proof (fsuc x) .fst .snd ∙
        sym r ∙ sym (cong (sumrec (λ _ → e .fst (fzero , p)) inr) γ) ∙ γ)))))))
        (lemma (e .fst (fsuc y , q))))
      (λ (z₁ , eq₁) → cong (fst ∘ fst) (cong (λ a → sumrec
      (λ y → e .snd .equiv-proof fzero .fst .fst ,
      sumrec
      (λ α → zrec (lower (Cubical.Data.Sum.⊎Path.encode _ _ (sym (e .snd .equiv-proof fzero .fst .snd)
      ∙ cong (e .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = e .snd .equiv-proof fzero .fst .fst}
        {v = e .snd .equiv-proof (fsuc x) .fst .fst} (α ∙ sym y))
        ∙ e .snd .equiv-proof (fsuc x) .fst .snd))))
      (λ (α , β) → cong (decomp→equiv1lemma e p .fst .fst)
       (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = e .snd .equiv-proof fzero .fst .fst}
        {v = fsuc α , cong P β ∙ e .snd .equiv-proof fzero .fst .fst .snd} (sym β))
        ∙ cong (λ a → sumrec (λ _ → e .fst (fzero , p)) inr (e .fst a))
        (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
        {u = fsuc α , cong P β ∙ e .snd .equiv-proof fzero .fst .fst .snd}
        {v = e .snd .equiv-proof fzero .fst .fst} β)
        ∙ cong (sumrec (λ _ → e .fst (fzero , p)) inr) (e .snd .equiv-proof fzero .fst .snd)
        ∙ cong (e .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true) {u = fzero , p}
        {v = e .snd .equiv-proof (fsuc x) .fst .fst} (sym y))
        ∙ e .snd .equiv-proof (fsuc x) .fst .snd
        )
      (lemma {k = n} (e .snd .equiv-proof fzero .fst .fst .fst)))
    (λ (y , eq) → e .snd .equiv-proof (fsuc x) .fst .fst ,
     cong (decomp→equiv1lemma e p .fst .fst)
      (sym (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
         {u = (fsuc y) , cong P eq ∙ e .snd .equiv-proof (fsuc x) .fst .fst .snd}
      {v = e .snd .equiv-proof (fsuc x) .fst .fst} eq)) ∙ cong (λ α →
      sumrec (λ _ → e .fst (fzero , p)) inr (e .fst α))
      (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
            {u = fsuc y , cong P eq ∙ e .snd .equiv-proof (fsuc x) . fst .fst .snd}
      {v = e .snd .equiv-proof (fsuc x) .fst .fst} eq)
      ∙ cong (sumrec (λ _ → e .fst (fzero , p)) inr) (e .snd .equiv-proof (fsuc x) .fst .snd))
      a) (isTotProp (lemma {k = n} (e .snd .equiv-proof (fsuc x) .fst .fst .fst)) (inr (z₁ , eq₁))))
      ∙ sumrec
        (λ α → zrec (lower (Cubical.Data.Sum.⊎Path.encode (fsuc z₁) fzero
        (eq₁ ∙ cong (fst ∘ fst) (e .snd .equiv-proof (fsuc x) .snd ((fzero , p) , sym(
          sym r ∙ cong (λ a → sumrec (λ _ → e .fst (fzero , p)) inr a) α)))))))
      (λ (β , γ) → cong fst (isEmbedding→Inj (isEquiv→isEmbedding (e .snd))
        (e .snd .equiv-proof (fsuc x) .fst .fst) (fsuc y , q)
        (e .snd .equiv-proof (fsuc x) .fst .snd ∙
        sym (γ ⁻¹ ∙ cong (λ a → sumrec (λ _ → e .fst (fzero , p)) inr a) γ ∙ r))))
        (lemma (e .fst (fsuc y , q))))
    (lemma {k = n} (e .snd .equiv-proof (fsuc x) .fst .fst .fst))))
  decomp→equiv1lemma e p .snd = e .snd .equiv-proof fzero .fst .snd

lemma3 : (k n : ℕ) → ((P , bl) : ℙᵈᵢ (suc k) (Fin (suc n))) →
  (eq : P fzero ≡ true) →
  (e : (Σ[ e ∈ (fiber P true ≃ Fin (suc k))] (e .fst (fzero , eq) ≡ fzero))) →
  (x : fiber (P ∘ inr) true) → Σ[ y ∈ Fin k ] (fsuc y ≡ e .fst .fst (inr (x .fst) , x .snd))
lemma3 k n (P , bl) eq (e , e∙) (x , eq') = sumrec
  {C = Σ[ y ∈ Fin k ] (fsuc y ≡ e .fst (inr x , eq'))}
  (λ x₁ → zrec (lower (Cubical.Data.Sum.⊎Path.encode fzero (fsuc x) (cong (fst ∘ fst)
    (isContr→isProp (e .snd .equiv-proof fzero) ((fzero , eq) , e∙) ((fsuc x , eq') , x₁))))))
  (λ (x₂ , p) → x₂ , p)
  (lemma (e .fst (inr x , eq')))

lemma4 : (k n : ℕ) → ((P , bl) : ℙᵈᵢ (suc k) (Fin (suc n))) →
  (eq : P (fzero) ≡ true) →
  (e : (Σ[ e ∈ (fiber P true ≃ Fin (suc k))] (e .fst (fzero , eq) ≡ fzero))) →
  (x : Fin k) → Σ[ y ∈ fiber (P ∘ inr) true ] (fsuc x ≡ e .fst .fst (inr (y .fst) , y .snd))
lemma4 k n (P , bl) eq (e , e∙) x = sumrec
  {C = Σ[ y ∈ fiber (P ∘ inr) true ] (fsuc x ≡ e .fst (inr (y .fst) , y .snd))}
  (λ eq₂ → zrec (lower (Cubical.Data.Sum.⊎Path.encode (fsuc x) (fzero)
    (sym (e .snd .equiv-proof (fsuc x) .fst .snd)
    ∙ cong (e .fst) (Σ≡Prop (λ z → isSetBool _ _) {u = e .snd .equiv-proof (fsuc x)
    .fst .fst} {v = (fzero , eq)} eq₂) ∙ e∙))))
  (λ (y , eq₂) → (y , cong P eq₂ ∙ e .snd .equiv-proof (fsuc x) .fst .fst .snd) ,
  e .snd .equiv-proof (fsuc x) .fst .snd ⁻¹ ∙ cong (fst e)
    (Σ≡Prop (λ a → isSetBool (P a) true) (sym eq₂)))
  (lemma {k = n} (e .snd .equiv-proof (fsuc x) .fst .fst .fst))

decomp→equiv1 : (k n : ℕ) → ((P , bl) : ℙᵈᵢ (suc k) (Fin (suc n))) →
  (fiber P true ≃ Fin (suc k)) → P fzero ≡ true → fiber (P ∘ inr) true ≃ Fin k
decomp→equiv1 k n (P , bl) e eq .fst (x , y) = lemma3 k n (P , bl) eq (e' , e'≡) (x , y) .fst
  where
  e' : fiber P true ≃ Fin (suc k)
  e' = fst (decomp→equiv1lemma k n (P , bl) e eq)
  e'≡ : e' .fst (fzero , eq) ≡ fzero
  e'≡ = snd (decomp→equiv1lemma k n (P , bl) e eq)
decomp→equiv1 k n (P , bl) e eq .snd .equiv-proof y .fst =
  lemma4 k n (P , bl) eq (e' , e'≡) y .fst ,
  isEmbedding→Inj isEmbedding-inr _ _
  (lemma3 k n (P , bl) eq (e' , e'≡) (lemma4 k n (P , bl) eq (e' , e'≡) y .fst) .snd
  ∙ sym (lemma4 k n (P , bl) eq (e' , e'≡) y .snd))
  where
  e' : fiber P true ≃ Fin (suc k)
  e' = fst (decomp→equiv1lemma k n (P , bl) e eq)
  e'≡ : e' .fst (fzero , eq) ≡ fzero
  e'≡ = snd (decomp→equiv1lemma k n (P , bl) e eq)
decomp→equiv1 k n (P , bl) e eq .snd .equiv-proof y .snd ((x , p), q)=
  Σ≡Prop (λ x₁ → isSetFin (fst (decomp→equiv1 k n (P , bl) e eq) x₁) y)
  (Σ≡Prop (λ x₁ → isSetBool ((P ∘ inr) x₁) true) (
  cong (λ a → lemma4 k n (P , bl) eq (e' , e'≡) a .fst .fst) (sym q)
  ∙ sym (isEmbedding→Inj isEmbedding-inr x (lemma4 k n (P , bl) eq (e' , e'≡)
  (lemma3 k n (P , bl) eq (e' , e'≡) (x , p) .fst) .fst .fst)
  (cong fst(
  isEmbedding→Inj (isEquiv→isEmbedding (e' .snd)) (fsuc x , p)
  (fsuc (lemma4 k n (P , bl) eq (e' , e'≡)
    (lemma3 k n (P , bl) eq (e' , e'≡) (x , p) .fst) .fst .fst) ,
    lemma4 k n (P , bl) eq (e' , e'≡) (lemma3 k n (P , bl) eq
    (e' , e'≡) (x , p) .fst) .fst .snd)
  (sym (lemma3 k n (P , bl) eq (e' , e'≡) (x , p) .snd)
  ∙ lemma4 k n (P , bl) eq (e' , e'≡)
  (lemma3 k n (P , bl) eq (e' , e'≡) (x , p) .fst) .snd))))))
  where
  e' : fiber P true ≃ Fin (suc k)
  e' = fst (decomp→equiv1lemma k n (P , bl) e eq)
  e'≡ : e' .fst (fzero , eq) ≡ fzero
  e'≡ = snd (decomp→equiv1lemma k n (P , bl) e eq)
  
decomp→equiv2 : (k n : ℕ) → ((P , bl) : ℙᵈᵢ (suc k) (Fin (suc n))) →
  (fiber P true ≃ Fin (suc k)) → P (fzero) ≡ false → fiber (P ∘ inr) true ≃ Fin (suc k)
decomp→equiv2 k n (P , bl) e eq .fst (x , y) = e .fst (inr x , y)
decomp→equiv2 k n (P , bl) e eq .snd .equiv-proof y =
  (lemma' (e .snd .equiv-proof y .fst .fst) .fst ,
    cong (λ a → fst e a) (lemma' (e .snd .equiv-proof y .fst .fst) .snd)
    ∙ e .snd .equiv-proof y .fst .snd) ,
  λ z → Σ≡Prop (λ p → isSetFin (fst (decomp→equiv2 k n (P , bl) e eq) p) y)
    (Σ≡Prop (λ x → isSetBool (P (inr x)) true)
    (isEmbedding→Inj isEmbedding-inr (lemma' (e .snd .equiv-proof y .fst .fst) .fst .fst)
      (z .fst .fst)
    (cong fst (lemma' (e .snd .equiv-proof y .fst .fst) .snd
    ∙ cong fst (e .snd .equiv-proof y .snd ((inr (z .fst .fst) , z .fst .snd) , z .snd))))))
  where
  lemma' : ((x , p) : fiber P true) → Σ[ y ∈ (fiber (P ∘ inr) true) ] ((inr (fst y), snd y) ≡ (x , p))
  lemma' (fzero , p) = zrec (true≢false (sym p ∙ eq))
  lemma' ((inr y) , p) = (y , p) , refl

decomp→ : (k n : ℕ) → ℙᵈᵢ (suc k) (Fin (suc n)) → ℙᵈᵢ (suc k) (Fin n) ⊎ ℙᵈᵢ k (Fin n)
decomp→ k n (P , bl) = sumelim
  (λ p → inr (P ∘ inr , proprec isPropPropTrunc (λ e → ∣ decomp→equiv1 k n (P , bl) e p ∣₁) bl))
  (λ p → inl (P ∘ inr , proprec isPropPropTrunc (λ e → ∣ decomp→equiv2 k n (P , bl) e p ∣₁) bl))
  (dichotomyBool (P fzero))

decomp←fun1→ : (k n : ℕ) → ℙᵈᵢ (suc k) (Fin n) → Fin (suc n) → Bool
decomp←fun1→ k n (P , bl) (inl x) = false
decomp←fun1→ k n (P , bl) (inr x) = P x

decomp←fun1≃ : (k n : ℕ) → ((P , bl) : ℙᵈᵢ (suc k) (Fin n)) →
  (e : (fiber P true ≃ Fin (suc k))) → fiber (decomp←fun1→ k n (P , bl)) true ≃ Fin (suc k)
decomp←fun1≃ k n (P , bl) e .fst (inl x , p) = zrec (false≢true p)
decomp←fun1≃ k n (P , bl) e .fst (inr x , p) = e .fst (x , p)
decomp←fun1≃ k n (P , bl) e .snd .equiv-proof y .fst = (inr (e .snd .equiv-proof y .fst .fst .fst),
  e .snd .equiv-proof y .fst .fst .snd) , e .snd .equiv-proof y .fst .snd
decomp←fun1≃ k n (P , bl) e .snd .equiv-proof y .snd ((fzero , p) , q) = zrec (false≢true p)
decomp←fun1≃ k n (P , bl) e .snd .equiv-proof y .snd ((fsuc x , p) , q) =
  Σ≡Prop (λ z → isSetFin (fst (decomp←fun1≃ k n (P , bl) e) z) y) (Σ≡Prop (λ z → isSetBool
    (decomp←fun1→ k n (P , bl) z) true)
  (cong (fsuc ∘ fst ∘ fst) (e .snd .equiv-proof y .snd ((x , p) , q))))

decomp←fun1 : (k n : ℕ) → ℙᵈᵢ (suc k) (Fin n) → ℙᵈᵢ (suc k) (Fin (suc n))
decomp←fun1 k n (P , bl) = decomp←fun1→ k n (P , bl) ,
  proprec isPropPropTrunc (λ e → ∣ decomp←fun1≃ k n (P , bl) e ∣₁) bl

decomp←fun2→ : (k n : ℕ) → ℙᵈᵢ k (Fin n) → (Fin (suc n)) → Bool
decomp←fun2→ k n (P , bl) (inl x) = true
decomp←fun2→ k n (P , bl) (inr x) = P x

decomp←fun2≃ : (k n : ℕ) → ((P , bl) : ℙᵈᵢ k (Fin n)) →
  (e : (fiber P true ≃ Fin k)) → fiber (decomp←fun2→ k n (P , bl)) true ≃ Fin (suc k)
decomp←fun2≃ k n (P , bl) e .fst (inl x , p) = fzero
decomp←fun2≃ k n (P , bl) e .fst (inr x , p) = inr (e .fst (x , p))
decomp←fun2≃ k n (P , bl) e .snd .equiv-proof (inl tt) .fst = (fzero , refl) , refl
decomp←fun2≃ k n (P , bl) e .snd .equiv-proof (inr y) .fst =
  (inr (e .snd .equiv-proof y .fst .fst .fst) , e .snd .equiv-proof y .fst .fst .snd) ,
  cong inr (e .snd .equiv-proof y .fst .snd)
decomp←fun2≃ k n (P , bl) e .snd .equiv-proof (inl tt) .snd ((fzero , p) , q) = Σ≡Prop
  (λ x → isSetFin (fst (decomp←fun2≃ k n (P , bl) e) x) fzero)
  (Σ≡Prop (λ x → isSetBool (decomp←fun2→ k n (P , bl) x) true) refl)
decomp←fun2≃ k n (P , bl) e .snd .equiv-proof (inr y) .snd ((fzero , p) , q) =
  zrec (lower (Cubical.Data.Sum.⊎Path.encode {ℓ = lzero} fzero (fsuc y) q))
decomp←fun2≃ k n (P , bl) e .snd .equiv-proof (inl tt) .snd ((inr x , p) , q) =
  zrec (lower (Cubical.Data.Sum.⊎Path.encode {ℓ = lzero} fzero (fsuc (e .fst (x , p))) (sym q)))
decomp←fun2≃ k n (P , bl) e .snd .equiv-proof (inr y) .snd ((inr x , p) , q) = Σ≡Prop
  (λ x → isSetFin (fst (decomp←fun2≃ k n (P , bl) e) x) (fsuc y))
  (Σ≡Prop (λ x → isSetBool (decomp←fun2→ k n (P , bl) x) true)
  (cong (fsuc ∘ fst ∘ fst) (e .snd .equiv-proof y .snd ((x , p) ,
  isEmbedding→Inj isEmbedding-inr (fst e (x , p)) y q))))

decomp←fun2 : (k n : ℕ) → ℙᵈᵢ k (Fin n) → ℙᵈᵢ (suc k) (Fin (suc n))
decomp←fun2 k n (P , bl) = decomp←fun2→ k n (P , bl) ,
  proprec isPropPropTrunc (λ e → ∣ decomp←fun2≃ k n (P , bl) e ∣₁) bl

decomp← : (k n : ℕ) → ℙᵈᵢ (suc k) (Fin n) ⊎ ℙᵈᵢ k (Fin n) → ℙᵈᵢ (suc k) (Fin (suc n))
decomp← k n (inl (P , bl)) = decomp←fun1 k n (P , bl)
decomp← k n (inr (P , bl)) = decomp←fun2 k n (P , bl)

decomp→inv : (k n : ℕ) → (F : ℙᵈᵢ (suc k) (Fin (suc n))) → decomp← k n (decomp→ k n F) ≡ F
decomp→inv k n (P , bl) = Σ≡Prop (λ _ → isPropPropTrunc) (funExt (sumelim
  (λ y → sumelim {C = λ z → decomp← k n (decomp→ k n (P , bl)) .fst (inl y) ≡ P (inl y)}
    (λ z → cong (λ a → decomp← k n (sumelim
      {C = λ (x : (P fzero ≡ true) ⊎ (P fzero ≡ false)) →
        ℙᵈᵢ (suc k) (Fin n) ⊎ ℙᵈᵢ k (Fin n)}
      (λ p → inr (P ∘ inr , proprec isPropPropTrunc (λ e → ∣ decomp→equiv1 k n (P , bl) e p ∣₁) bl))
      (λ p → inl (P ∘ inr , proprec isPropPropTrunc (λ e → ∣ decomp→equiv2 k n (P , bl) e p ∣₁) bl))
      a) .fst (inl y)) (isPropBoth (P fzero) (dichotomyBool (P fzero)) (inl z)) ∙ sym z)
    (λ z → cong (λ a → decomp← k n (sumelim
      {C = λ (x : (P fzero ≡ true) ⊎ (P fzero ≡ false)) →
        ℙᵈᵢ (suc k) (Fin n) ⊎ ℙᵈᵢ k (Fin n)}
      (λ p → inr (P ∘ inr , proprec isPropPropTrunc (λ e → ∣ decomp→equiv1 k n (P , bl) e p ∣₁) bl))
      (λ p → inl (P ∘ inr , proprec isPropPropTrunc (λ e → ∣ decomp→equiv2 k n (P , bl) e p ∣₁) bl))
      a) .fst (inl y)) (isPropBoth (P fzero) (dichotomyBool (P fzero)) (inr z)) ∙ sym z)
    (dichotomyBool (P fzero)))
  (λ y → sumelim {C = λ z → decomp← k n (decomp→ k n (P , bl)) .fst (inr y) ≡ P (inr y)}
    (λ z → cong (λ a → decomp← k n (sumelim
      {C = λ (x : (P fzero ≡ true) ⊎ (P fzero ≡ false)) →
        ℙᵈᵢ (suc k) (Fin n) ⊎ ℙᵈᵢ k (Fin n)}
      (λ p → inr (P ∘ inr , proprec isPropPropTrunc (λ e → ∣ decomp→equiv1 k n (P , bl) e p ∣₁) bl))
      (λ p → inl (P ∘ inr , proprec isPropPropTrunc (λ e → ∣ decomp→equiv2 k n (P , bl) e p ∣₁) bl))
      a) .fst (inr y)) (isPropBoth (P fzero) (dichotomyBool (P fzero)) (inl z)))
    (λ z → cong (λ a → decomp← k n (sumelim
      {C = λ (x : (P fzero ≡ true) ⊎ (P fzero ≡ false)) →
        ℙᵈᵢ (suc k) (Fin n) ⊎ ℙᵈᵢ k (Fin n)}
      (λ p → inr (P ∘ inr , proprec isPropPropTrunc (λ e → ∣ decomp→equiv1 k n (P , bl) e p ∣₁) bl))
      (λ p → inl (P ∘ inr , proprec isPropPropTrunc (λ e → ∣ decomp→equiv2 k n (P , bl) e p ∣₁) bl))
      a) .fst (inr y)) (isPropBoth (P fzero) (dichotomyBool (P fzero)) (inr z)) )
    (dichotomyBool (P fzero)))))
  where
  isPropBoth : ∀ b → isProp ((b ≡ true) ⊎ (b ≡ false))
  isPropBoth b (inl p) (inl q) = cong inl (isSetBool b true p q)
  isPropBoth b (inl p) (inr q) = zrec (true≢false (sym p ∙ q))
  isPropBoth b (inr p) (inl q) = zrec (true≢false (sym q ∙ p))
  isPropBoth b (inr p) (inr q) = cong inr (isSetBool b false p q)

decomp←inv : (k n : ℕ) → (F : ℙᵈᵢ (suc k) (Fin n) ⊎ ℙᵈᵢ k (Fin n)) → decomp→ k n (decomp← k n F) ≡ F
decomp←inv k n (inl (P , bl)) = cong inl (Σ≡Prop (λ _ → isPropPropTrunc) refl)
decomp←inv k n (inr (P , bl)) = cong inr (Σ≡Prop (λ _ → isPropPropTrunc) refl)

decomp≃ : (k n : ℕ) → ℙᵈᵢ (suc k) (Fin (suc n)) ≃ ℙᵈᵢ (suc k) (Fin n) ⊎ ℙᵈᵢ k (Fin n)
decomp≃ k n = isoToEquiv (record {
  fun = decomp→ k n ;
  inv = decomp← k n ;
  leftInv = decomp→inv k n ;
  rightInv = decomp←inv k n })

isFinOrdℙᵈᵢFin : (k n : ℕ) → (ℙᵈᵢ k (Fin n)) ≃ Fin (n choose k)
isFinOrdℙᵈᵢFin 0 n = isContr→Equiv
  (((λ _ → false) , ∣ uninhabEquiv (λ f → false≢true (f .snd)) (idfun _) ∣₁)
  , λ y → Σ≡Prop (λ _ → isPropPropTrunc)
    (funExt λ x → sumrec (λ p → zrec (proprec isProp⊥ (λ f → f .fst (x , p)) (y .snd))) sym
      (dichotomyBool (y .fst x))))
  isContrSumFin1
isFinOrdℙᵈᵢFin (suc k) 0 = uninhabEquiv
  (λ (P , bl) → proprec isProp⊥ (λ f → invEquiv f .fst (inl tt) .fst) bl) (idfun _)
isFinOrdℙᵈᵢFin (suc k) (suc n) = decomp≃ k n
  ∙ₑ ⊎-equiv (isFinOrdℙᵈᵢFin (suc k) n) (isFinOrdℙᵈᵢFin k n)
  ∙ₑ SumFin⊎≃ (n choose (suc k)) (n choose k)

ℙᵈᵢ≃→ : ∀ {ℓ ℓ'} → (X : Type ℓ) (Y : Type ℓ') (k : ℕ) → (X ≃ Y) → ℙᵈᵢ k Y → ℙᵈᵢ k X
ℙᵈᵢ≃→ X Y k e (P , bl) = P ∘ e .fst , proprec isPropPropTrunc
  (λ p → ∣ (λ (x , isfib) → p .fst (e .fst x , isfib)) ,
    record {equiv-proof = λ y →
      ((e .snd .equiv-proof (p .snd .equiv-proof y .fst .fst .fst) .fst .fst ,
      cong P (e .snd .equiv-proof (p .snd .equiv-proof y .fst .fst .fst) .fst .snd)
      ∙ p .snd .equiv-proof y .fst .fst .snd) ,
      cong (p .fst) (Σ≡Prop (λ x₁ → isSetBool (P x₁) true)
      {u = e .fst (e .snd .equiv-proof (p .snd .equiv-proof y .fst .fst .fst) .fst .fst) ,
      cong P (e .snd .equiv-proof (p .snd .equiv-proof y .fst .fst .fst) .fst .snd)
      ∙ p .snd .equiv-proof y .fst .fst .snd} {v = p .snd .equiv-proof y .fst .fst}
      (e .snd .equiv-proof (p .snd .equiv-proof y .fst .fst .fst) .fst .snd))
      ∙ p .snd .equiv-proof y .fst .snd) ,
      λ y₁ → Σ≡Prop (λ x₁ → isSetFin (p .fst (e .fst (fst x₁) , snd x₁)) y)
      (Σ≡Prop (λ x₁ → isSetBool (P (e .fst x₁)) true)
      (cong fst (e .snd .equiv-proof (p .snd .equiv-proof y .fst .fst .fst) .snd
      (y₁ .fst .fst , sym (cong (fst ∘ fst) (p .snd .equiv-proof y .snd
      ((e .fst (y₁ .fst .fst) , y₁ .fst .snd) , y₁ .snd)))))))} ∣₁) bl

ℙᵈᵢ≃Iso : ∀ {ℓ ℓ'} → (X : Type ℓ) (Y : Type ℓ') (k : ℕ) → (X ≃ Y) → Iso (ℙᵈᵢ k Y) (ℙᵈᵢ k X)
ℙᵈᵢ≃Iso X Y k e .Iso.fun = ℙᵈᵢ≃→ X Y k e
ℙᵈᵢ≃Iso X Y k e .Iso.inv = ℙᵈᵢ≃→ Y X k (invEquiv e)
ℙᵈᵢ≃Iso X Y k e .Iso.leftInv (P , bl) = Σ≡Prop (λ _ → isPropPropTrunc)
  (cong ((P ∘_) ∘ fst) (invEquiv-is-linv e))
ℙᵈᵢ≃Iso X Y k e .Iso.rightInv (P , bl) = Σ≡Prop (λ _ → isPropPropTrunc)
  (cong ((P ∘_) ∘ fst) (invEquiv-is-rinv e))

ℙᵈᵢ≃ : ∀ {ℓ ℓ'} → (X : Type ℓ) (Y : Type ℓ') (k : ℕ) → (X ≃ Y) → ℙᵈᵢ k Y ≃ ℙᵈᵢ k X
ℙᵈᵢ≃ X Y k e = isoToEquiv (ℙᵈᵢ≃Iso X Y k e)

isFinℙᵈᵢ : ∀ {ℓ} → (k : ℕ) → (X : FinSet ℓ) → isFinSet (ℙᵈᵢ k ⟨ X ⟩)
isFinℙᵈᵢ k (X , n , isFinX) = n choose k , proprec isPropPropTrunc
  (λ p → ∣ (ℙᵈᵢ≃ (Fin n) X k (invEquiv p)) ∙ₑ isFinOrdℙᵈᵢFin k n ∣₁) isFinX
