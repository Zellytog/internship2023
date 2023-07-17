open import Agda.Primitive
open import Cubical.Core.Everything
open import Cubical.Data.Bool
open import Cubical.Data.Empty renaming (rec to zrec)
open import Cubical.Data.FinSet
open import Cubical.Data.Sum renaming (rec to sumrec ; elim to sumelim)
open import Cubical.Data.SumFin
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Everything
open import Cubical.Functions.Involution
open import Cubical.HITs.PropositionalTruncation renaming (rec to proprec)
open import Cubical.Relation.Nullary
open import Sign.AbGrp
open import Sign.TwoTorsors
open import Sign.Orientation.Base
open import Sign.Orientation.Sign
open import Sign.Orientation.FinPart

module Sign.Orientation.TestFunctions where

testinvol : Fin 2 → Fin 2
testinvol fzero = fsuc fzero
testinvol (fsuc fzero) = fzero

involtest : isInvolution testinvol
involtest fzero = refl
involtest (fsuc fzero) = refl

testinvolIsEquiv : isEquiv testinvol
testinvolIsEquiv = involIsEquiv involtest

FinNotEq : 𝔖 2
FinNotEq = ua (testinvol , testinvolIsEquiv)

pσ₂ : 𝔖 2 → Path (Σ[ X ∈ Type₀ ] ∥ X ≃ Fin 2 ∥₁) (Fin 2 , ∣ idEquiv _ ∣₁) (Fin 2 , ∣ idEquiv _ ∣₁)
pσ₂ σ = ΣPathP (σ , isProp→PathP (λ _ → isPropPropTrunc) (∣ idEquiv _ ∣₁) (∣ idEquiv _ ∣₁))

Fin2isTors : (Σ[ X ∈ Type₀ ] ∥ X ≃ Fin 2 ∥₁) → TwoTorsor lzero
Fin2isTors (X , e) = X , proprec isPropPropTrunc (λ e → ∣ e ∙ₑ SumFin2≃Bool ∣₁) e

pB₂ : Bool ≡ Bool → Path (TwoTorsor lzero) (Bool , ∣ idEquiv Bool ∣₁) (Bool , ∣ idEquiv Bool ∣₁)
pB₂ e = ΣPathP (e , isProp→PathP (λ _ → isPropPropTrunc) ∣ idEquiv Bool ∣₁ ∣ idEquiv Bool ∣₁)

ε₂ : 𝔖 2 → Bool
ε₂ = +ₜ≃ (Fin 2 , ∣ idEquiv _ ∙ₑ SumFin2≃Bool ∣₁) .fst ∘ pathToEquiv ∘ cong (fst ∘ Fin2isTors) ∘ pσ₂

testS3₁ : Fin 3 → Fin 3
testS3₁ fzero = fsuc fzero
testS3₁ (fsuc fzero) = fsuc (fsuc fzero)
testS3₁ (fsuc (fsuc fzero)) = fzero

testS3₂ : Fin 3 → Fin 3
testS3₂ fzero = fsuc (fsuc fzero)
testS3₂ (fsuc fzero) = fzero
testS3₂ (fsuc (fsuc fzero)) = fsuc fzero

testS3₁₂ : ∀ x → testS3₁ (testS3₂ x) ≡ x
testS3₁₂ fzero = refl
testS3₁₂ (fsuc fzero) = refl
testS3₁₂ (fsuc (fsuc fzero)) = refl

testS3₂₁ : ∀ x → testS3₂ (testS3₁ x) ≡ x
testS3₂₁ fzero = refl
testS3₂₁ (fsuc fzero) = refl
testS3₂₁ (fsuc (fsuc fzero)) = refl

F3iso₁ : Iso (Fin 3) (Fin 3)
F3iso₁ .Iso.fun = testS3₁
F3iso₁ .Iso.inv = testS3₂
F3iso₁ .Iso.leftInv = testS3₂₁
F3iso₁ .Iso.rightInv = testS3₁₂

F3iso₂ : Iso (Fin 3) (Fin 3)
F3iso₂ .Iso.fun = testS3₂
F3iso₂ .Iso.inv = testS3₁
F3iso₂ .Iso.leftInv = testS3₁₂
F3iso₂ .Iso.rightInv = testS3₂₁

𝔖₃1 : Fin 3 ≡ Fin 3
𝔖₃1 = ua (isoToEquiv F3iso₁)

𝔖₃2 : Fin 3 ≡ Fin 3
𝔖₃2 = ua (isoToEquiv F3iso₂)

data Bool' : Type₀ where
  left : Bool'
  right : Bool'

Bool'→Bool : Bool' → Bool
Bool'→Bool left = false
Bool'→Bool right = true

Bool→Bool' : Bool → Bool'
Bool→Bool' false = left
Bool→Bool' true = right

BoolisBool' : ∀ x → Bool'→Bool (Bool→Bool' x) ≡ x
BoolisBool' true = refl
BoolisBool' false = refl

Bool'isBool : ∀ x → Bool→Bool' (Bool'→Bool x) ≡ x
Bool'isBool left = refl
Bool'isBool right = refl

Bool'IsoBool : Iso Bool' Bool
Bool'IsoBool .Iso.fun = Bool'→Bool
Bool'IsoBool .Iso.inv = Bool→Bool'
Bool'IsoBool .Iso.leftInv = Bool'isBool
Bool'IsoBool .Iso.rightInv = BoolisBool'

Bool'≃Bool : Bool' ≃ Bool
Bool'≃Bool = isoToEquiv Bool'IsoBool

Bool'T : TwoTorsor lzero
Bool'T = (Bool' , ∣ Bool'≃Bool ∣₁)

notBool' : Bool' → Bool'
notBool' left = right
notBool' right = left

notBool'invol : isInvolution notBool'
notBool'invol left = refl
notBool'invol right = refl

notBool'≡ : Bool' ≡ Bool'
notBool'≡ = ua (notBool' , involIsEquiv notBool'invol)

notEq'ₜ : Bool'T ≡ Bool'T
notEq'ₜ = ΣPathP (notBool'≡ , isProp→PathP (λ _ → isPropPropTrunc) (Bool'T .snd) (Bool'T .snd))

notEqₜ : Path (TwoTorsor lzero) (Bool , ∣ idEquiv Bool ∣₁) (Bool , ∣ idEquiv Bool ∣₁)
notEqₜ = ΣPathP (notEq , isProp→PathP (λ _ → isPropPropTrunc) ∣ idEquiv Bool ∣₁ ∣ idEquiv Bool ∣₁)

testFamily : Bool' → TwoTorsor lzero
testFamily left = Bool'T
testFamily right = Bool , ∣ idEquiv Bool ∣₁

Bool'FinSet : FinSet lzero
Bool'FinSet = Bool' , 2 , ∣ Bool'≃Bool ∙ₑ invEquiv SumFin2≃Bool ∣₁

testEqSum : testFamily ≡ testFamily
testEqSum i left = notEq'ₜ i
testEqSum i right = notEqₜ i

testEqSum2 : Σᵀᶠ≃ Bool'FinSet testFamily ≡ Σᵀᶠ≃ Bool'FinSet testFamily
testEqSum2 = cong (Σᵀᶠ≃ Bool'FinSet) testEqSum

finTest : Bool
finTest = (+ₜ≃ (Σᵀᶠ≃ Bool'FinSet testFamily) .fst ∘ pathToEquiv) $ cong fst testEqSum2

pattern oneᶠ = fzero
pattern twoᶠ = fsuc fzero
pattern threeᶠ = fsuc (fsuc fzero)
pattern fourᶠ = fsuc (fsuc (fsuc fzero))
pattern fiveᶠ = fsuc (fsuc (fsuc (fsuc fzero)))

test₃ : Fin 3 → Fin 3
test₃ oneᶠ = oneᶠ
test₃ twoᶠ = threeᶠ
test₃ threeᶠ = twoᶠ

test₃invol : isInvolution test₃
test₃invol oneᶠ = refl
test₃invol twoᶠ = refl
test₃invol threeᶠ = refl

test₃isEquiv : isEquiv test₃
test₃isEquiv = involIsEquiv test₃invol

𝔖₃3 : 𝔖 3
𝔖₃3 = ua (test₃ , test₃isEquiv)

test₅ : Fin 5 → Fin 5
test₅ oneᶠ = oneᶠ
test₅ twoᶠ = threeᶠ
test₅ threeᶠ = twoᶠ
test₅ fourᶠ = fiveᶠ
test₅ fiveᶠ = fourᶠ

test₅invol : isInvolution test₅
test₅invol oneᶠ = refl
test₅invol twoᶠ = refl
test₅invol threeᶠ = refl
test₅invol fourᶠ = refl
test₅invol fiveᶠ = refl

test₅isEquiv : isEquiv test₅
test₅isEquiv = involIsEquiv test₅invol

𝔖₅1 : 𝔖 5
𝔖₅1 = ua (test₅ , test₅isEquiv)

𝔄₅1 : 𝔄 5
𝔄₅1 = 𝔖₅1 , refl

