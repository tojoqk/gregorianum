module Gregorianum.Year.Properties where

open import Gregorianum.Law.Leap
open import Gregorianum.Law.Leap.Properties using (leap?; leap⇒¬leap+1; leap+1⇒¬leap; ¬leap1; leap-irrelevant)
open import Gregorianum.Year
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Product using (∃-syntax; Σ-syntax; Σ; _×_; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

isLeap? : ∀ y → Dec (IsLeap y)
isLeap? (+ n) with leap? n
... | yes lp = yes (is-leap⁺ lp)
... | no ¬lp = no λ { (is-leap⁺ lp) → ¬lp lp }
isLeap? (-[1+ n ]) with leap? (suc n)
... | yes lp = yes (is-leap⁻ lp)
... | no ¬lp = no λ { (is-leap⁻ lp) → ¬lp lp }

next-integer-exists : ∀ a → ∃[ b ] a ⋖ᶻ b
next-integer-exists (+ n) = (+ (suc n)) , step⁺
next-integer-exists (-[1+_] zero) = + zero , step⁰
next-integer-exists (-[1+_] (suc n)) = -[1+ n ] , step⁻

⋖ᶻ-suc : ∀ a → a ⋖ᶻ (ℤ.suc a)
⋖ᶻ-suc (+_ n) = step⁺
⋖ᶻ-suc (-[1+_] zero) = step⁰
⋖ᶻ-suc (-[1+_] (suc n)) = step⁻

is-leap-irrelevant : ∀ {y} → (p : IsLeap y) → (q : IsLeap y) → p ≡ q
is-leap-irrelevant (is-leap⁺ p) (is-leap⁺ q) rewrite (leap-irrelevant p q) = refl
is-leap-irrelevant (is-leap⁻ p) (is-leap⁻ q) rewrite (leap-irrelevant p q) = refl

has-year-type-irrelevant : ∀ {a yt}
                         → (p : a HasYearType yt)
                         → (q : a HasYearType yt)
                         → p ≡ q
has-year-type-irrelevant (common _) (common _) = refl
has-year-type-irrelevant (leap p) (leap q) rewrite (is-leap-irrelevant p q) = refl

year-unique : ∀ {yt} ( (a th⟨ p ⟩) (b th⟨ q ⟩) : Year yt)
            → a ≡ b
            → (a th⟨ p ⟩) ≡ (b th⟨ q ⟩)
year-unique (a th⟨ p ⟩) (b th⟨ q ⟩) refl rewrite (has-year-type-irrelevant p q) = refl


year-type-unique : ∀ {a yt₁ yt₂}
                   → a HasYearType yt₁
                   → a HasYearType yt₂
                   → yt₁ ≡ yt₂
year-type-unique (common _) (common _) = refl
year-type-unique (common ¬p) (leap p) = contradiction p ¬p
year-type-unique (leap p) (common ¬p) = contradiction p ¬p
year-type-unique (leap _) (leap _) = refl

next-ℤ-unique : ∀ {a b c} → a ⋖ᶻ b → a ⋖ᶻ c → b ≡ c
next-ℤ-unique step⁺ step⁺ = refl
next-ℤ-unique step⁰ step⁰ = refl
next-ℤ-unique step⁻ step⁻ = refl

next-year-unique : ∀ {yt₁ yt₂ yt₃}
                      → { y₁@(a₁ th⟨ _ ⟩) : Year yt₁}
                      → { y₂@(a₂ th⟨ _ ⟩) : Year yt₂}
                      → { y₃@(a₃ th⟨ _ ⟩) : Year yt₃}
                      → y₁ ⋖ y₂
                      → y₁ ⋖ y₃
                      → yt₂ ≡ yt₃ × a₂ ≡ a₃
next-year-unique (common-common a₁⋖a₂ _ _) (common-common a₁⋖a₃ _ _) = refl , next-ℤ-unique a₁⋖a₂ a₁⋖a₃
next-year-unique (common-leap a₁⋖a₂ _ _) (common-leap a₁⋖a₃ _ _) = refl , next-ℤ-unique a₁⋖a₂ a₁⋖a₃
next-year-unique (common-common a₁⋖a₂ _ (common ¬q)) (common-leap a₁⋖a₃ _ (leap q)) with next-ℤ-unique a₁⋖a₂ a₁⋖a₃
...                                                                                    | refl = contradiction q ¬q
next-year-unique (common-leap a₁⋖a₂ _ (leap q)) (common-common a₁⋖a₃ p₁ (common ¬q)) with next-ℤ-unique a₁⋖a₂ a₁⋖a₃
...                                                                                     | refl = contradiction q ¬q
next-year-unique (leap-common  a₁⋖a₂ _ _) (leap-common a₁⋖a₃ _ _) = refl , next-ℤ-unique a₁⋖a₂ a₁⋖a₃

next-year-exists : ∀ {yt₁} (y₁ : Year yt₁) → ∃[ yt₂ ] Σ[ y₂ ∈ Year yt₂ ] (y₁ ⋖ y₂)
next-year-exists (a th⟨ common p ⟩) with isLeap? (ℤ.suc a)
next-year-exists (a th⟨ common p ⟩)    | yes q = leap , (((+ 1 ℤ.+ a) th⟨ leap q ⟩) , common-leap (⋖ᶻ-suc a) (common p) (leap q))
next-year-exists (a th⟨ common p ⟩)    | no ¬q = common , (((+ 1 ℤ.+ a) th⟨ common ¬q ⟩) , common-common (⋖ᶻ-suc a) (common p) (common ¬q))
next-year-exists (a th⟨ leap p ⟩)                      with isLeap? (ℤ.suc a)
next-year-exists (a th⟨ leap p ⟩)                         | no ¬q = common , ((+ 1 ℤ.+ a) th⟨ common ¬q ⟩) , leap-common (⋖ᶻ-suc a) (leap p) (common ¬q)
next-year-exists ((+ n) th⟨ leap (is-leap⁺ p) ⟩)          | yes (is-leap⁺ q) = contradiction p (leap+1⇒¬leap q)
next-year-exists (-[1+ zero ] th⟨ leap (is-leap⁻ p) ⟩)    | yes (is-leap⁺ q) = contradiction p ¬leap1
next-year-exists (-[1+ (suc n) ] th⟨ leap (is-leap⁻ p) ⟩) | yes (is-leap⁻ q) = contradiction p (leap⇒¬leap+1 q)
