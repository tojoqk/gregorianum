module Gregorianum.Year.Properties where

open import Gregorianum.Year.Base

open import Gregorianum.Law.Leap.Base
open import Gregorianum.Law.Leap.Properties using (leap?; leap⇒¬leap+1; leap+1⇒¬leap; ¬leap1; leap-irrelevant)
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

⋖ᶻ-pred : ∀ a → (ℤ.pred a) ⋖ᶻ a
⋖ᶻ-pred (+_ zero) = step⁰
⋖ᶻ-pred (+_ (suc _)) = step⁺
⋖ᶻ-pred -[1+ _ ] = step⁻

is-leap-irrelevant : ∀ {y} → (p : IsLeap y) → (q : IsLeap y) → p ≡ q
is-leap-irrelevant (is-leap⁺ p) (is-leap⁺ q) rewrite (leap-irrelevant p q) = refl
is-leap-irrelevant (is-leap⁻ p) (is-leap⁻ q) rewrite (leap-irrelevant p q) = refl

has-year-type-irrelevant : ∀ {a yt}
                         → (p : a HasYearType yt)
                         → (q : a HasYearType yt)
                         → p ≡ q
has-year-type-irrelevant (common _) (common _) = refl
has-year-type-irrelevant (leap p) (leap q) rewrite (is-leap-irrelevant p q) = refl

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

prev-ℤ-unique : ∀ {a b c} → a ⋖ᶻ c → b ⋖ᶻ c → a ≡ b
prev-ℤ-unique step⁺ step⁺ = refl
prev-ℤ-unique step⁰ step⁰ = refl
prev-ℤ-unique step⁻ step⁻ = refl

next-year-unique : ∀ {yt₁ yt₂ yt₃}
                      → { y₁@(a₁ ⟨ _ ⟩) : Year yt₁}
                      → { y₂@(a₂ ⟨ _ ⟩) : Year yt₂}
                      → { y₃@(a₃ ⟨ _ ⟩) : Year yt₃}
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

prev-year-unique : ∀ {yt₁ yt₂ yt₃}
                 → { y₁@(a₁ ⟨ _ ⟩) : Year yt₁}
                 → { y₂@(a₂ ⟨ _ ⟩) : Year yt₂}
                 → { y₃@(a₃ ⟨ _ ⟩) : Year yt₃}
                 → y₁ ⋖ y₃
                 → y₂ ⋖ y₃
                 → yt₁ ≡ yt₂ × a₁ ≡ a₂
prev-year-unique (common-common a₁⋖a₃ _ _) (common-common a₂⋖a₃ _ _) = refl , (prev-ℤ-unique a₁⋖a₃ a₂⋖a₃)
prev-year-unique (leap-common a₁⋖a₃ _ _) (leap-common a₂⋖a₃ _ _) = refl , prev-ℤ-unique a₁⋖a₃ a₂⋖a₃
prev-year-unique (common-common a₁⋖a₃ (common ¬p) _) (leap-common a₂⋖a₃ (leap p) _) with prev-ℤ-unique a₁⋖a₃ a₂⋖a₃
...                                                                                    | refl = contradiction p ¬p
prev-year-unique (common-leap a₁⋖a₃ _ _) (common-leap a₂⋖a₃ _ _) = refl , (prev-ℤ-unique a₁⋖a₃ a₂⋖a₃)
prev-year-unique (leap-common a₁⋖a₃ (leap p) _) (common-common a₂⋖a₃ (common ¬p) _) with prev-ℤ-unique a₁⋖a₃ a₂⋖a₃
...                                                                                    | refl = contradiction p ¬p

next-year-exists : ∀ {yt₁} (y₁ : Year yt₁) → ∃[ yt₂ ] Σ[ y₂ ∈ Year yt₂ ] (y₁ ⋖ y₂)
next-year-exists (a ⟨ common p ⟩) with isLeap? (ℤ.suc a)
next-year-exists (a ⟨ common p ⟩)    | yes q = leap , (((+ 1 ℤ.+ a) ⟨ leap q ⟩) , common-leap (⋖ᶻ-suc a) (common p) (leap q))
next-year-exists (a ⟨ common p ⟩)    | no ¬q = common , (((+ 1 ℤ.+ a) ⟨ common ¬q ⟩) , common-common (⋖ᶻ-suc a) (common p) (common ¬q))
next-year-exists (a ⟨ leap p ⟩)                      with isLeap? (ℤ.suc a)
next-year-exists (a ⟨ leap p ⟩)                         | no ¬q = common , ((+ 1 ℤ.+ a) ⟨ common ¬q ⟩) , leap-common (⋖ᶻ-suc a) (leap p) (common ¬q)
next-year-exists ((+ n) ⟨ leap (is-leap⁺ p) ⟩)          | yes (is-leap⁺ q) = contradiction p (leap+1⇒¬leap q)
next-year-exists (-[1+ zero ] ⟨ leap (is-leap⁻ p) ⟩)    | yes (is-leap⁺ q) = contradiction p ¬leap1
next-year-exists (-[1+ (suc n) ] ⟨ leap (is-leap⁻ p) ⟩) | yes (is-leap⁻ q) = contradiction p (leap⇒¬leap+1 q)

prev-year-exists : ∀ {yt₂} (y₂ : Year yt₂) → ∃[ yt₁ ] Σ[ y₁ ∈ Year yt₁ ] (y₁ ⋖ y₂)
prev-year-exists (a ⟨ common q ⟩) with isLeap? (ℤ.pred a)
prev-year-exists (a ⟨ common q ⟩)    | yes p = leap , (ℤ.pred a ⟨ leap p ⟩) , leap-common (⋖ᶻ-pred a) (leap p) (common q)
prev-year-exists (a ⟨ common q ⟩)    | no ¬p = common , (((ℤ.pred a) ⟨ common ¬p ⟩) , common-common (⋖ᶻ-pred a) (common ¬p) (common q))
prev-year-exists (a ⟨ leap q ⟩)                   with isLeap? (ℤ.pred a)
prev-year-exists (a ⟨ leap q ⟩)                      | no ¬p = common , (((ℤ.pred a) ⟨ (common ¬p) ⟩) , (common-leap (⋖ᶻ-pred a) (common ¬p) (leap q)))
prev-year-exists ((+ zero) ⟨ leap _ ⟩)               | yes (is-leap⁻ p) = contradiction p ¬leap1
prev-year-exists ((+ (suc _)) ⟨ leap (is-leap⁺ q) ⟩) | yes (is-leap⁺ p) = contradiction p (leap+1⇒¬leap q)
prev-year-exists (-[1+_] _ ⟨ leap (is-leap⁻ q) ⟩)    | yes (is-leap⁻ p) = contradiction p (leap⇒¬leap+1 q)
