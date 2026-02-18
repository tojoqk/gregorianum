module Gregorianum.Year.Properties where

open import Gregorianum.Law.Leap
open import Gregorianum.Law.Leap.Properties using (leap?; leap⇒¬leap+1; leap+1⇒¬leap; ¬leap1)
open import Gregorianum.Year
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Data.Product using (∃-syntax; Σ-syntax; Σ; _×_; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

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

next-year-exists : ∀ {yt₁} (y₁ : Year yt₁) → ∃[ yt₂ ] Σ[ y₂ ∈ Year yt₂ ] (y₁ ⋖ y₂)
next-year-exists {common} (y th⟨ _ ⟩) with isLeap? (ℤ.suc y)
next-year-exists {common} (y th⟨ p ⟩)    | yes q = leap , ((ℤ.suc y th⟨ leap q ⟩) , common-leap (⋖ᶻ-suc y) p (leap q))
next-year-exists {common} (y th⟨ p ⟩)    | no ¬q = common , ((ℤ.suc y) th⟨ (common ¬q) ⟩) , common-common (⋖ᶻ-suc y) p (common ¬q)
next-year-exists {leap} (y th⟨ _ ⟩)                           with isLeap? (ℤ.suc y)
next-year-exists {leap} (y th⟨ p ⟩)                              | no ¬q = common , ((ℤ.suc y) th⟨ (common ¬q) ⟩) , leap-common (⋖ᶻ-suc y) p (common ¬q)
next-year-exists {leap} (+_ n th⟨ leap (is-leap⁺ p) ⟩)           | yes (is-leap⁺ q) = contradiction q (leap⇒¬leap+1 p)
next-year-exists {leap} (-[1+_] zero th⟨ leap (is-leap⁻ p) ⟩)    | yes _ = contradiction p ¬leap1
next-year-exists {leap} (-[1+_] (suc n) th⟨ leap (is-leap⁻ p) ⟩) | yes (is-leap⁻ q) = contradiction q (leap+1⇒¬leap p)




