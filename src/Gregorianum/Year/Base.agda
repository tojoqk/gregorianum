module Gregorianum.Year.Base where

open import Gregorianum.Law.Leap using (Leap)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Relation.Nullary.Negation using (¬_)

data YearType : Set where
  common : YearType
  leap : YearType

data IsLeap : ℤ → Set where
  is-leap⁺ : ∀ {n : ℕ} → Leap n → IsLeap (+ n)
  is-leap⁻ : ∀ {n : ℕ} → Leap (suc n) → IsLeap (-[1+ n ])

data _HasYearType_ : ℤ → YearType → Set where
  common : ∀ {y} → ¬ IsLeap y → y HasYearType common
  leap   : ∀ {y} → IsLeap y → y HasYearType leap


-- Proleptic Gregorian calendar
data _⋖ᶻ_ : ℤ → ℤ → Set where
  step⁺ : ∀ {n} → (+ n) ⋖ᶻ (+ suc n)
  step⁰ : -[1+ zero ] ⋖ᶻ (+ zero)
  step⁻ : ∀ {n} → -[1+ suc n ] ⋖ᶻ -[1+ n ]

record Year (yt : YearType): Set where
  constructor _th⟨_⟩
  field
    year : ℤ
    has-year-type : year HasYearType yt

data _⋖_ : ∀ {yt₁ yt₂} → Year yt₁ → Year yt₂ → Set where
  common-common : ∀ { y₁ y₂ }
                → y₁ ⋖ᶻ y₂
                → (p : y₁ HasYearType common)
                → (q : y₂ HasYearType common)
                → (y₁ th⟨ p ⟩) ⋖ (y₂ th⟨ q ⟩)
  common-leap   : ∀ { y₁ y₂ }
                → y₁ ⋖ᶻ y₂
                → (p : y₁ HasYearType common)
                → (q : y₂ HasYearType leap)
                → (y₁ th⟨ p ⟩) ⋖ (y₂ th⟨ q ⟩)
  leap-common   : ∀ { y₁ y₂ }
                → y₁ ⋖ᶻ y₂
                → (p : y₁ HasYearType leap)
                → (q : y₂ HasYearType common)
                → (y₁ th⟨ p ⟩) ⋖ (y₂ th⟨ q ⟩)
