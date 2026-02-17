module Gregorianum.Year where

open import Gregorianum.Law.Leap using (Leap)
open import Data.Nat using (ℕ; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Relation.Nullary.Negation using (¬_)

Year = ℤ

data YearType : Set where
  common : YearType
  leap : YearType

data IsLeap : Year → Set where
  is-leap⁺ : ∀ {n : ℕ} → Leap n → IsLeap (+ n)
  is-leap⁻ : ∀ {n : ℕ} → Leap (suc n) → IsLeap (-[1+ n ])

data _HasYearType_ : Year → YearType → Set where
  common : ∀ {y} → ¬ IsLeap y → y HasYearType common
  leap   : ∀ {y} → IsLeap y → y HasYearType leap
