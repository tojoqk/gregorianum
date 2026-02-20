module Gregorianum.Date where

open import Gregorianum.Year as Y using (Year; YearType; _HasYearType_)
open import Gregorianum.YearMonth as YM using (YearMonth)
open import Gregorianum.Month as M using (Month)
open import Gregorianum.Day using (Day; 1st; suc)
open import Data.Nat using (ℕ; zero; suc)

record Date : Set where
  constructor _/_
  field
    {last}     : ℕ
    year-month : YearMonth (suc last) -- suc last ≡ days
    {from-start} : ℕ
    {from-end} : ℕ
    day : Day last from-start from-end

  open YearMonth year-month

data _⋖_ : Date → Date → Set where
  step : ∀ {n i j} {ym : YearMonth (suc n)}
       → (d : Day n i (suc j))
       → (ym / d) ⋖ (ym / suc d)
  step-last : ∀ {m n} {ym₁ : YearMonth (suc m)} {ym₂ : YearMonth (suc n)}
            → (d : Day m m 0)
            → ym₁ YM.⋖ ym₂
            → (ym₁ / d) ⋖ (ym₂ / 1st)
