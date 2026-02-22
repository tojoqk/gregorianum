module Gregorianum.Date where

open import Gregorianum.Year using (Year)
open import Gregorianum.YearMonth as YM using (YearMonth)
open import Gregorianum.Day using (Day; 1st; suc)
open import Data.Nat using (ℕ; suc)

record Date : Set where
  constructor _/_
  field
    {cap}     : ℕ
    year-month : YearMonth (suc cap) -- suc cap ≡ days
    {acc} : ℕ
    {rem} : ℕ
    day : Day cap acc rem

  open YearMonth year-month

pattern _/_⟨_,_⟩ ym d acc rem = _/_ ym {acc} {rem} d

data _⋖_ : Date → Date → Set where
  step : ∀ {cap acc rem} {ym : YearMonth (suc cap)}
       → (d : Day cap acc (suc rem))
       → (ym / d) ⋖ (ym / suc d)
  step-last : ∀ {cap₁ cap₂} {ym₁ : YearMonth (suc cap₁)} {ym₂ : YearMonth (suc cap₂)}
            → (d : Day cap₁ cap₁ 0)
            → ym₁ YM.⋖ ym₂
            → (ym₁ / d) ⋖ (ym₂ / 1st)
