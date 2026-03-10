module Gregorianum.Date.Base where

open import Gregorianum.Year using (Year)
open import Gregorianum.YearMonth as YM using (YearMonth)
open import Gregorianum.Day using (Day)
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position

open import Data.Nat using (ℕ; suc)

record Date : Set where
  constructor _-_
  field
    {width}     : ℕ
    year-month : YearMonth (suc width) -- suc width ≡ days
    day : Day width

  open YearMonth year-month public

pattern _-_⟨_,_⟩ ym d acc rem = _-_ ym {acc} {rem} d

data _⋖_ : Date → Date → Set where
  step : ∀ {width acc rem} {ym : YearMonth (suc width)}
       → (c : Cursor width acc (suc rem))
       → (ym - pos c) ⋖ (ym - pos (suc c))
  step-month : ∀ {width₁ width₂} {ym₁ : YearMonth (suc width₁)} {ym₂ : YearMonth (suc width₂)}
             → (c : Cursor width₁ width₁ 0)
             → ym₁ YM.⋖ ym₂
             → (ym₁ - pos c) ⋖ (ym₂ - pos first)
