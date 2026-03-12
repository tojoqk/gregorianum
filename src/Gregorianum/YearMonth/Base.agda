module Gregorianum.YearMonth.Base where

open import Gregorianum.Year as Y using (Year; _HasYearType_)
open import Gregorianum.Month.Base as M hiding (_HasDays_; days)
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
import Gregorianum.Data.Cursor.Properties as Cursor

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_)

record YearMonth : Set where
  constructor _-_
  field
    year : Year
    month : Month

data _⋖_ : YearMonth → YearMonth → Set where
  stepᵐ : ∀ {y acc rem} → {c : Cursor 11 acc (suc rem)} → (y - mkPos c) ⋖ (y - mkPos (suc c))
  stepʸ : ∀ {y₁ y₂} → y₁ Y.⋖ y₂ → (y₁ - december) ⋖ (y₂ - january)

data IsSuccessor : YearMonth → Set where
  sucᵐ : ∀ {y acc rem} → {c : Cursor 11 (suc acc) rem} → IsSuccessor (y - mkPos c)
  sucʸ : ∀ {y} → Y.IsSuccessor y → IsSuccessor (y - january)

record _HasDays_ (ym : YearMonth) (days : ℕ) : Set where
  constructor mkHasDays
  field
    {yearType} : Y.YearType
    hasYearType : YearMonth.year ym HasYearType yearType
    hasDays : (yearType , YearMonth.month ym) M.HasDays days

days : ∀ ym → ∃[ ds ] ym HasDays ds
days (ym - m) with Y.yearType ym
...              | yt , pʸᵗ with M.days (yt , m)
...                            | ds , pᵈ = ds , mkHasDays pʸᵗ pᵈ

nextYearMonth : ∀ ym₁ → ∃[ ym₂ ] ym₁ ⋖ ym₂
nextYearMonth (year - mkPos {rem = suc rem} cursor) = (year - mkPos (suc cursor)) , stepᵐ
nextYearMonth (year - mkPos {rem = zero} twelfth) with Y.nextYear year
...                                                  | year' , p = (year' - january) , stepʸ p
nextYearMonth (year - mkPos {rem = zero} c₁₂@(suc×₁₂ _)) with Cursor.rem≡0⇒width≡acc c₁₂
...                                                         | ()

prevYearMonth : ∀ ym₂ → IsSuccessor ym₂ → ∃[ ym₁ ] ym₁ ⋖ ym₂
prevYearMonth (year - mkPos (suc cᵐ)) sucᵐ = (year - mkPos cᵐ) , stepᵐ
prevYearMonth (year - mkPos first) (sucʸ p) with Y.prevYear year p
...                                            | year' , p' = (year' - december) , stepʸ p'
