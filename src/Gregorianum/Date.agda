module Gregorianum.Date where

open import Gregorianum.Year using (Year; YearType; _HasYearType_)
open import Gregorianum.YearMonth using (YearMonth)
open import Gregorianum.Month using (Month; _HasDays_; _of_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

Day = Fin

record Date : Set where
  field
    year-month : YearMonth
    {year-type} : YearType
    has-year-type : YearMonth.year year-month HasYearType year-type
    {days} : ℕ
    has-days : (YearMonth.month year-month of year-type) HasDays days
    day : Day days

  open YearMonth year-month
