module Gregorianum.YearMonth where

open import Gregorianum.Year using (Year)
open import Gregorianum.Month using (Month)

record YearMonth : Set where
  field
    year : Year
    month : Month
