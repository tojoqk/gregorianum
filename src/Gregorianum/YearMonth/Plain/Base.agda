module Gregorianum.YearMonth.Plain.Base where

open import Gregorianum.YearMonth.Base using (YearMonth; _-_)

import Gregorianum.Year.Plain as Y
import Gregorianum.Month.Plain as M

open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)

data _HasPlain_ (ym : YearMonth) : (ℕ × ℕ) → Set where
  plain : ∀ {y m}
        → (YearMonth.year ym) Y.HasPlain y
        → (YearMonth.month ym) M.HasPlain m
        → ym HasPlain (y , m)

toPlain : (ym : YearMonth) → Σ[ (y , m) ∈ ℕ × ℕ ] ym HasPlain (y , m)
toPlain (year - month) with Y.toPlain year | M.toPlain month
...                       | year' , pʸ | month' , pᵐ = (year' , month') , plain pʸ pᵐ

fromPlain? : (tup : ℕ × ℕ) → Dec (∃[ ym ] ym HasPlain tup)
fromPlain? (y , m) with Y.fromPlain y | M.fromPlain? m
...                   | y' , pʸ | yes (m' , pᵐ) = yes ((y' - m') , plain pʸ pᵐ)
...                   | _       | no ¬p = no λ { ((_ - m') , plain _ p) → ¬p (m' , p)}
