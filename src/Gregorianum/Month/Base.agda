module Gregorianum.Month.Base where

open import Gregorianum.Year using (YearType; common; leap)
open import Data.Nat using (ℕ)

data Month : Set where
  january   : Month
  february  : Month
  march     : Month
  april     : Month
  may       : Month
  june      : Month
  july      : Month
  august    : Month
  september : Month
  october   : Month
  november  : Month
  december  : Month

record MonthInYearType : Set where
  constructor _of_
  field
    month : Month
    year-type : YearType

data _HasDays_ : MonthInYearType → ℕ → Set where
  january         : ∀ {yt} →      (january of yt) HasDays 31
  february-common :           (february of common) HasDays 28
  february-leap   :             (february of leap) HasDays 29
  march           : ∀ {yt} →        (march of yt) HasDays 31
  april           : ∀ {yt} →        (april of yt) HasDays 30
  may             : ∀ {yt} →          (may of yt) HasDays 31
  june            : ∀ {yt} →         (june of yt) HasDays 30
  july            : ∀ {yt} →         (july of yt) HasDays 31
  august          : ∀ {yt} →       (august of yt) HasDays 31
  september       : ∀ {yt} →    (september of yt) HasDays 30
  october         : ∀ {yt} →      (october of yt) HasDays 31
  november        : ∀ {yt} →     (november of yt) HasDays 30
  december        : ∀ {yt} →     (december of yt) HasDays 31
