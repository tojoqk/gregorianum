module Gregorianum.YearMonth where

open import Gregorianum.Year as Y using (Year; YearType; common; leap)
open import Gregorianum.Month
open import Data.Nat using (ℕ)

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

record YearMonth (days : ℕ): Set where
  constructor _/_⟨_⟩
  field
    {year-type} : YearType
    year : Year year-type
    month : Month
    has-days : (month of year-type) HasDays days

data _⋖_ : ∀ {m n} → YearMonth m → YearMonth n → Set where
  january-feburary-common : ∀ {y : Year common}  → (y / january ⟨ january ⟩)          ⋖ (y / february ⟨ february-common ⟩)
  january-feburary-leap   : ∀ {y : Year leap}    → (y / january ⟨ january ⟩)          ⋖ (y / february ⟨ february-leap ⟩)
  february-common-march   : ∀ {y : Year common}  → (y / february ⟨ february-common ⟩) ⋖ (y / march ⟨ march ⟩)
  february-leap-march     : ∀ {y : Year leap}    → (y / february ⟨ february-leap ⟩)   ⋖ (y / march ⟨ march ⟩)
  march-april             : ∀ {yt} {y : Year yt} → (y / march ⟨ march ⟩)              ⋖ (y / april ⟨ april ⟩)
  april-may               : ∀ {yt} {y : Year yt} → (y / april ⟨ april ⟩)              ⋖ (y / may ⟨ may ⟩)
  may-june                : ∀ {yt} {y : Year yt} → (y / may ⟨ may ⟩)                  ⋖ (y / june ⟨ june ⟩)
  june-july               : ∀ {yt} {y : Year yt} → (y / june ⟨ june ⟩)                ⋖ (y / july ⟨ july ⟩)
  july-august             : ∀ {yt} {y : Year yt} → (y / july ⟨ july ⟩)                ⋖ (y / august ⟨ august ⟩)
  august-september        : ∀ {yt} {y : Year yt} → (y / august ⟨ august ⟩)            ⋖ (y / september ⟨ september ⟩)
  september-october       : ∀ {yt} {y : Year yt} → (y / september ⟨ september ⟩)      ⋖ (y / october ⟨ october ⟩)
  october-november        : ∀ {yt} {y : Year yt} → (y / october ⟨ october ⟩)          ⋖ (y / november ⟨ november ⟩)
  november-december       : ∀ {yt} {y : Year yt} → (y / november ⟨ november ⟩)        ⋖ (y / december ⟨ december ⟩)
  december-january        : ∀ {yt₁} {y₁ : Year yt₁} {yt₂} {y₂ : Year yt₂}
                          → y₁ Y.⋖ y₂ → (y₁ / december ⟨ december ⟩) ⋖ (y₂ / january ⟨ january ⟩)
