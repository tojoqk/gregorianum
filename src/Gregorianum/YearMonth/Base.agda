module Gregorianum.YearMonth.Base where

open import Gregorianum.Year as Y using (Year; YearType; common; leap)
open import Gregorianum.Month.Base
open import Data.Nat using (ℕ)

record YearMonth (days : ℕ): Set where
  constructor _-_⟨_⟩
  field
    {year-type} : YearType
    year : Year year-type
    month : Month
    has-days : (month of year-type) HasDays days

data _⋖_ : ∀ {m n} → YearMonth m → YearMonth n → Set where
  january-feburary-common : ∀ {y : Year common}  → (y - january ⟨ january ⟩)          ⋖ (y - february ⟨ february-common ⟩)
  january-feburary-leap   : ∀ {y : Year leap}    → (y - january ⟨ january ⟩)          ⋖ (y - february ⟨ february-leap ⟩)
  february-common-march   : ∀ {y : Year common}  → (y - february ⟨ february-common ⟩) ⋖ (y - march ⟨ march ⟩)
  february-leap-march     : ∀ {y : Year leap}    → (y - february ⟨ february-leap ⟩)   ⋖ (y - march ⟨ march ⟩)
  march-april             : ∀ {yt} {y : Year yt} → (y - march ⟨ march ⟩)              ⋖ (y - april ⟨ april ⟩)
  april-may               : ∀ {yt} {y : Year yt} → (y - april ⟨ april ⟩)              ⋖ (y - may ⟨ may ⟩)
  may-june                : ∀ {yt} {y : Year yt} → (y - may ⟨ may ⟩)                  ⋖ (y - june ⟨ june ⟩)
  june-july               : ∀ {yt} {y : Year yt} → (y - june ⟨ june ⟩)                ⋖ (y - july ⟨ july ⟩)
  july-august             : ∀ {yt} {y : Year yt} → (y - july ⟨ july ⟩)                ⋖ (y - august ⟨ august ⟩)
  august-september        : ∀ {yt} {y : Year yt} → (y - august ⟨ august ⟩)            ⋖ (y - september ⟨ september ⟩)
  september-october       : ∀ {yt} {y : Year yt} → (y - september ⟨ september ⟩)      ⋖ (y - october ⟨ october ⟩)
  october-november        : ∀ {yt} {y : Year yt} → (y - october ⟨ october ⟩)          ⋖ (y - november ⟨ november ⟩)
  november-december       : ∀ {yt} {y : Year yt} → (y - november ⟨ november ⟩)        ⋖ (y - december ⟨ december ⟩)
  december-january        : ∀ {yt₁} {y₁ : Year yt₁} {yt₂} {y₂ : Year yt₂}
                          → y₁ Y.⋖ y₂ → (y₁ - december ⟨ december ⟩) ⋖ (y₂ - january ⟨ january ⟩)
