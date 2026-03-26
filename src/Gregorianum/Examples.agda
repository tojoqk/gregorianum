module Gregorianum.Examples where

open import Gregorianum.Date
open import Gregorianum.Date.Timeline
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Compile-time verified dates via decidable predicates
_ : Date
_ = ⟨ 2026 - 3 - 23 ⟩

-- Leap years are handled automatically; 2024-02-29 is valid
_ : Date
_ = ⟨ 2024 - 2 - 29 ⟩

-- This would result in a compile-time error:
-- invalidDay : Date
-- invalidDay = ⟨ 2026 - 2 - 29 ⟩

_ : proj₁ (nextDate ⟨ 2024 - 2 - 29 ⟩) ≡ ⟨ 2024 - 3 - 1 ⟩
_ = refl

_ : ⟨ 2024 - 2 - 29 ⟩ ⋖ ⟨ 2024 - 3 - 1 ⟩
_ = proj₂ (nextDate ⟨ 2024 - 2 - 29 ⟩)

_ : proj₁ (from-yes (prevDate? ⟨ 2024 - 3 - 1 ⟩)) ≡ ⟨ 2024 - 2 - 29 ⟩
_ = refl

_ : ⟨ 2024 - 2 - 29 ⟩ ⋖ ⟨ 2024 - 3 - 1 ⟩
_ = proj₂ (from-yes (prevDate? ⟨ 2024 - 3 - 1 ⟩))

_ : ⟨ 2024 - 12 - 31 ⟩ ⋖ ⟨ 2025 - 1 - 1 ⟩
_ = proj₂ (nextDate ⟨ 2024 - 12 - 31 ⟩)

_ : ⟨ 2024 - 12 - 31 ⟩ ⋖ ⟨ 2025 - 1 - 1 ⟩
_ = proj₂ (from-yes (prevDate? ⟨ 2025 - 1 - 1 ⟩))

_ : proj₁ (addDays ⟨ 2024 - 2 - 22 ⟩ 366) ≡ ⟨ 2025 - 2 - 22 ⟩
_ = refl

_ : ⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→ ⟨ 2025 - 2 - 22 ⟩
_ = proj₂ (addDays ⟨ 2024 - 2 - 22 ⟩ 366)

_ : ⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→ ⟨ 2025 - 2 - 22 ⟩
_ = proj₂ (from-yes (subtractDays? ⟨ 2025 - 2 - 22 ⟩ 366))

_ : ⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→ ⟨ 2025 - 2 - 22 ⟩
_ = from-yes (⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→? ⟨ 2025 - 2 - 22 ⟩)

_ : ⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→ ⟨ 2025 - 2 - 22 ⟩
_ = from-yes (⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→? ⟨ 2025 - 2 - 22 ⟩)
