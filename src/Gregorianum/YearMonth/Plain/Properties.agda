module Gregorianum.YearMonth.Plain.Properties where

open import Gregorianum.YearMonth.Plain.Base
open import Gregorianum.Year.Plain.Properties
open import Gregorianum.Month.Plain.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

yearMonth-unique : ∀ {ym₁ ym₂ tup} → ym₁ HasPlain tup → ym₂ HasPlain tup → ym₁ ≡ ym₂
yearMonth-unique (plain pʸ₁ pᵐ₁) (plain pʸ₂ pᵐ₂) with year-unique pʸ₁ pʸ₂ | month-unique pᵐ₁ pᵐ₂
...                                                 | refl | refl = refl
