module Gregorianum.Date.Properties where

open import Gregorianum.Date.Base

open import Gregorianum.Day.Base using (Day)
import Gregorianum.YearMonth.Base as YM
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Gregorianum.Data.Cursor.Properties as Cursor

open import Gregorianum.YearMonth.Properties as YM using (next-year-month-unique; prev-year-month-unique)
open import Data.Product using (∃-syntax; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

next-date-unique : ∀ {d₁ d₂ d₃ : Date}
                → d₁ ⋖ d₂
                → d₁ ⋖ d₃
                → d₂ ≡ d₃
next-date-unique stepᵈ stepᵈ = refl
next-date-unique (stepʸᵐ p) (stepʸᵐ q) with next-year-month-unique p q
next-date-unique {_} {ym₂ - d₂ ⟨ hasDays₂ ⟩} {_ - _ ⟨ hasDays₃ ⟩} (stepʸᵐ p) (stepʸᵐ q) | refl with YM.days-unique hasDays₂ hasDays₃
... | refl with YM.has-days-irrelevant hasDays₂ hasDays₃
... | refl = refl

prev-date-unique : ∀ {d₁ d₂ d₃ : Date}
                 → d₁ ⋖ d₃
                 → d₂ ⋖ d₃
                 → d₁ ≡ d₂
prev-date-unique stepᵈ stepᵈ = refl
prev-date-unique (stepʸᵐ p) (stepʸᵐ q) with prev-year-month-unique p q
prev-date-unique {_ - mkPos c₁ ⟨ hasDays₁ ⟩} {_ - mkPos c₂ ⟨ hasDays₂ ⟩} (stepʸᵐ p) (stepʸᵐ q) | refl with YM.days-unique hasDays₁ hasDays₂
... | refl with YM.has-days-irrelevant hasDays₁ hasDays₂
... | refl with Cursor.unique c₁ c₂
... | refl = refl

