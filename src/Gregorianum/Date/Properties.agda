module Gregorianum.Date.Properties where

open import Gregorianum.Date.Base

open import Gregorianum.Day.Base using (Day)
import Gregorianum.YearMonth.Base as YM
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Gregorianum.Data.Cursor.Properties as Cursor

open import Gregorianum.YearMonth.Properties as YM using (nextYearMonth-unique; prevYearMonth-unique)
open import Data.Product using (∃-syntax; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

nextDate-unique : ∀ {d₁ d₂ d₃ : Date}
                → d₁ ⋖ d₂
                → d₁ ⋖ d₃
                → d₂ ≡ d₃
nextDate-unique stepᵈ stepᵈ = refl
nextDate-unique (stepʸᵐ p) (stepʸᵐ q) with nextYearMonth-unique p q
nextDate-unique {_} {ym₂ - d₂ ⟨ hasDays₂ ⟩} {_ - _ ⟨ hasDays₃ ⟩} (stepʸᵐ p) (stepʸᵐ q) | refl with YM.days-unique hasDays₂ hasDays₃
... | refl with YM.HasDays-irrelevant hasDays₂ hasDays₃
... | refl = refl

prevDate-unique : ∀ {d₁ d₂ d₃ : Date}
                 → d₁ ⋖ d₃
                 → d₂ ⋖ d₃
                 → d₁ ≡ d₂
prevDate-unique stepᵈ stepᵈ = refl
prevDate-unique (stepʸᵐ p) (stepʸᵐ q) with prevYearMonth-unique p q
prevDate-unique {_ - mkPos c₁ ⟨ hasDays₁ ⟩} {_ - mkPos c₂ ⟨ hasDays₂ ⟩} (stepʸᵐ p) (stepʸᵐ q) | refl with YM.days-unique hasDays₁ hasDays₂
... | refl with YM.HasDays-irrelevant hasDays₁ hasDays₂
... | refl with Cursor.unique c₁ c₂
... | refl = refl

