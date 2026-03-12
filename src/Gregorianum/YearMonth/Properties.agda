module Gregorianum.YearMonth.Properties where

open import Gregorianum.YearMonth.Base
import Gregorianum.Year as Y
import Gregorianum.Year.Properties as Y
import Gregorianum.Month as M
import Gregorianum.Month.Properties as M
open import Gregorianum.Year.Properties using (nextYear-unique; prevYear-unique)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

nextYearMonth-unique : ∀ {ym₁ ym₂ ym₃}
                     → ym₁ ⋖ ym₂
                     → ym₁ ⋖ ym₃
                     → ym₂ ≡ ym₃
nextYearMonth-unique stepᵐ stepᵐ = refl
nextYearMonth-unique (stepʸ p) (stepʸ q) with nextYear-unique p q
...                                           | refl = refl

prevYearMonth-unique : ∀ {ym₁ ym₂ ym₃}
                     → ym₁ ⋖ ym₃
                     → ym₂ ⋖ ym₃
                     → ym₁ ≡ ym₂
prevYearMonth-unique stepᵐ stepᵐ = refl
prevYearMonth-unique (stepʸ p) (stepʸ q) with prevYear-unique p q
...                                           | refl = refl

days-unique : ∀ {ym days₁ days₂}
               → ym HasDays days₁
               → ym HasDays days₂
               → days₁ ≡ days₂
days-unique (mkHasDays _ M.january-days) (mkHasDays _ M.january-days) = refl
days-unique (mkHasDays _ M.february-common-days) (mkHasDays _ M.february-common-days) = refl
days-unique (mkHasDays Y.common M.february-common-days) (mkHasDays () M.february-leap-days)
days-unique (mkHasDays Y.common₁₀₀ M.february-common-days) (mkHasDays () M.february-leap-days)
days-unique (mkHasDays _ M.february-leap-days) (mkHasDays _ M.february-leap-days) = refl
days-unique (mkHasDays () M.february-leap-days) (mkHasDays Y.common M.february-common-days)
days-unique (mkHasDays () M.february-leap-days) (mkHasDays Y.common₁₀₀ M.february-common-days)
days-unique (mkHasDays _ M.march-days) (mkHasDays _ M.march-days) = refl
days-unique (mkHasDays _ M.april-days) (mkHasDays _ M.april-days) = refl
days-unique (mkHasDays _ M.may-days) (mkHasDays _ M.may-days) = refl
days-unique (mkHasDays _ M.june-days) (mkHasDays _ M.june-days) = refl
days-unique (mkHasDays _ M.july-days) (mkHasDays _ M.july-days) = refl
days-unique (mkHasDays _ M.august-days) (mkHasDays _ M.august-days) = refl
days-unique (mkHasDays _ M.september-days) (mkHasDays _ M.september-days) = refl
days-unique (mkHasDays _ M.october-days) (mkHasDays _ M.october-days) = refl
days-unique (mkHasDays _ M.november-days) (mkHasDays _ M.november-days) = refl
days-unique (mkHasDays _ M.december-days) (mkHasDays _ M.december-days) = refl

HasDays-irrelevant : ∀ {ym days} → (p q : ym HasDays days) → p ≡ q
HasDays-irrelevant (mkHasDays hasYearType₁ hasDays₁) (mkHasDays hasYearType₂ hasDays₂) with Y.yearType-unique hasYearType₁ hasYearType₂
... | refl with Y.HasYearType-irrelevant hasYearType₁ hasYearType₂ | M.HasDays-irrelevant hasDays₁ hasDays₂
... | refl | refl = refl

