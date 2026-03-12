module Gregorianum.Date.Base where

open import Gregorianum.Year using (Year; _HasYearType_; YearType)
open import Gregorianum.YearMonth as YM using (YearMonth; _HasDays_)
import Gregorianum.Month as M
open import Gregorianum.Day using (Day)
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
import Gregorianum.Data.Cursor.Properties as Cursor
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.Nat using (ℕ; zero; suc)

record Date : Set where
  constructor mkDate
  field
    yearMonth : YearMonth
    {width} : ℕ
    hasDays : yearMonth HasDays suc width -- suc width ≡ days
    day : Day width

  open YearMonth yearMonth public

pattern _-_⟨_⟩ ym d hasDays = mkDate ym hasDays d

data _⋖_ : Date → Date → Set where
  stepᵈ : ∀ {ym : YearMonth} {width acc rem}
        → {hasDays : ym HasDays (suc width)}
        → {c : Cursor width acc (suc rem)}
        → (ym - mkPos c ⟨ hasDays ⟩) ⋖ (ym - mkPos (suc c) ⟨ hasDays ⟩)
  stepʸᵐ : ∀ {ym₁ ym₂ width₁ width₂}
         → {hasDays₁ : ym₁ HasDays (suc width₁)}
         → {hasDays₂ : ym₂ HasDays (suc width₂)}
         → {c : Cursor width₁ width₁ 0}
         → ym₁ YM.⋖ ym₂
         → (ym₁ - mkPos c ⟨ hasDays₁ ⟩) ⋖ (ym₂ - mkPos first ⟨ hasDays₂ ⟩)

data IsSuccessor : Date → Set where
  sucᵈ : ∀ {ym width acc rem}
       → {hasDays : ym HasDays (suc width)}
       → {c : Cursor width (suc acc) rem}
       → IsSuccessor (mkDate ym hasDays (mkPos c))
  sucʸᵐ : ∀ {ym width rem}
        → {hasDays : ym HasDays (suc width)}
        → {c : Cursor width zero rem}
        → YM.IsSuccessor ym → IsSuccessor (ym - mkPos c ⟨ hasDays ⟩)

nextDate : ∀ (d₁ : Date) → ∃[ d₂ ] d₁ ⋖ d₂
nextDate (yearMonth - mkPos {rem = suc rem } cursor ⟨ hasDays ⟩) = (yearMonth - mkPos (suc cursor) ⟨ hasDays ⟩) , stepᵈ
nextDate (yearMonth - mkPos {rem = zero} cursor ⟨ hasDays ⟩) with YM.nextYearMonth yearMonth
... | ym' , ym⋖ym' with YM.days ym'
... | suc width , hasDays' = (ym' - mkPos first ⟨ hasDays' ⟩) , h
  where
    h : (yearMonth - mkPos cursor ⟨ hasDays ⟩) ⋖ (ym' - mkPos first ⟨ hasDays' ⟩)
    h with Cursor.rem≡0⇒width≡acc cursor
    ... | refl = stepʸᵐ ym⋖ym'

prevDate : ∀ (d₂ : Date) → IsSuccessor d₂ → ∃[ d₁ ] d₁ ⋖ d₂
prevDate (ym - mkPos {acc = suc acc} (suc c) ⟨ hasDays ⟩) sucᵈ = (ym - mkPos c ⟨ hasDays ⟩) , stepᵈ
prevDate (ym - mkPos {acc = zero} first ⟨ hasDays ⟩) (sucʸᵐ x) with YM.prevYearMonth ym x
... | ym' , ym'⋖ym with YM.days ym'
... | suc width , hasDays' = (ym' - mkPos last ⟨ hasDays' ⟩) , h
    where
      h : (ym' - mkPos last ⟨ hasDays' ⟩) ⋖ (ym - mkPos first ⟨ hasDays ⟩)
      h = stepʸᵐ ym'⋖ym
