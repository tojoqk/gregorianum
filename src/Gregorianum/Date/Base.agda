module Gregorianum.Date.Base where

open import Gregorianum.Year using (_×₄₀₀+_×₁₀₀+_×₄+_; Year; _HasYearType_; YearType; yearType; leap; common; leap₄₀₀)
open import Gregorianum.Year.Properties using (common⇒IsSuc)
open import Gregorianum.Year.Weight.Base using (_HasLeapWeight_; _HasCommonWeight_; weight)
open import Gregorianum.Year.Weight.Properties using (IsSuc⇒suc-common-weight)
open import Gregorianum.YearMonth.Base as YM using (YearMonth; year-month-first; _HasDays_; _-_; mkHasDays)
import Gregorianum.YearMonth.Properties as YM
open import Gregorianum.Month using ([_]; january; january-days; _HasDayWeight_; dayWeight)
open import Gregorianum.Day using (Day; [_])
open import Gregorianum.Data.Cursor using (Cursor; zero; suc; first; last)
open import Gregorianum.Data.Cursor.Position using (Position; mkPos)
open import Gregorianum.Data.Cursor.Properties using (rem≡0⇒width≡acc)

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; NonZero)
open import Data.Product using (∃-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

record Date : Set where
  constructor mkDate
  field
    yearMonth : YearMonth
    {width} : ℕ
    hasDays : yearMonth HasDays suc width -- suc width ≡ days
    day : Day width

  open YearMonth yearMonth public

pattern _-_⟨_⟩ ym d hasDays = mkDate ym hasDays d
pattern date-first = year-month-first - [ mkPos first ] ⟨ mkHasDays leap₄₀₀ january-days ⟩

data _⋖_ : Date → Date → Set where
  step-day : ∀ {ym : YearMonth} {width acc rem}
        → {hasDays : ym HasDays (suc width)}
        → {c : Cursor width acc (suc rem)}
        → (ym - [ mkPos c ] ⟨ hasDays ⟩) ⋖ (ym - [ mkPos (suc c) ] ⟨ hasDays ⟩)
  step-month : ∀ {ym₁ ym₂ width₁ width₂}
         → {hasDays₁ : ym₁ HasDays (suc width₁)}
         → {hasDays₂ : ym₂ HasDays (suc width₂)}
         → {c : Cursor width₁ width₁ 0}
         → ym₁ YM.⋖ ym₂
         → (ym₁ - [ mkPos c ] ⟨ hasDays₁ ⟩) ⋖ (ym₂ - [ mkPos first ] ⟨ hasDays₂ ⟩)

data IsSuc : Date → Set where
  suc-day : ∀ {acc rem}
       → {c : Cursor 30 (suc acc) rem}
       → IsSuc (year-month-first - [ mkPos c ] ⟨ YM.mkHasDays leap₄₀₀ january-days ⟩)
  suc-month : ∀ {ym width acc rem}
        → {hasDays : ym HasDays (suc width)}
        → {c : Cursor width acc rem}
        → YM.IsSuc ym → IsSuc (ym - [ mkPos c ] ⟨ hasDays ⟩)

next : ∀ (d₁ : Date) → ∃[ d₂ ] d₁ ⋖ d₂
next (yearMonth - [ mkPos {rem = suc rem } cursor ] ⟨ hasDays ⟩) = (yearMonth - [ mkPos (suc cursor) ] ⟨ hasDays ⟩) , step-day
next (yearMonth - [ mkPos {rem = zero} cursor ] ⟨ hasDays ⟩) with YM.next yearMonth
... | ym' , ym⋖ym' with YM.days ym'
... | suc width , hasDays' = (ym' - [ mkPos first ] ⟨ hasDays' ⟩) , h
  where
    h : (yearMonth - [ mkPos cursor ] ⟨ hasDays ⟩)  ⋖ (ym' - [ mkPos first ] ⟨ hasDays' ⟩)
    h with rem≡0⇒width≡acc cursor
    ... | refl = step-month ym⋖ym'

prev : ∀ (d₂ : Date) → IsSuc d₂ → ∃[ d₁ ] d₁ ⋖ d₂
prev (yearMonth - [ mkPos (suc c) ] ⟨ hasDays ⟩) _ = (yearMonth - [ mkPos c ] ⟨ hasDays ⟩) , step-day
prev (ym - [ mkPos first ] ⟨ hasDays ⟩) (suc-month p)  with YM.prev ym p
... | ym' , ym'⋖ym with YM.days ym'
... | suc ds , hd = (ym' - [ mkPos last ] ⟨ hd ⟩) , h
  where
    h : (ym' - [ mkPos last ] ⟨ hd ⟩) ⋖ (ym - [ mkPos first ] ⟨ hasDays ⟩)
    h = step-month ym'⋖ym

data _HasOrdinal_ (d : Date) : (n : ℕ) → Set where
  leap-ordinal : ∀ {yl yc ymo}
                   → (Date.year d) HasYearType leap
                   → (Date.year d) HasLeapWeight (suc yl)
                   → (Date.year d) HasCommonWeight yc
                   → (leap , Date.month d) HasDayWeight ymo
                   → d HasOrdinal (Position.toℕ (Day.position (Date.day d)) + ymo + yl * 366 + yc * 365)
  common-ordinal : ∀ {yl yc ymo}
                     → {{_ : NonZero yl}}
                     → (Date.year d) HasYearType common
                     → (Date.year d) HasLeapWeight yl
                     → (Date.year d) HasCommonWeight (suc yc)
                     → (common , Date.month d) HasDayWeight ymo
                     → d HasOrdinal (Position.toℕ (Day.position (Date.day d)) + ymo + yl * 366 + yc * 365)

toOrdinal : (d : Date) → ∃[ n ] d HasOrdinal n
toOrdinal d with yearType (Date.year d)
toOrdinal d | leap , p with dayWeight (leap , Date.month d)
toOrdinal d | leap , p | w , q = _ , leap-ordinal p weight weight q
toOrdinal d | common , p with dayWeight (common , Date.month d)
... | w , q with IsSuc⇒suc-common-weight (common⇒IsSuc p)
... | ycw , q' = _ , common-ordinal p weight q' q

_<_ : Date → Date → Set
d₁ < d₂ = proj₁ (toOrdinal d₁) ℕ.< proj₁ (toOrdinal d₂)

isSuc? : ∀ d → Dec (IsSuc d)
isSuc? (ym - d ⟨ hasDays ⟩) with YM.isSuc? ym
... | yes h = yes (suc-month h)
isSuc? (ym - [ mkPos (suc cursor) ] ⟨ hasDays ⟩) | no ¬h = yes h
  where
    h : IsSuc (ym - [ mkPos (suc cursor) ] ⟨ hasDays ⟩)
    h with YM.¬IsSuc⇒first ¬h
    ... | refl with YM.days-unique hasDays (YM.mkHasDays leap₄₀₀ january-days)
    ... | refl with YM.has-days-irrelevant hasDays (YM.mkHasDays leap₄₀₀ january-days)
    ... | refl = suc-day
isSuc? (ym - [ mkPos first ] ⟨ hasDays ⟩) | no ¬h = no h
  where
    h : ¬ IsSuc (ym - [ mkPos first ] ⟨ hasDays ⟩)
    h (suc-month x) = ¬h x
