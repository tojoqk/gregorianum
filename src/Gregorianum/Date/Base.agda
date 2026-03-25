module Gregorianum.Date.Base where

open import Gregorianum.Year as Y using (Year; _HasYearType_; YearType; leap; common)
open import Gregorianum.Year.Properties as Y
import Gregorianum.Month.Base as M
open import Gregorianum.Year.Weight.Base as Y
open import Gregorianum.Year.Weight.Properties as Y
open import Gregorianum.YearMonth as YM using (YearMonth; _HasDays_)
import Gregorianum.YearMonth.Properties as YM
import Gregorianum.Month as M
open import Gregorianum.Day using (Day)
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position hiding (_<_)
import Gregorianum.Data.Cursor.Properties as Cursor
open import Data.Product using (∃-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; NonZero)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

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
  sucᵈ : ∀ {acc rem}
       → {c : Cursor 30 (suc acc) rem}
       → IsSuccessor (((zero Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) YM.- mkPos first) - (mkPos c) ⟨ YM.mkHasDays Y.leap₄₀₀ M.january-days ⟩ )
  sucʸᵐ : ∀ {ym width acc rem}
        → {hasDays : ym HasDays (suc width)}
        → {c : Cursor width acc rem}
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
prevDate (yearMonth - mkPos (suc c) ⟨ hasDays ⟩) _ = (yearMonth - mkPos c ⟨ hasDays ⟩) , stepᵈ
prevDate (ym - mkPos first ⟨ hasDays ⟩) (sucʸᵐ p)  with YM.prevYearMonth ym p
... | ym' , ym'⋖ym with YM.days ym'
... | suc ds , hd = (ym' - mkPos last ⟨ hd ⟩) , h
  where
    h : (ym' - mkPos last ⟨ hd ⟩) ⋖ (ym - mkPos first ⟨ hasDays ⟩)
    h = stepʸᵐ ym'⋖ym

data _HasOrdinal_ (d : Date) : (n : ℕ) → Set where
  has-leap-ordinal : ∀ {yl yc ymo}
                   → (Date.year d) HasYearType Y.leap
                   → (Date.year d) Y.HasLeapWeight (suc yl)
                   → (Date.year d) Y.HasCommonWeight yc
                   → (Y.leap , Date.month d) M.HasDayWeight ymo
                   → d HasOrdinal (Position.toℕ (Date.day d) + ymo + yl * 366 + yc * 365)
  has-common-ordinal : ∀ {yl yc ymo}
                     → {{_ : NonZero yl}}
                     → (Date.year d) HasYearType Y.common
                     → (Date.year d) Y.HasLeapWeight yl
                     → (Date.year d) Y.HasCommonWeight (suc yc)
                     → (Y.common , Date.month d) M.HasDayWeight ymo
                     → d HasOrdinal (Position.toℕ (Date.day d) + ymo + yl * 366 + yc * 365)

toOrdinal : (d : Date) → ∃[ n ] d HasOrdinal n
toOrdinal d with Y.yearType (Date.year d)
toOrdinal d | leap , p with M.dayWeight (leap , Date.month d)
toOrdinal d | leap , p | w , q = _ , has-leap-ordinal p Y.has-weight Y.has-weight q
toOrdinal d | common , p with M.dayWeight (common , Date.month d)
... | w , q with Y.is-successor⇒suc-common-weight (Y.common⇒is-successor p)
... | ycw , q' = _ , has-common-ordinal p has-weight q' q

_<_ : Date → Date → Set
d₁ < d₂ = proj₁ (toOrdinal d₁) ℕ.< proj₁ (toOrdinal d₂)

isSuccessor? : ∀ d → Dec (IsSuccessor d)
isSuccessor? (ym - d ⟨ hasDays ⟩) with YM.isSuccessor? ym
... | yes h = yes (sucʸᵐ h)
isSuccessor? (ym - mkPos (suc cursor) ⟨ hasDays ⟩) | no ¬h = yes h
  where
    h : IsSuccessor (ym - mkPos (suc cursor) ⟨ hasDays ⟩)
    h with YM.¬IsSuccessor⇒first ¬h
    ... | refl with YM.days-unique hasDays (YM.mkHasDays Y.leap₄₀₀ M.january-days)
    ... | refl with YM.has-days-irrelevant hasDays (YM.mkHasDays Y.leap₄₀₀ M.january-days)
    ... | refl = sucᵈ
isSuccessor? (ym - mkPos first ⟨ hasDays ⟩) | no ¬h = no h
  where
    h : ¬ IsSuccessor (ym - mkPos first ⟨ hasDays ⟩)
    h (sucʸᵐ x) = ¬h x
