module Gregorianum.Date.Properties where

open import Gregorianum.Date.Base

open import Gregorianum.Day.Base using (Day; [_])
open import Gregorianum.YearMonth.Base as YM using (step-year; step-month; _-_; mkHasDays)
open import Gregorianum.Year.Base using (leap; common; common₁; leap₄₀₀; leap₄; common₁₀₀; _×₄₀₀+_×₁₀₀+_×₄+_)
open import Gregorianum.Year.Properties using (year-type-unique)
open import Gregorianum.Year.Weight.Base using () renaming (weight to year-weight)
open import Gregorianum.Year.Weight.Properties using (next-leap-is-common; next-leap-common-weight; leap-weight-unique; common-weight-unique)
open import Gregorianum.Month.Base using (january-weight; january; january-days; december-days; december-leap-weight; december-common-weight; [_])
open import Gregorianum.YearMonth.Properties as YM using (days-unique; has-days-irrelevant)
open import Gregorianum.Month.Properties using (next-month-day-weight; day-weight-unique)
open import Gregorianum.Data.Cursor using (suc; first)
open import Gregorianum.Data.Position using (mkPos)
open import Gregorianum.Data.Cursor.Properties using () renaming (unique to cursor-unique)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; ≤-refl)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂; _×_)
open import Induction.WellFounded using (WellFounded; module Subrelation)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)
import Relation.Binary.Construct.On as On

next-unique : ∀ {d₁ d₂ d₃ : Date}
                → d₁ ⋖ d₂
                → d₁ ⋖ d₃
                → d₂ ≡ d₃
next-unique step-day step-day = refl
next-unique (step-month p) (step-month q) with YM.next-unique p q
next-unique {_} {ym₂ - d₂ ⟨ hasDays₂ ⟩} {_ - _ ⟨ hasDays₃ ⟩} (step-month p) (step-month q) | refl with days-unique hasDays₂ hasDays₃
... | refl with has-days-irrelevant hasDays₂ hasDays₃
... | refl = refl

prev-unique : ∀ {d₁ d₂ d₃ : Date}
                 → d₁ ⋖ d₃
                 → d₂ ⋖ d₃
                 → d₁ ≡ d₂
prev-unique step-day step-day = refl
prev-unique (step-month p) (step-month q) with YM.prev-unique p q
prev-unique {_ - [ mkPos c₁ ] ⟨ hasDays₁ ⟩} {_ - [ mkPos c₂ ] ⟨ hasDays₂ ⟩} (step-month p) (step-month q) | refl with days-unique hasDays₁ hasDays₂
... | refl with has-days-irrelevant hasDays₁ hasDays₂
... | refl with cursor-unique c₁ c₂
... | refl = refl

<-WellFounded : WellFounded _<_
<-WellFounded d = On.accessible (proj₁ ∘ toOrdinal) (<-wellFounded-fast (proj₁ (toOrdinal d)))

private
  pattern suc⁵ n = suc (suc (suc (suc (suc n))))
  pattern suc¹⁰ n = suc⁵ (suc⁵ n)
  pattern suc⁵⁰ n = suc¹⁰ (suc¹⁰ (suc¹⁰ (suc¹⁰ (suc¹⁰ n))))
  pattern suc¹⁰⁰ n = suc⁵⁰ (suc⁵⁰ n)
  pattern suc³⁶⁵ n = suc¹⁰⁰ (suc¹⁰⁰ (suc¹⁰⁰ (suc⁵⁰ (suc¹⁰ (suc⁵ n)))))
  pattern suc³⁶⁶ n = suc¹⁰⁰ (suc¹⁰⁰ (suc¹⁰⁰ (suc⁵⁰ (suc¹⁰ (suc⁵ (suc n))))))

next-ordinal : ∀ {d₁ d₂ n} → d₁ ⋖ d₂ → d₁ HasOrdinal n → d₂ HasOrdinal (suc n)
next-ordinal step-day (leap-ordinal hasYearType hlw hcw hdw) = leap-ordinal hasYearType hlw hcw hdw
next-ordinal step-day (common-ordinal hasYearType hlw hcw hdw) = common-ordinal hasYearType hlw hcw hdw
next-ordinal (step-month (step-year y₁⋖y₂)) (leap-ordinal hasYearType hlw hcw hdw) with next-leap-is-common y₁⋖y₂ hasYearType | next-leap-common-weight y₁⋖y₂ hlw hcw
next-ordinal {(y - december) - [ mkPos thirty-first ] ⟨ mkHasDays _ december-days ⟩} (step-month (step-year y₁⋖y₂)) (leap-ordinal hasYearType hlw hcw december-leap-weight) | hyt | inj₂ (_ , hlw' , hcw') = common-ordinal hyt hlw' hcw' january-weight
... | common₁ | inj₁ (() , _)
... | common₁₀₀ | inj₁ (() , _)
next-ordinal (step-month (step-year y₁⋖y₂)) (common-ordinal hasYearType hlw hcw hdw) with next-leap-common-weight y₁⋖y₂ hlw hcw
next-ordinal {(y - december) - [ mkPos thirty-first ] ⟨ mkHasDays _ december-days ⟩} {d₂} (step-month (step-year y₁⋖y₂)) (common-ordinal {yl} {yc} hasYearType hlw hcw december-common-weight) | inj₁ (hyt , hlw' , hcw') = subst (d₂ HasOrdinal_) (trans (+-comm (yl * 366) (365 + (yc * 365))) (cong (365 +_) (+-comm (yc * 365) (yl * 366)))) (leap-ordinal hyt hlw' hcw' january-weight)
next-ordinal {(y - december) - [ mkPos thirty-first ] ⟨ mkHasDays _ december-days ⟩} {d₂} (step-month (step-year y₁⋖y₂)) (common-ordinal {yl} {yc} hasYearType hlw hcw december-common-weight) | inj₂ (hyt , hlw' , hcw') = subst (d₂ HasOrdinal_) (trans (+-comm (yl * 366) (365 + (yc * 365))) (cong (365 +_) (+-comm (yc * 365) (yl * 366)))) (common-ordinal hyt hlw' hcw' january-weight)
next-ordinal {_ - _ ⟨ mkHasDays {leap} hasYearType hasDays ⟩} (step-month step-month) (leap-ordinal hyt hlw hcw hdw) with next-month-day-weight hasDays hdw
... | h = leap-ordinal hyt hlw hcw h
next-ordinal {_ - _ ⟨ mkHasDays {common} () hasDays ⟩} (step-month step-month) (leap-ordinal leap₄ hlw hcw hdw)
next-ordinal {_ - _ ⟨ mkHasDays {common} () hasDays ⟩} (step-month step-month) (leap-ordinal leap₄₀₀ hlw hcw hdw)
next-ordinal {_ - _ ⟨ mkHasDays {common} hasYearType hasDays ⟩} (step-month step-month) (common-ordinal hyt hlw hcw hdw) with next-month-day-weight hasDays hdw
... | h = common-ordinal hyt hlw hcw h
next-ordinal {_ - _ ⟨ mkHasDays {leap} () hasDays ⟩} (step-month step-month) (common-ordinal common₁ hlw hcw hdw)
next-ordinal {_ - _ ⟨ mkHasDays {leap} () hasDays ⟩} (step-month step-month) (common-ordinal common₁₀₀ hlw hcw hdw)

ordinal-unique : ∀ {d n₁ n₂} → d HasOrdinal n₁ → d HasOrdinal n₂ → n₁ ≡ n₂
ordinal-unique (leap-ordinal hyt hlw hcw hdw) (leap-ordinal hyt' hlw' hcw' hdw') with year-type-unique hyt hyt' | leap-weight-unique hlw hlw' | common-weight-unique hcw hcw' | day-weight-unique hdw hdw'
... | refl | refl | refl | refl = refl
ordinal-unique (common-ordinal hyt hlw hcw hdw) (common-ordinal hyt' hlw' hcw' hdw') with year-type-unique hyt hyt' | leap-weight-unique hlw hlw' | common-weight-unique hcw hcw' | day-weight-unique hdw hdw'
... | refl | refl | refl | refl = refl
ordinal-unique (leap-ordinal leap₄ _ _ _) (common-ordinal () _ _ _)
ordinal-unique (leap-ordinal leap₄₀₀ _ _ _) (common-ordinal () _ _ _)
ordinal-unique (common-ordinal common₁ _ _ _) (leap-ordinal () _ _ _)
ordinal-unique (common-ordinal common₁₀₀ _ _ _) (leap-ordinal () _ _ _)

⋖⇒suc : ∀ {d₁ d₂} → d₁ ⋖ d₂ → ∃[ n ] (d₁ HasOrdinal n) × (d₂ HasOrdinal (suc n)) 
⋖⇒suc {d₁} {d₂} d₁⋖d₂ with toOrdinal d₁
... | n , ho₁ with next-ordinal d₁⋖d₂ ho₁
... | ho₂ = n , ho₁ , ho₂

⋖⇒< : ∀ {d₁ d₂} → d₁ ⋖ d₂ → d₁ < d₂
⋖⇒< {d₁} {d₂} d₁⋖d₂ with ⋖⇒suc d₁⋖d₂ | toOrdinal d₁ | toOrdinal d₂
... | n , ho₁ , ho₂ | n₁ , ho₁' | n₂ , ho₂' with ordinal-unique ho₁ ho₁' | ordinal-unique ho₂ ho₂'
... | refl | refl = ≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded d = Subrelation.accessible ⋖⇒< (<-WellFounded d)

IsSuc⇒suc-ordinal : ∀ {d} → IsSuc d → ∃[ n ] d HasOrdinal (suc n)
IsSuc⇒suc-ordinal {d} isSuc with prev d isSuc
... | d' , d'⋖d with toOrdinal d'
... | n' , ho' = n' , (next-ordinal d'⋖d ho')

¬IsSuc⇒first : ∀ {d} → ¬ IsSuc d → d ≡ date-first
¬IsSuc⇒first {ym - d ⟨ hd ⟩} ¬isSuc with YM.isSuc? ym
... | yes h = contradiction (suc-month h) ¬isSuc
... | no ¬h with YM.¬IsSuc⇒first ¬h
¬IsSuc⇒first {ym - [ mkPos first ] ⟨ mkHasDays leap₄₀₀ january-days ⟩} ¬isSuc | no ¬h | refl = refl
¬IsSuc⇒first {ym - [ mkPos (suc cursor) ] ⟨ mkHasDays leap₄₀₀ january-days ⟩} ¬isSuc | no ¬h | refl = contradiction suc-day ¬isSuc

¬isSuc-unique : ∀ {d₁ d₂} → ¬ IsSuc d₁ → ¬ IsSuc d₂ → d₁ ≡ d₂
¬isSuc-unique ¬isSuc₁ ¬isSuc₂ with ¬IsSuc⇒first ¬isSuc₁ | ¬IsSuc⇒first ¬isSuc₂
... | refl | refl = refl

∃prev⇒IsSuc : ∀ {d₁ d₂ : Date} → d₁ ⋖ d₂ → IsSuc d₂
∃prev⇒IsSuc {_} {ym - d₂ ⟨ hd ⟩} d with YM.isSuc? ym
... | yes p = suc-month p
... | no p with YM.¬IsSuc⇒first p
∃prev⇒IsSuc {_} {_ - _ ⟨ mkHasDays leap₄₀₀ january-days ⟩} step-day | no _ | refl = suc-day
∃prev⇒IsSuc {_} {ym - d₂ ⟨ hd ⟩} (step-month (step-year ())) | no p | refl

ordinal≡0⇒first : ∀ {d} → d HasOrdinal 0 → d ≡ date-first
ordinal≡0⇒first {d} p with isSuc? d
ordinal≡0⇒first {d} ho | yes isSuc with IsSuc⇒suc-ordinal isSuc
... | _ , ho' with ordinal-unique ho ho'
... | ()
ordinal≡0⇒first {d} ho | no ¬isSuc with ¬IsSuc⇒first ¬isSuc
... | refl = refl

suc-ordinal⇒IsSuc : ∀ {d n} → d HasOrdinal (suc n) → IsSuc d
suc-ordinal⇒IsSuc {yearMonth - day ⟨ hasDays ⟩} {n} ho with YM.isSuc? yearMonth
... | yes h = suc-month h
... | no ¬h with YM.¬IsSuc⇒first ¬h
suc-ordinal⇒IsSuc {yearMonth - [ mkPos (suc cursor) ] ⟨ mkHasDays leap₄₀₀ january-days ⟩} {n} ho | no ¬h | refl = suc-day
suc-ordinal⇒IsSuc {yearMonth - [ mkPos first ] ⟨ mkHasDays leap₄₀₀ january-days ⟩} {n} ho | no ¬h | refl with ordinal-unique ho (leap-ordinal leap₄₀₀ year-weight year-weight january-weight)
... | ()

prev-ordinal : ∀ {d₁ d₂ n} → d₁ ⋖ d₂ → d₂ HasOrdinal (suc n) → d₁ HasOrdinal n
prev-ordinal d₁⋖d₂ ho with ⋖⇒suc d₁⋖d₂
... | _ , ho₁ , ho₂ with ordinal-unique ho ho₂
... | refl = ho₁

date-unique : ∀ {d₁ d₂ n} → d₁ HasOrdinal n → d₂ HasOrdinal n → d₁ ≡ d₂
date-unique {d₁} {d₂} {zero} ho₁ ho₂ with ordinal≡0⇒first ho₁ | ordinal≡0⇒first ho₂
... | refl | refl = refl
date-unique {d₁} {d₂} {suc n} ho₁ ho₂ with suc-ordinal⇒IsSuc ho₁ | suc-ordinal⇒IsSuc ho₂
... | isSuc₁ | isSuc₂ with prev d₁ isSuc₁ | prev d₂ isSuc₂
... | d₁' , d₁'⋖d₁ | d₂' , d₂'⋖d₂ with prev-ordinal d₁'⋖d₁ ho₁ | prev-ordinal d₂'⋖d₂ ho₂
... | ho₁' | ho₂' with date-unique ho₁' ho₂'
... | refl with next-unique d₁'⋖d₁ d₂'⋖d₂
... | refl = refl
