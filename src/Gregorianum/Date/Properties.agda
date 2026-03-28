module Gregorianum.Date.Properties where

open import Gregorianum.Date.Base

open import Gregorianum.Day.Base
import Gregorianum.YearMonth.Base as YM
import Gregorianum.Month.Base as M
import Gregorianum.Year.Base as Y
import Gregorianum.Year.Properties as Y
import Gregorianum.Year.Weight.Base as Y
import Gregorianum.Year.Weight.Properties as Y
open import Gregorianum.Month.Base as M
open import Gregorianum.Month.Properties as M
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position hiding (_<_)
open import Gregorianum.Data.Cursor.Properties as Cursor
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Gregorianum.YearMonth.Properties as YM
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
import Data.Nat.Properties as ℕ
import Data.Nat.Induction as ℕ
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; trans)
open import Induction.WellFounded
import Relation.Binary.Construct.On as On
open import Function using (_∘_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

next-unique : ∀ {d₁ d₂ d₃ : Date}
                → d₁ ⋖ d₂
                → d₁ ⋖ d₃
                → d₂ ≡ d₃
next-unique stepᵈ stepᵈ = refl
next-unique (stepʸᵐ p) (stepʸᵐ q) with YM.next-unique p q
next-unique {_} {ym₂ - d₂ ⟨ hasDays₂ ⟩} {_ - _ ⟨ hasDays₃ ⟩} (stepʸᵐ p) (stepʸᵐ q) | refl with YM.days-unique hasDays₂ hasDays₃
... | refl with YM.has-days-irrelevant hasDays₂ hasDays₃
... | refl = refl

prev-unique : ∀ {d₁ d₂ d₃ : Date}
                 → d₁ ⋖ d₃
                 → d₂ ⋖ d₃
                 → d₁ ≡ d₂
prev-unique stepᵈ stepᵈ = refl
prev-unique (stepʸᵐ p) (stepʸᵐ q) with YM.prev-unique p q
prev-unique {_ - [ mkPos c₁ ] ⟨ hasDays₁ ⟩} {_ - [ mkPos c₂ ] ⟨ hasDays₂ ⟩} (stepʸᵐ p) (stepʸᵐ q) | refl with YM.days-unique hasDays₁ hasDays₂
... | refl with YM.has-days-irrelevant hasDays₁ hasDays₂
... | refl with Cursor.unique c₁ c₂
... | refl = refl

<-WellFounded : WellFounded _<_
<-WellFounded d = On.accessible (proj₁ ∘ toOrdinal) (ℕ.<-wellFounded-fast (proj₁ (toOrdinal d)))

private
  pattern suc⁵ n = suc (suc (suc (suc (suc n))))
  pattern suc¹⁰ n = suc⁵ (suc⁵ n)
  pattern suc⁵⁰ n = suc¹⁰ (suc¹⁰ (suc¹⁰ (suc¹⁰ (suc¹⁰ n))))
  pattern suc¹⁰⁰ n = suc⁵⁰ (suc⁵⁰ n)
  pattern suc³⁶⁵ n = suc¹⁰⁰ (suc¹⁰⁰ (suc¹⁰⁰ (suc⁵⁰ (suc¹⁰ (suc⁵ n)))))
  pattern suc³⁶⁶ n = suc¹⁰⁰ (suc¹⁰⁰ (suc¹⁰⁰ (suc⁵⁰ (suc¹⁰ (suc⁵ (suc n))))))

next-ordinal : ∀ {d₁ d₂ n} → d₁ ⋖ d₂ → d₁ HasOrdinal n → d₂ HasOrdinal (suc n)
next-ordinal stepᵈ (has-leap-ordinal hasYearType hlw hcw hdw) = has-leap-ordinal hasYearType hlw hcw hdw
next-ordinal stepᵈ (has-common-ordinal hasYearType hlw hcw hdw) = has-common-ordinal hasYearType hlw hcw hdw
next-ordinal (stepʸᵐ (YM.stepʸ y₁⋖y₂)) (has-leap-ordinal hasYearType hlw hcw hdw) with Y.next-leap-is-common y₁⋖y₂ hasYearType | Y.next-leap-common-weight y₁⋖y₂ hlw hcw
next-ordinal {(y YM.- december) - [ mkPos thirty-first ] ⟨ YM.mkHasDays _ M.december-days ⟩} (stepʸᵐ (YM.stepʸ y₁⋖y₂)) (has-leap-ordinal hasYearType hlw hcw december-leap-weight) | hyt | inj₂ (_ , hlw' , hcw') = has-common-ordinal hyt hlw' hcw' M.january-weight
... | Y.common | inj₁ (() , _)
... | Y.common₁₀₀ | inj₁ (() , _)
next-ordinal (stepʸᵐ (YM.stepʸ y₁⋖y₂)) (has-common-ordinal hasYearType hlw hcw hdw) with Y.next-leap-common-weight y₁⋖y₂ hlw hcw
next-ordinal {(y YM.- december) - [ mkPos thirty-first ] ⟨ YM.mkHasDays _ M.december-days ⟩} {d₂} (stepʸᵐ (YM.stepʸ y₁⋖y₂)) (has-common-ordinal {yl} {yc} hasYearType hlw hcw december-common-weight) | inj₁ (hyt , hlw' , hcw') = subst (d₂ HasOrdinal_) (trans (ℕ.+-comm (yl * 366) (365 + (yc * 365))) (cong (365 +_) (ℕ.+-comm (yc * 365) (yl * 366)))) (has-leap-ordinal hyt hlw' hcw' M.january-weight)
next-ordinal {(y YM.- december) - [ mkPos thirty-first ] ⟨ YM.mkHasDays _ M.december-days ⟩} {d₂} (stepʸᵐ (YM.stepʸ y₁⋖y₂)) (has-common-ordinal {yl} {yc} hasYearType hlw hcw december-common-weight) | inj₂ (hyt , hlw' , hcw') = subst (d₂ HasOrdinal_) (trans (ℕ.+-comm (yl * 366) (365 + (yc * 365))) (cong (365 +_) (ℕ.+-comm (yc * 365) (yl * 366)))) (has-common-ordinal hyt hlw' hcw' M.january-weight)
next-ordinal {_ - _ ⟨ YM.mkHasDays {Y.leap} hasYearType hasDays ⟩} (stepʸᵐ YM.stepᵐ) (has-leap-ordinal hyt hlw hcw hdw) with M.next-month-day-weight hasDays hdw
... | h = has-leap-ordinal hyt hlw hcw h
next-ordinal {_ - _ ⟨ YM.mkHasDays {Y.common} () hasDays ⟩} (stepʸᵐ YM.stepᵐ) (has-leap-ordinal Y.leap₄ hlw hcw hdw)
next-ordinal {_ - _ ⟨ YM.mkHasDays {Y.common} () hasDays ⟩} (stepʸᵐ YM.stepᵐ) (has-leap-ordinal Y.leap₄₀₀ hlw hcw hdw)
next-ordinal {_ - _ ⟨ YM.mkHasDays {Y.common} hasYearType hasDays ⟩} (stepʸᵐ YM.stepᵐ) (has-common-ordinal hyt hlw hcw hdw) with M.next-month-day-weight hasDays hdw
... | h = has-common-ordinal hyt hlw hcw h
next-ordinal {_ - _ ⟨ YM.mkHasDays {Y.leap} () hasDays ⟩} (stepʸᵐ YM.stepᵐ) (has-common-ordinal Y.common hlw hcw hdw)
next-ordinal {_ - _ ⟨ YM.mkHasDays {Y.leap} () hasDays ⟩} (stepʸᵐ YM.stepᵐ) (has-common-ordinal Y.common₁₀₀ hlw hcw hdw)

ordinal-unique : ∀ {d n₁ n₂} → d HasOrdinal n₁ → d HasOrdinal n₂ → n₁ ≡ n₂
ordinal-unique (has-leap-ordinal hyt hlw hcw hdw) (has-leap-ordinal hyt' hlw' hcw' hdw') with Y.year-type-unique hyt hyt' | Y.leap-weight-unique hlw hlw' | Y.common-weight-unique hcw hcw' | day-weight-unique hdw hdw'
... | refl | refl | refl | refl = refl
ordinal-unique (has-common-ordinal hyt hlw hcw hdw) (has-common-ordinal hyt' hlw' hcw' hdw') with Y.year-type-unique hyt hyt' | Y.leap-weight-unique hlw hlw' | Y.common-weight-unique hcw hcw' | day-weight-unique hdw hdw'
... | refl | refl | refl | refl = refl
ordinal-unique (has-leap-ordinal Y.leap₄ _ _ _) (has-common-ordinal () _ _ _)
ordinal-unique (has-leap-ordinal Y.leap₄₀₀ _ _ _) (has-common-ordinal () _ _ _)
ordinal-unique (has-common-ordinal Y.common _ _ _) (has-leap-ordinal () _ _ _)
ordinal-unique (has-common-ordinal Y.common₁₀₀ _ _ _) (has-leap-ordinal () _ _ _)

⋖⇒suc : ∀ {d₁ d₂} → d₁ ⋖ d₂ → ∃[ n ] (d₁ HasOrdinal n) × (d₂ HasOrdinal (suc n)) 
⋖⇒suc {d₁} {d₂} d₁⋖d₂ with toOrdinal d₁
... | n , ho₁ with next-ordinal d₁⋖d₂ ho₁
... | ho₂ = n , ho₁ , ho₂

⋖⇒< : ∀ {d₁ d₂} → d₁ ⋖ d₂ → d₁ < d₂
⋖⇒< {d₁} {d₂} d₁⋖d₂ with ⋖⇒suc d₁⋖d₂ | toOrdinal d₁ | toOrdinal d₂
... | n , ho₁ , ho₂ | n₁ , ho₁' | n₂ , ho₂' with ordinal-unique ho₁ ho₁' | ordinal-unique ho₂ ho₂'
... | refl | refl = ℕ.≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded d = Subrelation.accessible ⋖⇒< (<-WellFounded d)

private
  pattern date-first = ((zero Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) YM.- january) - [ mkPos first ] ⟨ YM.mkHasDays Y.leap₄₀₀ january-days ⟩

IsSuc⇒suc-ordinal : ∀ {d} → IsSuc d → ∃[ n ] d HasOrdinal (suc n)
IsSuc⇒suc-ordinal {d} isSuc with prev d isSuc
... | d' , d'⋖d with toOrdinal d'
... | n' , ho' = n' , (next-ordinal d'⋖d ho')

¬IsSuc⇒first : ∀ {d} → ¬ IsSuc d → d ≡ date-first
¬IsSuc⇒first {ym - d ⟨ hd ⟩} ¬isSuc with YM.isSuc? ym
... | yes h = contradiction (sucʸᵐ h) ¬isSuc
... | no ¬h with YM.¬IsSuc⇒first ¬h
¬IsSuc⇒first {ym - [ mkPos first ] ⟨ YM.mkHasDays Y.leap₄₀₀ january-days ⟩} ¬isSuc | no ¬h | refl = refl
¬IsSuc⇒first {ym - [ mkPos (suc cursor) ] ⟨ YM.mkHasDays Y.leap₄₀₀ january-days ⟩} ¬isSuc | no ¬h | refl = contradiction sucᵈ ¬isSuc

¬isSuc-unique : ∀ {d₁ d₂} → ¬ IsSuc d₁ → ¬ IsSuc d₂ → d₁ ≡ d₂
¬isSuc-unique ¬isSuc₁ ¬isSuc₂ with ¬IsSuc⇒first ¬isSuc₁ | ¬IsSuc⇒first ¬isSuc₂
... | refl | refl = refl

∃prev⇒IsSuc : ∀ {d₁ d₂ : Date} → d₁ ⋖ d₂ → IsSuc d₂
∃prev⇒IsSuc {_} {ym - d₂ ⟨ hd ⟩} d with YM.isSuc? ym
... | yes p = sucʸᵐ p
... | no p with YM.¬IsSuc⇒first p
∃prev⇒IsSuc {_} {_ - _ ⟨ YM.mkHasDays Y.leap₄₀₀ january-days ⟩} stepᵈ | no _ | refl = sucᵈ
∃prev⇒IsSuc {_} {ym - d₂ ⟨ hd ⟩} (stepʸᵐ (YM.stepʸ ())) | no p | refl

ordinal≡0⇒first : ∀ {d} → d HasOrdinal 0 → d ≡ date-first
ordinal≡0⇒first {d} p with isSuc? d
ordinal≡0⇒first {d} ho | yes isSuc with IsSuc⇒suc-ordinal isSuc
... | _ , ho' with ordinal-unique ho ho'
... | ()
ordinal≡0⇒first {d} ho | no ¬isSuc with ¬IsSuc⇒first ¬isSuc
... | refl = refl

suc-ordinal⇒IsSuc : ∀ {d n} → d HasOrdinal (suc n) → IsSuc d
suc-ordinal⇒IsSuc {yearMonth - day ⟨ hasDays ⟩} {n} ho with YM.isSuc? yearMonth
... | yes h = sucʸᵐ h
... | no ¬h with YM.¬IsSuc⇒first ¬h
suc-ordinal⇒IsSuc {yearMonth - [ mkPos (suc cursor) ] ⟨ YM.mkHasDays Y.leap₄₀₀ january-days ⟩} {n} ho | no ¬h | refl = sucᵈ
suc-ordinal⇒IsSuc {yearMonth - [ mkPos first ] ⟨ YM.mkHasDays Y.leap₄₀₀ january-days ⟩} {n} ho | no ¬h | refl with ordinal-unique ho (has-leap-ordinal Y.leap₄₀₀ Y.has-weight Y.has-weight january-weight)
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
