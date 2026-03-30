module Gregorianum.YearMonth.Properties where

open import Gregorianum.YearMonth.Base

open import Gregorianum.Year as Y using (common₁; common₁₀₀)
open import Gregorianum.Year.Properties as Y using (year-type-unique; has-type-irrelevant)
open import Gregorianum.Year.Weight.Base using (weight)
open import Gregorianum.Year.Weight.Properties using (next-weight; IsSuc⇒suc-weight)
open import Gregorianum.Month as M hiding (_HasDays_)
open import Gregorianum.Data.Cursor using (zero; suc; first)
open import Gregorianum.Data.Cursor.Position using (mkPos)
import Gregorianum.Month.Properties as M

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (suc-injective; ≤-refl)
import Data.Nat.Induction as ℕ
open import Data.Product using (∃-syntax; _×_; _,_; proj₁)
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)
import Relation.Binary.Construct.On as On
open import Function using (_∘_)

next-unique : ∀ {ym₁ ym₂ ym₃}
                     → ym₁ ⋖ ym₂
                     → ym₁ ⋖ ym₃
                     → ym₂ ≡ ym₃
next-unique stepᵐ stepᵐ = refl
next-unique (stepʸ p) (stepʸ q) with Y.next-unique p q
... | refl = refl

prev-unique : ∀ {ym₁ ym₂ ym₃}
                     → ym₁ ⋖ ym₃
                     → ym₂ ⋖ ym₃
                     → ym₁ ≡ ym₂
prev-unique stepᵐ stepᵐ = refl
prev-unique (stepʸ p) (stepʸ q) with Y.prev-unique p q
... | refl = refl

days-unique : ∀ {ym days₁ days₂}
               → ym HasDays days₁
               → ym HasDays days₂
               → days₁ ≡ days₂
days-unique (mkHasDays _ M.january-days) (mkHasDays _ M.january-days) = refl
days-unique (mkHasDays _ M.february-common-days) (mkHasDays _ M.february-common-days) = refl
days-unique (mkHasDays common₁ M.february-common-days) (mkHasDays () M.february-leap-days)
days-unique (mkHasDays common₁₀₀ M.february-common-days) (mkHasDays () M.february-leap-days)
days-unique (mkHasDays _ M.february-leap-days) (mkHasDays _ M.february-leap-days) = refl
days-unique (mkHasDays () M.february-leap-days) (mkHasDays common₁ M.february-common-days)
days-unique (mkHasDays () M.february-leap-days) (mkHasDays common₁₀₀ M.february-common-days)
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

has-days-irrelevant : ∀ {ym days} → (p q : ym HasDays days) → p ≡ q
has-days-irrelevant (mkHasDays hasYearType₁ hasDays₁) (mkHasDays hasYearType₂ hasDays₂) with year-type-unique hasYearType₁ hasYearType₂
... | refl with has-type-irrelevant hasYearType₁ hasYearType₂ | M.has-days-irrelevant hasDays₁ hasDays₂
... | refl | refl = refl

<-WellFounded : WellFounded _<_
<-WellFounded ym = On.accessible (proj₁ ∘ toOrdinal) (ℕ.<-wellFounded-fast (proj₁ (toOrdinal ym)))

next-ordinal : ∀ {ym₁ ym₂ n} → ym₁ ⋖ ym₂ → ym₁ HasOrdinal n → ym₂ HasOrdinal (suc n)
next-ordinal (stepʸ {y₁} {y₂} y₁⋖y₂) (ordinal weight) with next-weight y₁⋖y₂ weight
...                                                                         | h = ordinal h
next-ordinal (stepᵐ {y} {ac} {rm} {c}) (ordinal {n} weight) = ordinal weight

⋖⇒suc : ∀ {ym₁ ym₂} → ym₁ ⋖ ym₂ → ∃[ n ] (ym₁ HasOrdinal n) × (ym₂ HasOrdinal (suc n))
⋖⇒suc ym₁⋖ym₂ with next-ordinal ym₁⋖ym₂ (ordinal weight)
... | h = _ , ((ordinal weight) , h)

ordinal-unique : ∀ {ym n₁ n₂} → ym HasOrdinal n₁ → ym HasOrdinal n₂ → n₁ ≡ n₂
ordinal-unique (ordinal weight) (ordinal weight) = refl

suc-ordinal⇒IsSuc : ∀ {ym n} → ym HasOrdinal (suc n) → IsSuc ym
suc-ordinal⇒IsSuc {year - [ mkPos cursor ]} p with Y.isSuc? year
... | yes q = sucʸ q
suc-ordinal⇒IsSuc {year - [ mkPos cursor ]} p | no ¬q with Y.¬IsSuc⇒first ¬q
suc-ordinal⇒IsSuc {(0 Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - [ mkPos first ]} p | no ¬q | refl with toOrdinal ((0 Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - [ mkPos first ])
suc-ordinal⇒IsSuc {(0 Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - [ mkPos first ]} p | no ¬q | refl | n , snd with ordinal-unique p snd
suc-ordinal⇒IsSuc {(zero Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - [ mkPos first ]} p | no ¬q | refl | n , ordinal weight | ()
suc-ordinal⇒IsSuc {year - [ mkPos (suc cursor) ]} p | no _ | refl = sucᵐ

IsSuc⇒suc-ordinal : ∀ {ym} → IsSuc ym → ∃[ n ] ym HasOrdinal (suc n)
IsSuc⇒suc-ordinal sucᵐ = _ + 0 * 12 , ordinal weight
IsSuc⇒suc-ordinal {year - [ mkPos first ]} (sucʸ x) with IsSuc⇒suc-weight x
... | fst , snd = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (fst * 12))))))))))) , ordinal snd
IsSuc⇒suc-ordinal {year - [ mkPos (suc c) ]} (sucʸ x) = _ , ordinal weight

¬IsSuc⇒first : ∀ {ym} → ¬ IsSuc ym → ym ≡ (zero Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - january
¬IsSuc⇒first {y - m} p with Y.isSuc? y
¬IsSuc⇒first {y - m} p | yes isSuc = contradiction (sucʸ isSuc) p
¬IsSuc⇒first {y - m} p | no ¬isSuc with Y.¬IsSuc⇒first ¬isSuc
¬IsSuc⇒first {y - january} p | no ¬isSuc | refl = refl
¬IsSuc⇒first {y - [ mkPos (suc cursor) ]} p | no ¬isSuc | refl = contradiction sucᵐ p

¬isSuc-unique : ∀ {d₁ d₂} → ¬ IsSuc d₁ → ¬ IsSuc d₂ → d₁ ≡ d₂
¬isSuc-unique ¬isSuc₁ ¬isSuc₂ with ¬IsSuc⇒first ¬isSuc₁ | ¬IsSuc⇒first ¬isSuc₂
... | refl | refl = refl

∃prev⇒IsSuc : ∀ {ym₁ ym₂ : YearMonth} → ym₁ ⋖ ym₂ → IsSuc ym₂
∃prev⇒IsSuc {_} {year - month} d with Y.isSuc? year
... | yes p = sucʸ p
... | no p with Y.¬IsSuc⇒first p
∃prev⇒IsSuc {_} {year - month} stepᵐ | no p | refl = sucᵐ

prev-ordinal : ∀ {ym₁ ym₂ n} → ym₁ ⋖ ym₂ → ym₂ HasOrdinal (suc n) → ym₁ HasOrdinal n
prev-ordinal ym₁⋖ym₂ p with ⋖⇒suc ym₁⋖ym₂
... | _ , q , p' with ordinal-unique p p'
... | refl = q

⋖⇒< : ∀ {ym₁ ym₂} → ym₁ ⋖ ym₂ → ym₁ < ym₂
⋖⇒< {ym₁} {ym₂} p with ⋖⇒suc p | toOrdinal ym₁ | toOrdinal ym₂
... | n , ep₁ , ep₂ | n₁ , ordinal _ | n₂ , ordinal _ with ordinal-unique ep₁ (ordinal weight) | ordinal-unique ep₂ (ordinal weight)
... | eq₁ | eq₂ rewrite sym eq₁ | sym eq₂ = ≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded y = Subrelation.accessible ⋖⇒< (<-WellFounded y)

first-ordinal≡zero : ∀ {n} → ((0 Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - january) HasOrdinal n → n ≡ 0
first-ordinal≡zero p with ordinal-unique p (ordinal weight)
... | refl = refl

ordinal≡0⇒first : ∀ {ym} → ym HasOrdinal 0 → ym ≡ ((0 Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - january)
ordinal≡0⇒first {ym} p with isSuc? ym
ordinal≡0⇒first {ym} p | yes isSuc with IsSuc⇒suc-ordinal isSuc
... | fst , snd with ordinal-unique snd p
... | ()
ordinal≡0⇒first {ym} p | no q with ¬IsSuc⇒first q
ordinal≡0⇒first {ym} p | no q | refl = refl

year-month-unique : ∀ {ym₁ ym₂ n} → ym₁ HasOrdinal n → ym₂ HasOrdinal n → ym₁ ≡ ym₂
year-month-unique {ym₁} {ym₂} {zero} p q with ordinal≡0⇒first p | ordinal≡0⇒first q
... | refl | refl = refl
year-month-unique {ym₁} {ym₂} {suc n} p q with prev ym₁ (suc-ordinal⇒IsSuc p) | prev ym₂ (suc-ordinal⇒IsSuc q)
... | ym₁' , ym₁'⋖ym₁ | ym₂ , ym₂'⋖ym₂ with prev-ordinal ym₁'⋖ym₁ p | prev-ordinal ym₂'⋖ym₂ q
... | p' | q' with year-month-unique p' q'
... | refl with next-unique ym₁'⋖ym₁ ym₂'⋖ym₂
... | refl = refl
