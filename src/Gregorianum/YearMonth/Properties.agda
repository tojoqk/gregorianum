module Gregorianum.YearMonth.Properties where

open import Gregorianum.YearMonth.Base

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position hiding (_<_)
import Gregorianum.Year as Y
import Gregorianum.Year.Properties as Y
import Gregorianum.Year.Weight.Base as Y
import Gregorianum.Year.Weight.Properties as Y
import Gregorianum.Month as M
import Gregorianum.Month.Properties as M
open import Gregorianum.Year.Properties using (next-year-unique; prev-year-unique)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; NonZero)
open import Data.Nat.Properties using (suc-injective; ≤-refl)
import Data.Nat.Induction as ℕ
open import Induction.WellFounded
import Relation.Binary.Construct.On as On
open import Function using (_∘_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

next-year-month-unique : ∀ {ym₁ ym₂ ym₃}
                     → ym₁ ⋖ ym₂
                     → ym₁ ⋖ ym₃
                     → ym₂ ≡ ym₃
next-year-month-unique stepᵐ stepᵐ = refl
next-year-month-unique (stepʸ p) (stepʸ q) with next-year-unique p q
...                                           | refl = refl

prev-year-month-unique : ∀ {ym₁ ym₂ ym₃}
                     → ym₁ ⋖ ym₃
                     → ym₂ ⋖ ym₃
                     → ym₁ ≡ ym₂
prev-year-month-unique stepᵐ stepᵐ = refl
prev-year-month-unique (stepʸ p) (stepʸ q) with prev-year-unique p q
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

has-days-irrelevant : ∀ {ym days} → (p q : ym HasDays days) → p ≡ q
has-days-irrelevant (mkHasDays hasYearType₁ hasDays₁) (mkHasDays hasYearType₂ hasDays₂) with Y.year-type-unique hasYearType₁ hasYearType₂
... | refl with Y.has-year-type-irrelevant hasYearType₁ hasYearType₂ | M.has-days-irrelevant hasDays₁ hasDays₂
... | refl | refl = refl

<-WellFounded : WellFounded _<_
<-WellFounded ym = On.accessible (proj₁ ∘ toOrdinal) (ℕ.<-wellFounded-fast (proj₁ (toOrdinal ym)))

next-year-month-ordinal : ∀ {ym₁ ym₂ n} → ym₁ ⋖ ym₂ → ym₁ HasOrdinal n → ym₂ HasOrdinal (suc n)
next-year-month-ordinal (stepʸ {y₁} {y₂} y₁⋖y₂) (has-ordinal Y.has-weight) with Y.next-year-weight y₁⋖y₂ Y.has-weight
...                                                                         | h = has-ordinal h
next-year-month-ordinal (stepᵐ {y} {ac} {rm} {c}) (has-ordinal {n} Y.has-weight) = has-ordinal Y.has-weight

⋖⇒suc : ∀ {ym₁ ym₂} → ym₁ ⋖ ym₂ → ∃[ n ] (ym₁ HasOrdinal n) × (ym₂ HasOrdinal (suc n))
⋖⇒suc ym₁⋖ym₂ with next-year-month-ordinal ym₁⋖ym₂ (has-ordinal Y.has-weight)
... | h = _ , ((has-ordinal Y.has-weight) , h)

ordinal-unique : ∀ {ym n₁ n₂} → ym HasOrdinal n₁ → ym HasOrdinal n₂ → n₁ ≡ n₂
ordinal-unique (has-ordinal Y.has-weight) (has-ordinal Y.has-weight) = refl

suc-ordinal-is-successor : ∀ {ym n} → ym HasOrdinal (suc n) → IsSuc ym
suc-ordinal-is-successor {year - mkPos cursor} p with Y.isSuc? year
... | yes q = sucʸ q
suc-ordinal-is-successor {year - mkPos cursor} p | no ¬q with Y.¬IsSuc⇒first ¬q
suc-ordinal-is-successor {(0 Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - mkPos first} p | no ¬q | refl with toOrdinal ((0 Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - mkPos first)
suc-ordinal-is-successor {(0 Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - mkPos first} p | no ¬q | refl | n , snd with ordinal-unique p snd
suc-ordinal-is-successor {(zero Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - mkPos first} p | no ¬q | refl | n , has-ordinal Y.has-weight | ()
suc-ordinal-is-successor {year - mkPos (suc cursor)} p | no _ | refl = sucᵐ

is-successor⇒suc-ordinal : ∀ {ym} → IsSuc ym → ∃[ n ] ym HasOrdinal (suc n)
is-successor⇒suc-ordinal sucᵐ = _ + 0 * 12 , has-ordinal Y.has-weight
is-successor⇒suc-ordinal {year - mkPos first} (sucʸ x) with Y.is-successor⇒suc-weight x
... | fst , snd = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (fst * 12))))))))))) , has-ordinal snd
is-successor⇒suc-ordinal {year - mkPos (suc c)} (sucʸ x) = _ , has-ordinal Y.has-weight

¬IsSuc⇒first : ∀ {ym} → ¬ IsSuc ym → ym ≡ (zero Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - mkPos first
¬IsSuc⇒first {y - m} p with Y.isSuc? y
¬IsSuc⇒first {y - m} p | yes isSuc = contradiction (sucʸ isSuc) p
¬IsSuc⇒first {y - m} p | no ¬isSuc with Y.¬IsSuc⇒first ¬isSuc
¬IsSuc⇒first {y - mkPos first} p | no ¬isSuc | refl = refl
¬IsSuc⇒first {y - mkPos (suc cursor)} p | no ¬isSuc | refl = contradiction sucᵐ p

∃prev⇒IsSuc : ∀ {ym₁ ym₂ : YearMonth} → ym₁ ⋖ ym₂ → IsSuc ym₂
∃prev⇒IsSuc {_} {year - month} d with Y.isSuc? year
... | yes p = sucʸ p
... | no p with Y.¬IsSuc⇒first p
∃prev⇒IsSuc {_} {year - month} stepᵐ | no p | refl = sucᵐ

prev-year-month-ordinal : ∀ {ym₁ ym₂ n} → ym₁ ⋖ ym₂ → ym₂ HasOrdinal (suc n) → ym₁ HasOrdinal n
prev-year-month-ordinal ym₁⋖ym₂ p with ⋖⇒suc ym₁⋖ym₂
... | _ , q , p' with ordinal-unique p p'
... | refl = q

⋖⇒< : ∀ {ym₁ ym₂} → ym₁ ⋖ ym₂ → ym₁ < ym₂
⋖⇒< {ym₁} {ym₂} p with ⋖⇒suc p | toOrdinal ym₁ | toOrdinal ym₂
... | n , ep₁ , ep₂ | n₁ , has-ordinal _ | n₂ , has-ordinal _ with ordinal-unique ep₁ (has-ordinal Y.has-weight) | ordinal-unique ep₂ (has-ordinal Y.has-weight)
... | eq₁ | eq₂ rewrite sym eq₁ | sym eq₂ = ≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded y = Subrelation.accessible ⋖⇒< (<-WellFounded y)

first-ordinal≡zero : ∀ {n} → ((0 Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - mkPos first) HasOrdinal n → n ≡ 0
first-ordinal≡zero p with ordinal-unique p (has-ordinal Y.has-weight)
... | refl = refl

ordinal≡0⇒first : ∀ {ym} → ym HasOrdinal 0 → ym ≡ ((0 Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - mkPos first)
ordinal≡0⇒first {ym} p with isSuc? ym
ordinal≡0⇒first {ym} p | yes isSuc with is-successor⇒suc-ordinal isSuc
... | fst , snd with ordinal-unique snd p
... | ()
ordinal≡0⇒first {ym} p | no q with ¬IsSuc⇒first q
ordinal≡0⇒first {ym} p | no q | refl = refl

year-month-unique : ∀ {ym₁ ym₂ n} → ym₁ HasOrdinal n → ym₂ HasOrdinal n → ym₁ ≡ ym₂
year-month-unique {ym₁} {ym₂} {zero} p q with ordinal≡0⇒first p | ordinal≡0⇒first q
... | refl | refl = refl
year-month-unique {ym₁} {ym₂} {suc n} p q with prevYearMonth ym₁ (suc-ordinal-is-successor p) | prevYearMonth ym₂ (suc-ordinal-is-successor q)
... | ym₁' , ym₁'⋖ym₁ | ym₂ , ym₂'⋖ym₂ with prev-year-month-ordinal ym₁'⋖ym₁ p | prev-year-month-ordinal ym₂'⋖ym₂ q
... | p' | q' with year-month-unique p' q'
... | refl with next-year-month-unique ym₁'⋖ym₁ ym₂'⋖ym₂
... | refl = refl
