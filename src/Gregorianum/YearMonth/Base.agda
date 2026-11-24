module Gregorianum.YearMonth.Base where

open import Gregorianum.Year as Y using (Year; year-first; YearType; _′_″_‴_; _HasYearType_)
import Gregorianum.Year.Properties as Y
open import Gregorianum.Month.Base as M using (Month; [_]; january; december)
open import Gregorianum.Data.Cursor using (Cursor; first; suc)
open import Gregorianum.Data.Position using (mkPos; Position)
open import Gregorianum.Data.Cursor.Properties using (rem≡0⇒width≡acc)

open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; NonZero)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no)

record YearMonth : Set where
  constructor _-_
  field
    year : Year
    month : Month

pattern year-month-first = year-first - [ mkPos first ]

data _⋖_ : YearMonth → YearMonth → Set where
  step-month : ∀ {y acc rem} → {c : Cursor 11 acc (suc rem)} → (y - [ mkPos c ]) ⋖ (y - [ mkPos (suc c) ])
  step-year : ∀ {y₁ y₂} → y₁ Y.⋖ y₂ → (y₁ - december) ⋖ (y₂ - january)

record _HasDays_ (ym : YearMonth) (days : ℕ) : Set where
  constructor mkHasDays
  field
    {yearType} : YearType
    hasYearType : YearMonth.year ym HasYearType yearType
    hasDays : (yearType , YearMonth.month ym) M.HasDays days

days : ∀ ym → ∃[ ds ] ym HasDays ds
days (ym - m) with Y.yearType ym
...              | yt , pʸᵗ with M.days (yt , m)
...                            | ds , pᵈ = ds , mkHasDays pʸᵗ pᵈ

private
  pattern suc⁴ x = suc (suc (suc (suc x)))
  pattern suc¹² x = suc⁴ (suc⁴ (suc⁴ x))

next : ∀ ym₁ → ∃[ ym₂ ] ym₁ ⋖ ym₂
next (year - [ mkPos {rem = suc rem} cursor ]) = (year - [ mkPos (suc cursor) ]) , step-month
next (year - december) with Y.next year
...                                                  | year' , p = (year' - january) , step-year p
next (year - [ mkPos {rem = zero} c₁₂@(suc¹² _) ]) with rem≡0⇒width≡acc c₁₂
...                                                         | ()

prev? : (ym : YearMonth) → Dec (∃[ ym′ ] ym′ ⋖ ym)
prev? (y - january) with Y.prev? y
... | yes (y′ , y′⋖y) = yes ((y′ - december) , step-year y′⋖y)
... | no ¬p  = no λ { (y′ , step-year y′⋖y) → ¬p (YearMonth.year y′ , y′⋖y) }
prev? (y - [ mkPos (suc c) ]) = yes ((y - [ mkPos c ]) , step-month)

data _HasOrdinal_ (ym : YearMonth) : (n : ℕ) → Set where
  ordinal : ∀ {yo}
             → (YearMonth.year ym) Y.HasOrdinal yo
             → ym HasOrdinal (Position.toℕ (Month.position (YearMonth.month ym)) + yo * 12)

toOrdinal : (ym : YearMonth) → ∃[ n ] ym HasOrdinal n
toOrdinal ym = _ , ordinal Y.ordinal

_<_ : YearMonth → YearMonth → Set
ym₁ < ym₂ = proj₁ (toOrdinal ym₁) ℕ.< proj₁ (toOrdinal ym₂)
