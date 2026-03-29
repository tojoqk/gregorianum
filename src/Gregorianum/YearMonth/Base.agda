module Gregorianum.YearMonth.Base where

open import Gregorianum.Year as Y using (Year; YearType; _×₄₀₀+_×₁₀₀+_×₄+_; _HasYearType_)
import Gregorianum.Year.Properties as Y
open import Gregorianum.Year.Weight.Base using (_HasWeight_; weight)
open import Gregorianum.Month.Base as M using (Month; [_]; january; december)
open import Gregorianum.Data.Cursor using (Cursor; zero; suc; first; suc¹²)
open import Gregorianum.Data.Cursor.Position using (mkPos; Position)
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

data _⋖_ : YearMonth → YearMonth → Set where
  stepᵐ : ∀ {y acc rem} → {c : Cursor 11 acc (suc rem)} → (y - [ mkPos c ]) ⋖ (y - [ mkPos (suc c) ])
  stepʸ : ∀ {y₁ y₂} → y₁ Y.⋖ y₂ → (y₁ - december) ⋖ (y₂ - january)

data IsSuc : YearMonth → Set where
  sucᵐ : ∀ {acc rem} → {c : Cursor 11 (suc acc) rem} → IsSuc ((zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - [ mkPos c ])
  sucʸ : ∀ {ym} → Y.IsSuc (YearMonth.year ym) → IsSuc ym


isSuc? : (ym : YearMonth) → Dec (IsSuc ym)
isSuc? (year - month) with Y.isSuc? year
... | yes p = yes (sucʸ p)
isSuc? (year - month) | no p with Y.¬IsSuc⇒first p
isSuc? ((zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - [ mkPos first ]) | no ¬p | refl = no λ { (sucʸ p) → ¬p p}
isSuc? ((zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - [ mkPos (suc _) ]) | no _ | refl = yes sucᵐ

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

next : ∀ ym₁ → ∃[ ym₂ ] ym₁ ⋖ ym₂
next (year - [ mkPos {rem = suc rem} cursor ]) = (year - [ mkPos (suc cursor) ]) , stepᵐ
next (year - december) with Y.next year
...                                                  | year' , p = (year' - january) , stepʸ p
next (year - [ mkPos {rem = zero} c₁₂@(suc¹² _) ]) with rem≡0⇒width≡acc c₁₂
...                                                         | ()

prev : ∀ ym₂ → IsSuc ym₂ → ∃[ ym₁ ] ym₁ ⋖ ym₂
prev (_ - [ mkPos (suc c) ]) sucᵐ = ((zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) - [ mkPos c ]) , stepᵐ
prev (year - [ mkPos first ]) (sucʸ x) = (proj₁ (Y.prev year x) - december) , stepʸ (proj₂ (Y.prev year x))
prev (year - [ mkPos (suc month) ]) (sucʸ x) = (year - [ mkPos month ]) , stepᵐ

data _HasOrdinal_ (ym : YearMonth) : (n : ℕ) → Set where
  ordinal : ∀ {yw}
             → (YearMonth.year ym) HasWeight (suc yw)
             → ym HasOrdinal (Position.toℕ (Month.position (YearMonth.month ym)) + yw * 12)

toOrdinal : (ym : YearMonth) → ∃[ n ] ym HasOrdinal n
toOrdinal ym = _ , ordinal weight

_<_ : YearMonth → YearMonth → Set
ym₁ < ym₂ = proj₁ (toOrdinal ym₁) ℕ.< proj₁ (toOrdinal ym₂)
