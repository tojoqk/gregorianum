module Gregorianum.YearMonth.Timeline where

open import Gregorianum.YearMonth.Base
  using (YearMonth; _HasOrdinal_; toOrdinal; nextYearMonth; isSuc?; prevYearMonth)
open import Gregorianum.YearMonth.Properties
  using (year-month-unique; next-year-month-ordinal; prev-year-month-ordinal; suc-ordinal-is-successor; ordinal-unique)

open import Gregorianum.Relation.Timeline YearMonth using (IsTimeline; module Path)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

private
  shift : ∀ {n} → (ym₁ : YearMonth) → (k : ℕ) → ym₁ HasOrdinal n → ∃[ ym₂ ] ym₂ HasOrdinal (k + n)
  shift ym₁ zero ho = ym₁ , ho
  shift ym₁ (suc k) ho with shift ym₁ k ho
  ... | ym₂' , ho₂' with nextYearMonth ym₂'
  ... | ym₂ , ym₂'⋖ym₂ = ym₂ , next-year-month-ordinal ym₂'⋖ym₂ ho₂'

isTimeline : IsTimeline 
isTimeline = record
              { _HasOrdinal_ = _HasOrdinal_
              ; toOrdinal = toOrdinal
              ; unique = year-month-unique
              ; ordinal-unique = ordinal-unique
              ; shift = shift
              }

open Path isTimeline public

open import Gregorianum.Relation.Path YearMonth _─[_]→_ using (Tri; tri→; tri←; tri≡) public

forward : ∀ ym₁ n → ∃[ ym₂ ] ym₁ ─[ n ]→ ym₂
forward ym₁ n = let (_ , ho₁) = toOrdinal ym₁ in
                let (ym₂ , ho₂) = shift ym₁ n ho₁
                in ym₂ , ⟨ ho₁ , ho₂ ⟩

backward? : ∀ d₂ n → Dec (∃[ d₁ ] d₁ ─[ n ]→ d₂)
backward? d₂ zero = let (_ , ho) = toOrdinal d₂ in yes (d₂ , ⟨ ho , ho ⟩)
backward? d₂ (suc n) with isSuc? d₂
... | yes isSuc with prevYearMonth d₂ isSuc
... | d₂' , d₂'⋖d₂ with backward? d₂' n
... | yes (d₁ , ⟨ ho₁ , ho₂' ⟩) = yes (d₁ , ⟨ ho₁ , next-year-month-ordinal d₂'⋖d₂ ho₂' ⟩)
... | no ¬p = no h
  where
    h : ¬ (∃[ d₁ ] d₁ ─[ suc n ]→ d₂)
    h (d₁ , ⟨ ho₁ , ho₂ ⟩) = ¬p (d₁ , ⟨ ho₁ , prev-year-month-ordinal d₂'⋖d₂ ho₂ ⟩)
backward? d₂ (suc n) | no ¬isSuc = no h
  where
    h : ¬ (∃[ d₁ ] d₁ ─[ suc n ]→ d₂)
    h (d₁ , ⟨ ho₁ , ho₂ ⟩) = ¬isSuc (suc-ordinal-is-successor ho₂)
