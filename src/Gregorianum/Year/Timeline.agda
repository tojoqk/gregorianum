module Gregorianum.Year.Timeline where

open import Gregorianum.Year.Base using (Year; _HasOrdinal_; toOrdinal; next; isSuc?; prev)
open import Gregorianum.Year.Properties using (year-unique; next-ordinal; prev-ordinal; suc-ordinal⇒IsSuc; ordinal-unique; has-ordinal-irrelevant)
open import Gregorianum.Relation.Timeline Year using (IsTimeline; module Path)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

private
  shift : ∀ {n} → (ym₁ : Year) → (k : ℕ) → ym₁ HasOrdinal n → ∃[ ym₂ ] ym₂ HasOrdinal (k + n)
  shift ym₁ zero ho = ym₁ , ho
  shift ym₁ (suc k) ho with shift ym₁ k ho
  ... | ym₂' , ho₂' with next ym₂'
  ... | ym₂ , ym₂'⋖ym₂ = ym₂ , next-ordinal ym₂'⋖ym₂ ho₂'

isTimeline : IsTimeline 
isTimeline = record
              { _HasOrdinal_ = _HasOrdinal_
              ; toOrdinal = toOrdinal
              ; unique = year-unique
              ; ordinal-unique = ordinal-unique
              ; shift = shift
              ; has-ordinal-irrelevant = has-ordinal-irrelevant
              }

open Path isTimeline public
