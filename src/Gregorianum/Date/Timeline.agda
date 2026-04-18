module Gregorianum.Date.Timeline where

open import Gregorianum.Date.Base
  using (Date; _HasOrdinal_; toOrdinal; next; isSuc?; prev)
open import Gregorianum.Date.Properties
  using (date-unique; next-ordinal; prev-ordinal; suc-ordinal⇒IsSuc; ordinal-unique; has-ordinal-irrelevant)

open import Gregorianum.Relation.Timeline Date using (IsTimeline; module Path)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

private
  shift : ∀ {n} → (d₁ : Date) → (k : ℕ) → d₁ HasOrdinal n → ∃[ d₂ ] d₂ HasOrdinal (k + n)
  shift d₁ zero ho = d₁ , ho
  shift d₁ (suc k) ho with shift d₁ k ho
  ... | d₂' , ho₂' with next d₂'
  ... | d₂ , d₂'⋖d₂ = d₂ , next-ordinal d₂'⋖d₂ ho₂'

isTimeline : IsTimeline 
isTimeline = record
              { _HasOrdinal_ = _HasOrdinal_
              ; toOrdinal = toOrdinal
              ; unique = date-unique
              ; ordinal-unique = ordinal-unique
              ; shift = shift
              ; has-ordinal-irrelevant = has-ordinal-irrelevant
              }

open Path isTimeline public
