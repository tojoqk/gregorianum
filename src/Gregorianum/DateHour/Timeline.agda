module Gregorianum.DateHour.Timeline where

open import Gregorianum.DateHour.Base
  using (DateHour; _HasOrdinal_; toOrdinal; next; isSuc?; prev)
open import Gregorianum.DateHour.Properties
  using (date-hour-unique; next-ordinal; prev-ordinal; suc-ordinal⇒IsSuc; ordinal-unique; has-ordinal-irrelevant)

open import Gregorianum.Relation.Timeline DateHour using (IsTimeline; module Path)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

private
  shift : ∀ {n} → (dh₁ : DateHour) → (k : ℕ) → dh₁ HasOrdinal n → ∃[ dh₂ ] dh₂ HasOrdinal (k + n)
  shift dh₁ zero ho = dh₁ , ho
  shift dh₁ (suc k) ho with shift dh₁ k ho
  ... | dh₂' , ho₂' with next dh₂'
  ... | dh₂ , dh₂'⋖dh₂ = dh₂ , next-ordinal dh₂'⋖dh₂ ho₂'

isTimeline : IsTimeline
isTimeline = record
              { _HasOrdinal_ = _HasOrdinal_
              ; toOrdinal = toOrdinal
              ; unique = date-hour-unique
              ; ordinal-unique = ordinal-unique
              ; shift = shift
              ; has-ordinal-irrelevant = has-ordinal-irrelevant
              }

open Path isTimeline public
