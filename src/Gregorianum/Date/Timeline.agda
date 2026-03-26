module Gregorianum.Date.Timeline where

open import Gregorianum.Date.Base
  using (Date; _HasOrdinal_; toOrdinal; nextDate; isSuccessor?; prevDate)
open import Gregorianum.Date.Properties
  using (date-unique; next-date-ordinal; prev-date-ordinal; suc-ordinal-is-successor; ordinal-unique)

open import Gregorianum.Relation.Timeline Date using (IsTimeline; module Path)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

private
  shift : ∀ {n} → (d₁ : Date) → (k : ℕ) → d₁ HasOrdinal n → ∃[ d₂ ] d₂ HasOrdinal (k + n)
  shift d₁ zero ho = d₁ , ho
  shift d₁ (suc k) ho with shift d₁ k ho
  ... | d₂' , ho₂' with nextDate d₂'
  ... | d₂ , d₂'⋖d₂ = d₂ , next-date-ordinal d₂'⋖d₂ ho₂'

isTimeline : IsTimeline 
isTimeline = record
              { _HasOrdinal_ = _HasOrdinal_
              ; toOrdinal = toOrdinal
              ; unique = date-unique
              ; ordinal-unique = ordinal-unique
              ; shift = shift
              }

open Path isTimeline public

open import Gregorianum.Relation.Path Date _─[_]→_ using (Tri; tri→; tri←; tri≡) public

addDays : ∀ d₁ n → ∃[ d₂ ] d₁ ─[ n ]→ d₂
addDays d₁ n = let (_ , ho₁) = toOrdinal d₁ in
               let (d₂ , ho₂) = shift d₁ n ho₁
               in d₂ , ⟨ ho₁ , ho₂ ⟩

subtractDays? : ∀ d₂ n → Dec (∃[ d₁ ] d₁ ─[ n ]→ d₂)
subtractDays? d₂ zero = let (_ , ho) = toOrdinal d₂ in yes (d₂ , ⟨ ho , ho ⟩)
subtractDays? d₂ (suc n) with isSuccessor? d₂
... | yes isSuc with prevDate d₂ isSuc
... | d₂' , d₂'⋖d₂ with subtractDays? d₂' n
... | yes (d₁ , ⟨ ho₁ , ho₂' ⟩) = yes (d₁ , ⟨ ho₁ , next-date-ordinal d₂'⋖d₂ ho₂' ⟩)
... | no ¬p = no h
  where
    h : ¬ (∃[ d₁ ] d₁ ─[ suc n ]→ d₂)
    h (d₁ , ⟨ ho₁ , ho₂ ⟩) = ¬p (d₁ , ⟨ ho₁ , prev-date-ordinal d₂'⋖d₂ ho₂ ⟩)
subtractDays? d₂ (suc n) | no ¬isSuc = no h
  where
    h : ¬ (∃[ d₁ ] d₁ ─[ suc n ]→ d₂)
    h (d₁ , ⟨ ho₁ , ho₂ ⟩) = ¬isSuc (suc-ordinal-is-successor ho₂)
