module Gregorianum.Year.Timeline where

open import Gregorianum.Year.Base
  using (Year; _HasOrdinal_; toOrdinal; nextYear; isSuc?; prevYear)
open import Gregorianum.Year.Properties
  using (year-unique; next-year-ordinal; prev-year-ordinal; suc-ordinal-is-successor; ordinal-unique)

open import Gregorianum.Relation.Timeline Year using (IsTimeline; module Path)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

private
  shift : ∀ {n} → (ym₁ : Year) → (k : ℕ) → ym₁ HasOrdinal n → ∃[ ym₂ ] ym₂ HasOrdinal (k + n)
  shift ym₁ zero ho = ym₁ , ho
  shift ym₁ (suc k) ho with shift ym₁ k ho
  ... | ym₂' , ho₂' with nextYear ym₂'
  ... | ym₂ , ym₂'⋖ym₂ = ym₂ , next-year-ordinal ym₂'⋖ym₂ ho₂'

isTimeline : IsTimeline 
isTimeline = record
              { _HasOrdinal_ = _HasOrdinal_
              ; toOrdinal = toOrdinal
              ; unique = year-unique
              ; ordinal-unique = ordinal-unique
              ; shift = shift
              }

open Path isTimeline public

open import Gregorianum.Relation.Path Year _─[_]→_ using (Tri; tri→; tri←; tri≡) public

addYears : ∀ ym₁ n → ∃[ ym₂ ] ym₁ ─[ n ]→ ym₂
addYears ym₁ n = let (_ , ho₁) = toOrdinal ym₁ in
                  let (ym₂ , ho₂) = shift ym₁ n ho₁
                  in ym₂ , ⟨ ho₁ , ho₂ ⟩

subtractYears? : ∀ d₂ n → Dec (∃[ d₁ ] d₁ ─[ n ]→ d₂)
subtractYears? d₂ zero = let (_ , ho) = toOrdinal d₂ in yes (d₂ , ⟨ ho , ho ⟩)
subtractYears? d₂ (suc n) with isSuc? d₂
... | yes isSuc with prevYear d₂ isSuc
... | d₂' , d₂'⋖d₂ with subtractYears? d₂' n
... | yes (d₁ , ⟨ ho₁ , ho₂' ⟩) = yes (d₁ , ⟨ ho₁ , next-year-ordinal d₂'⋖d₂ ho₂' ⟩)
... | no ¬p = no h
  where
    h : ¬ (∃[ d₁ ] d₁ ─[ suc n ]→ d₂)
    h (d₁ , ⟨ ho₁ , ho₂ ⟩) = ¬p (d₁ , ⟨ ho₁ , prev-year-ordinal d₂'⋖d₂ ho₂ ⟩)
subtractYears? d₂ (suc n) | no ¬isSuc = no h
  where
    h : ¬ (∃[ d₁ ] d₁ ─[ suc n ]→ d₂)
    h (d₁ , ⟨ ho₁ , ho₂ ⟩) = ¬isSuc (suc-ordinal-is-successor ho₂)
