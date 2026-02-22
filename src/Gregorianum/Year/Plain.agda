module Gregorianum.Year.Plain where

open import Gregorianum.Year.Base
open import Gregorianum.Year.Properties using (isLeap?)

open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.Product using (Σ-syntax; ∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data _HasPlain_ {yt} (year : Year yt) : ℤ → Set where
  plain : ∀ {y}
        → (Year.year year) ≡ y
        → year HasPlain y

toPlain : ∀ {yt} → Year yt → ℤ
toPlain (year ⟨ _ ⟩) = year

fromPlain : (y : ℤ) → ∃[ yt ] Σ[ year ∈ Year yt ] year HasPlain y
fromPlain y with isLeap? y
...            | yes p = leap , (y ⟨ leap p ⟩) , plain refl
...            | no ¬p = common , (y ⟨ (common ¬p) ⟩) , plain refl
