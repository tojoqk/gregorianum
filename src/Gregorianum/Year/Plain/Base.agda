module Gregorianum.Year.Plain.Base where

open import Gregorianum.Year.Base using (Year; _×₄₀₀+_×₁₀₀+_×₄+_)

open import Gregorianum.Data.Cursor.Position using (Position; fromFin)
open import Gregorianum.Data.Cursor.Position.Properties using (toℕ∘fromFin≡toℕ)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.Nat.DivMod using (_divMod_; result)

data _HasPlain_ (year : Year) : ℕ → Set where
  plain : year HasPlain (Position.toℕ (Year.pos₁ year) + (Position.toℕ (Year.pos₄ year) + (Position.toℕ (Year.pos₁₀₀ year) + Year.quadricentennial year * 4) * 25) * 4)

toPlain : (y : Year) → ∃[ n ] y HasPlain n
toPlain (q ×₄₀₀+ y₁₀₀ ×₁₀₀+ y₄ ×₄+ y₁) = Position.toℕ y₁ + (Position.toℕ y₄ + (Position.toℕ y₁₀₀ + q * 4) * 25) * 4 , plain

fromPlain : (n : ℕ) → ∃[ y ] y HasPlain n
fromPlain n with n divMod 4
... | result q₄ r₄ p₄ with q₄ divMod 25
... | result q₁₀₀ r₁₀₀ p₁₀₀ with q₁₀₀ divMod 4
... | result q₄₀₀ r₄₀₀ p₄₀₀ = (q₄₀₀ ×₄₀₀+ fromFin r₄₀₀ ×₁₀₀+ fromFin r₁₀₀ ×₄+ fromFin r₄) , h
  where
    h : (q₄₀₀ ×₄₀₀+ fromFin r₄₀₀ ×₁₀₀+ fromFin r₁₀₀ ×₄+ fromFin r₄) HasPlain n
    h rewrite p₄
              | p₁₀₀
              | p₄₀₀
              | sym (toℕ∘fromFin≡toℕ r₄₀₀)
              | sym (toℕ∘fromFin≡toℕ r₁₀₀)
              | sym (toℕ∘fromFin≡toℕ r₄) = plain
