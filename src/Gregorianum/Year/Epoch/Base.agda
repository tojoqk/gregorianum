module Gregorianum.Year.Epoch.Base where

open import Gregorianum.Year.Base
open import Gregorianum.Year.Properties

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
import Gregorianum.Data.Cursor.Position.Properties as Position
import Gregorianum.Data.Cursor.Properties as Cursor

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat.DivMod using (_divMod_; result)

data _HasEpoch_ (year : Year) : ℕ → Set where
  epoch : year HasEpoch (Position.toℕ (Year.pos₁ year) + (Position.toℕ (Year.pos₄ year) + (Position.toℕ (Year.pos₁₀₀ year) + Year.quadricentennial year * 4) * 25) * 4)

toEpoch : (y : Year) → ∃[ n ] y HasEpoch n
toEpoch (q ×₄₀₀+ y₁₀₀ ×₁₀₀+ y₄ ×₄+ y₁) = Position.toℕ y₁ + (Position.toℕ y₄ + (Position.toℕ y₁₀₀ + q * 4) * 25) * 4 , epoch

fromEpoch : (n : ℕ) → ∃[ y ] y HasEpoch n
fromEpoch n with n divMod 4
... | result q₄ r₄ p₄ with q₄ divMod 25
... | result q₁₀₀ r₁₀₀ p₁₀₀ with q₁₀₀ divMod 4
... | result q₄₀₀ r₄₀₀ p₄₀₀ = (q₄₀₀ ×₄₀₀+ fromFin r₄₀₀ ×₁₀₀+ fromFin r₁₀₀ ×₄+ fromFin r₄) , h
  where
    h : (q₄₀₀ ×₄₀₀+ fromFin r₄₀₀ ×₁₀₀+ fromFin r₁₀₀ ×₄+ fromFin r₄) HasEpoch n
    h rewrite p₄
              | p₁₀₀
              | p₄₀₀
              | sym (Position.toℕ∘fromFin≡toℕ r₄₀₀)
              | sym (Position.toℕ∘fromFin≡toℕ r₁₀₀)
              | sym (Position.toℕ∘fromFin≡toℕ r₄) = epoch
