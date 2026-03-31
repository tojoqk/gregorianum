module Gregorianum.Year.Weight.Base where

open import Gregorianum.Year.Base using (Year; _′_″_‴_)

open import Gregorianum.Data.Position using (Position)
open import Data.Nat as ℕ using (ℕ; suc; zero; NonZero; _+_; _*_)
open import Data.Product using (∃-syntax; _,_)

data _HasWeight_ (year : Year) : (n : ℕ) → {{NonZero n}} → Set where
  weight : year HasWeight (1 + Position.toℕ (Year.pos₁ year) + Position.toℕ (Year.pos₄ year) * 4 + Position.toℕ (Year.pos₁₀₀ year) * 100 + Year.quadricentennial year * 400)

toWeight : (y : Year) → ∃[ n ] y HasWeight (suc n)
toWeight (q ′ y₁₀₀ ″ y₄ ‴ y₁) = _ , weight

data _HasLeapWeight_ (year : Year) : (n : ℕ) → {{NonZero n}} → Set where
  weight : year HasLeapWeight (suc (Position.toℕ (Year.pos₄ year)) + Position.toℕ (Year.pos₁₀₀ year) * 24 + Year.quadricentennial year * 97)
  
toLeapWeight : (y : Year) → ∃[ n ] y HasLeapWeight (suc n) 
toLeapWeight y = _ , weight

data _HasCommonWeight_ (year : Year) : (n : ℕ) → Set where
  weight : year HasCommonWeight (Position.toℕ (Year.pos₁ year) + Position.toℕ (Year.pos₄ year) * 3 + Position.toℕ (Year.pos₁₀₀ year) * 76 + Year.quadricentennial year * 303)

toCommonWeight : (y : Year) → ∃[ n ] y HasCommonWeight n 
toCommonWeight y = _ , weight
