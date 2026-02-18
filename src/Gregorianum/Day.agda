module Gregorianum.Day where

open import Data.Nat using (ℕ; suc; zero)

data Day (n : ℕ) : (i j : ℕ) → Set where
  1st : Day n zero n
  suc : ∀ {i j} → Day n i (suc j) → Day n (suc i) j
