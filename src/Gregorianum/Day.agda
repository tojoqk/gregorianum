module Gregorianum.Day where

open import Data.Nat using (ℕ; suc; zero)

data Day (cap : ℕ) : (acc rem : ℕ) → Set where
  1st : Day cap zero cap
  suc : ∀ {acc rem} → Day cap acc (suc rem) → Day cap (suc acc) rem
