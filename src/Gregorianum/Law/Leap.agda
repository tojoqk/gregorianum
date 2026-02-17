module Gregorianum.Law.Leap where

open import Data.Nat using (ℕ)
open import Data.Nat.Divisibility using (_∣_; _∤_)

data Centennial (y : ℕ) : Set where
  non-centennial : 100 ∤ y → Centennial y
  quadricentennial : 400 ∣ y → Centennial y

record Leap (y : ℕ): Set where
  field
    quadrennial : 4 ∣ y
    centennial : Centennial y
