module Gregorianum.Hour.Base where

open import Gregorianum.Data.Position using (Position)
open import Data.Nat using (ℕ)

record Hour : Set where
  constructor [_]
  field
    position : Position 23
