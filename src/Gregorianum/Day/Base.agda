module Gregorianum.Day.Base where

open import Gregorianum.Data.Position using (Position)
open import Data.Nat using (ℕ)

record Day (width : ℕ) : Set where
  constructor [_]
  field
    position : Position width


