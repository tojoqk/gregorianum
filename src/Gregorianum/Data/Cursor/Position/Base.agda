module Gregorianum.Data.Cursor.Position.Base where

open import Gregorianum.Data.Cursor.Base
open import Data.Nat using (ℕ)

record Position (width : ℕ): Set where
  constructor pos
  field
    {acc rem} : ℕ
    cursor : Cursor width acc rem
