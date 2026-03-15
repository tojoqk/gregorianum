module Gregorianum.Data.Cursor.Position.Induction where

open import Gregorianum.Data.Cursor.Position.Base

import Data.Nat.Induction as ℕ
open import Induction.WellFounded
import Relation.Binary.Construct.On as On

<-wellFounded : ∀ {w} → WellFounded (_<_ {w})
<-wellFounded p = On.accessible Position.toℕ (ℕ.<-wellFounded-fast (Position.toℕ p))
