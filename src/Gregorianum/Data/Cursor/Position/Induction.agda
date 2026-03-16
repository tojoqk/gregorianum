module Gregorianum.Data.Cursor.Position.Induction where

open import Gregorianum.Data.Cursor.Position.Base

import Data.Nat.Induction as ℕ
open import Induction.WellFounded
import Relation.Binary.Construct.On as On
open import Level using (Level)

<-wellFounded : ∀ {width} → WellFounded (_<_ {width})
<-wellFounded p = On.accessible Position.toℕ (ℕ.<-wellFounded-fast (Position.toℕ p))

module _  {width} {ℓ : Level} where
  open All (<-wellFounded {width}) ℓ public
    renaming ( wfRecBuilder to <-recBuilder
             ; wfRec        to <-rec
             )
    hiding (wfRec-builder)
