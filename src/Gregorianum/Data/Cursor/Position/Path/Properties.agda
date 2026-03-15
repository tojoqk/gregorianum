open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s)

module Gregorianum.Data.Cursor.Position.Path.Properties {width : ℕ} where

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position.Base
open import Gregorianum.Data.Cursor.Position.Path {width}
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

from-first-len : ∀ {len p} → mkPos first ─[ len ]→ p → len ≡ p .Position.acc
from-first-len ε = refl
from-first-len (extendʳ p) = cong suc (from-first-len p)
