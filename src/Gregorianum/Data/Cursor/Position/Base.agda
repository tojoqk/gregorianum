module Gregorianum.Data.Cursor.Position.Base where

open import Gregorianum.Data.Cursor.Base as Cursor hiding (toℕ)
import Gregorianum.Data.Cursor.Properties as Cursor

open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s)
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Properties as Fin

record Position (width : ℕ): Set where
  constructor mkPos
  field
    {acc rem} : ℕ
    cursor : Cursor width acc rem

  toℕ = acc

fromFin : ∀ {width} → Fin (suc width) → Position width
fromFin Fin.zero = mkPos zero
fromFin (Fin.suc n) = mkPos (fromℕ≤ (toℕ<n n))

toFin : ∀ {width} → Position width → Fin (suc width)
toFin (mkPos {acc = zero} {rem = rem} h) = Fin.zero
toFin (mkPos {acc = suc acc} {rem = rem} h) = Fin.fromℕ< (s≤s (Cursor.acc≤width h))

_<_ : ∀ {width} → Position width → Position width → Set
p₁ < p₂ = Position.toℕ p₁ ℕ.< Position.toℕ p₂
