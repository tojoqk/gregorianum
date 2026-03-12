module Gregorianum.Data.Cursor.Position.Properties where

open import Gregorianum.Data.Cursor.Position.Base

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Properties as Fin

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

toℕ∘fromFin≡toℕ : ∀ {width} → (n : Fin (suc width)) → Position.toℕ (fromFin n) ≡ Fin.toℕ n
toℕ∘fromFin≡toℕ Fin.zero = refl
toℕ∘fromFin≡toℕ (Fin.suc n) = refl
