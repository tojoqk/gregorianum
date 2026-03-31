module Gregorianum.Data.Position.Properties where

open import Gregorianum.Data.Position.Base

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

toℕ∘fromFin≡toℕ : ∀ {width} → (n : Fin (suc width)) → Position.toℕ (fromFin n) ≡ toℕ n
toℕ∘fromFin≡toℕ zero = refl
toℕ∘fromFin≡toℕ (suc n) = refl
