open import Data.Nat using (ℕ)
import Gregorianum.Relation.Path as Path

module Gregorianum.Relation.DualLinear (A : Set)
                                       (_≤[_]→_ : A → ℕ → A → Set)
                                       (_≥[_]→_ : A → ℕ → A → Set)
                                       where

open import Data.Nat using (zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Tri (x y : A) : Set where
  tri≡ : x ≡ y → Tri x y
  tri≤→ : ∀ {n} → x ≤[ suc n ]→ y → Tri x y
  tri≥→ : ∀ {n} → x ≥[ suc n ]→ y → Tri x y

record IsDualLinear : Set where
  field
    ≤-isLinear : Path.IsLinear A _≤[_]→_
    ≥-isLinear : Path.IsLinear A _≥[_]→_
    ≤→⇒≥← : ∀ {x y n} → x ≤[ n ]→ y → y ≥[ n ]→ x
    ≥→⇒≤← : ∀ {x y n} → x ≥[ n ]→ y → y ≤[ n ]→ x
    compare : ∀ x y → Tri x y
