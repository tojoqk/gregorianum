module Gregorianum.Relation.Edge (A : Set) (_⋖_ : A → A → Set) where

open import Relation.Binary.PropositionalEquality using (_≡_)

record IsEdge : Set where
  field
    uniqueˡ : ∀ {x y z} → x ⋖ z → y ⋖ z → x ≡ y
    uniqueʳ : ∀ {x y z} → x ⋖ y → x ⋖ z → y ≡ z
