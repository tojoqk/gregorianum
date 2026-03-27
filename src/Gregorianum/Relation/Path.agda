open import Data.Nat using (ℕ)

module Gregorianum.Relation.Path (A : Set)
                                 (_─[_]→_ : A → ℕ → A → Set)
                                 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (zero; suc; _+_)
open import Data.Product using (∃-syntax; _×_; _,_)

record IsPath : Set where
  field
    identity : ∀ {x y} → x ≡ y → x ─[ zero ]→ y
    identity⁻¹ : ∀ {x y} → x ─[ zero ]→ y → x ≡ y
    trans : ∀ {x y z m n}
          → x ─[ m ]→ y
          → y ─[ n ]→ z
          → x ─[ m + n ]→ z
    split : ∀ {x z}
          → (m n : ℕ)
          → x ─[ m + n ]→ z
          → ∃[ y ] (x ─[ m ]→ y × y ─[ n ]→ z)

data Tri (x y : A) : Set where
  tri≡ : x ≡ y → Tri x y
  tri→ : ∀ n → x ─[ suc n ]→ y → Tri x y
  tri← : ∀ n → y ─[ suc n ]→ x → Tri x y

record IsLinear : Set where
  field
    isPath : IsPath
    uniqueˡ : ∀ {x y z n} → x ─[ n ]→ z → y ─[ n ]→ z → x ≡ y
    uniqueʳ : ∀ {x y z n} → x ─[ n ]→ y → x ─[ n ]→ z → y ≡ z
    uniqueᶜ : ∀ {x y m n} → x ─[ m ]→ y → x ─[ n ]→ y → m ≡ n
    acyclic : ∀ {x n} → x ─[ n ]→ x → n ≡ 0
    total : ∀ x y → Tri x y
