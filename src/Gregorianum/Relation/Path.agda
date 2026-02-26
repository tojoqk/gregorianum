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
  tri→ : ∀ {n} → x ─[ suc n ]→ y → Tri x y
  tri← : ∀ {n} → y ─[ suc n ]→ x → Tri x y

record IsLinear : Set where
  field
    isPath : IsPath
    uniqueˡ : ∀ {x y z n} → x ─[ n ]→ z → y ─[ n ]→ y → x ≡ y
    uniqueʳ : ∀ {x y z n} → x ─[ n ]→ y → x ─[ n ]→ z → y ≡ z
    acyclic : ∀ {x y m n} → x ─[ m ]→ y → y ─[ n ]→ x → m ≡ 0 × n ≡ 0
    compare : ∀ x y → Tri x y

  open IsPath isPath

  unique-length : ∀ {x y m n} → x ─[ m ]→ y → x ─[ n ]→ y → m ≡ n
  unique-length {m = zero} {n = zero} p q = refl
  unique-length {m = zero} {n = suc n} p q with identity⁻¹ p
  ...                                         | refl with acyclic q q
  ...                                                   | ()
  unique-length {m = suc m} {n = zero} p q with identity⁻¹ q
  ...                                         | refl with acyclic p p
  ...                                                   | ()
  unique-length {m = suc m} {n = suc n} p q with split 1 m p | split 1 n q
  ... | a , x→a , a→y | b , x→b , b→y with uniqueʳ x→a x→b
  ...                                        | refl with unique-length a→y b→y
  ...                                                  | refl = refl
