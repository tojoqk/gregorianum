open import Gregorianum.Relation.Edge using (IsEdge)

module Gregorianum.Relation.Path (A : Set)
                                 (_⋖_ : A → A → Set)
                                 (isEdge : IsEdge A _⋖_)
                                 where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁)

data _─[_]→_ (x : A) : ℕ → A → Set where
  ε : x ─[ zero ]→ x
  _▸_ : ∀ {n} {x₁ x₂ : A}
      → x ─[ n ]→ x₁
      → x₁ ⋖ x₂
      → x ─[ suc n ]→ x₂

data Tri (x y : A) : Set where
  tri≡ : x ≡ y → Tri x y
  tri→ : ∀ {n} → x ─[ suc n ]→ y → Tri x y
  tri← : ∀ {n} → y ─[ suc n ]→ x → Tri x y

record IsLinear : Set where
  field
    acyclic : ∀ {x y m n} → x ─[ m ]→ y → y ─[ n ]→ x → m ≡ 0 × n ≡ 0
    compare : ∀ x y → Tri x y

  open IsEdge isEdge renaming (uniqueˡ to edge-uniqueˡ; uniqueʳ to edge-uniqueʳ)

  uniqueˡ : ∀ {x₁ x₂ y n} → x₁ ─[ n ]→ y → x₂ ─[ n ]→ y → x₁ ≡ x₂
  uniqueˡ ε ε = refl
  uniqueˡ (x₁→y₁ ▸ y₁⋖y) (x₂→y₂ ▸ y₂⋖y) with edge-uniqueˡ y₁⋖y y₂⋖y
  ...                                               | refl = uniqueˡ x₁→y₁ x₂→y₂

  uniqueʳ : ∀ {x y₁ y₂ n} → x ─[ n ]→ y₁ → x ─[ n ]→ y₂ → y₁ ≡ y₂
  uniqueʳ ε ε = refl
  uniqueʳ (x→yˡ ▸ y₀⋖y₁) (x→yʳ ▸ y₀⋖y₂) with uniqueʳ x→yˡ x→yʳ
  ...                                         | refl = edge-uniqueʳ y₀⋖y₁ y₀⋖y₂

  length-zero : ∀ {x n} → x ─[ n ]→ x → n ≡ 0
  length-zero p = proj₁ (acyclic p p)

  unique-length : ∀ {x y m n} → x ─[ m ]→ y → x ─[ n ]→ y → m ≡ n
  unique-length ε          q rewrite length-zero q = refl
  unique-length p@(_ ▸ _) ε rewrite length-zero p = refl
  unique-length (p ▸ y₀⋖y) (q ▸ y₁⋖y) rewrite edge-uniqueˡ y₀⋖y y₁⋖y = cong suc (unique-length p q)
