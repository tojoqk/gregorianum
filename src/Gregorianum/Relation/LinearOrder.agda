open import Gregorianum.Relation.Edge using (IsEdge)
open import Gregorianum.Relation.Path using (IsLinear)

module Gregorianum.Relation.LinearOrder (A : Set)
                                        (_⋖_ : A → A → Set)
                                        (isEdge : IsEdge A _⋖_)
                                        (isLinear : IsLinear A _⋖_ isEdge)
                                        where

open Gregorianum.Relation.Path A _⋖_ isEdge using (_─[_]→_; ε; _▸_; tri≡; tri→; tri←)
open IsLinear isLinear renaming (compare to path-compare)

open import Data.Nat using (ℕ; zero; suc; NonZero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation using (¬_)
open import Data.Product using (_,_)

record _≤_ (x₁ : A) (x₂ : A) : Set where
  constructor ≤⟨_⟩
  field
    {length} : ℕ
    path : x₁ ─[ length ]→ x₂

pattern ≤⟨_⟩[_] path length = record { length = length ; path = path }

≤-refl : ∀ {x} → x ≤ x
≤-refl = ≤⟨ ε ⟩

≤-antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
≤-antisym ≤⟨ p₁ ⟩ ≤⟨ p₂ ⟩ with acyclic p₁ p₂
≤-antisym ≤⟨ ε ⟩ ≤⟨ ε ⟩ | refl , refl = refl

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans x≤y ≤⟨ ε ⟩ = x≤y
≤-trans x≤y ≤⟨ y→z₀ ▸ z₀⋖z ⟩ with ≤-trans x≤y ≤⟨ y→z₀ ⟩
...                               | ≤⟨ x→z₀ ⟩ = ≤⟨ x→z₀ ▸ z₀⋖z ⟩

record _<_ (x₁ : A) (x₂ : A) : Set where
  constructor <⟨_⟩
  field
    {length-1} : ℕ
    path : x₁ ─[ suc length-1 ]→ x₂

pattern <⟨_⟩[1+_] path length-1 = record { length-1 = length-1 ; path = path }

<⇒≤ : ∀ {x y} → x < y → x ≤ y
<⇒≤ <⟨ x→y ⟩ = ≤⟨ x→y ⟩

≤⇒< : ∀ {x y} → ((≤⟨ _ ⟩[ d ]) : x ≤ y) → .{{NonZero d}} → x < y
≤⇒< ≤⟨ x→y ⟩[ (suc _) ] = <⟨ x→y ⟩

<-irrefl : ∀ {x y} → x < y → x ≢ y
<-irrefl <⟨ x→y ⟩ refl with length-zero x→y
...                        | ()

<-asym : ∀ {x y} → x < y → ¬ (y < x)
<-asym <⟨ x→y ⟩ <⟨ y→x ⟩ with acyclic x→y y→x
...                           | ()

<-trans : ∀ {x y z} → x < y → y < z → x < z
<-trans <⟨ x→y ⟩ <⟨ ε ▸ z₀⋖z ⟩[1+ .zero ] = <⟨ x→y ▸ z₀⋖z ⟩
<-trans x<y <⟨ y→z₀@(_ ▸ _) ▸ z₀⋖z ⟩[1+ .(suc _) ] with <-trans x<y (<⟨ y→z₀ ⟩)
...                                                      | <⟨ x→z₀ ⟩ = <⟨ x→z₀ ▸ z₀⋖z ⟩

data Tri (x y : A) : Set where
  tri≡ : x ≡ y → Tri x y
  tri< : x < y → Tri x y
  tri> : y < x → Tri x y

compare : ∀ x y → Tri x y
compare x y with path-compare x y
...            | tri≡ x≡y = tri≡ x≡y
...            | tri→ x→y = tri< <⟨ x→y ⟩
...            | tri← y→x = tri> <⟨ y→x ⟩
