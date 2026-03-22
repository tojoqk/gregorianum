open import Data.Nat using (ℕ)
import Gregorianum.Relation.Path as Path

module Gregorianum.Relation.LinearOrder (A : Set)
                                        (_─[_]→_ : A → ℕ → A → Set)
                                        (isLinear : Path.IsLinear A _─[_]→_)
                                        where

open import Gregorianum.Relation.Path A _─[_]→_ renaming (Tri to PathTri)
open IsLinear isLinear renaming (total to path-total)

open import Data.Nat using (ℕ; zero; suc; NonZero)
import Data.Nat.Properties as ℕ
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Negation using (¬_)
open import Data.Product using (_,_)

record _≼_ (x₁ : A) (x₂ : A) : Set where
  constructor ≼⟨_⟩
  field
    {length} : ℕ
    path : x₁ ─[ length ]→ x₂

pattern ≼⟨_⟩[_] path length = record { length = length ; path = path }

≼-refl : ∀ {x} → x ≼ x
≼-refl {x} = ≼⟨ identity refl ⟩

≼-antisym : ∀ {x y} → x ≼ y → y ≼ x → x ≡ y
≼-antisym ≼⟨ x→y ⟩[ len₁ ] ≼⟨ y→x ⟩[ len₂ ] with acyclic (trans x→y y→x)
... | eq with ℕ.m+n≡0⇒m≡0 len₁ eq | ℕ.m+n≡0⇒n≡0 len₁ eq
... | refl | refl = identity⁻¹ x→y

≼-trans : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
≼-trans ≼⟨ x→y ⟩  ≼⟨ y→z ⟩ = ≼⟨ (trans x→y y→z) ⟩

record _≺_ (x₁ : A) (x₂ : A) : Set where
  constructor ≺⟨_⟩
  field
    {length-1} : ℕ
    path : x₁ ─[ suc length-1 ]→ x₂

pattern ≺⟨_⟩[1+_] path length-1 = record { length-1 = length-1 ; path = path }

≺⇒≼ : ∀ {x y} → x ≺ y → x ≼ y
≺⇒≼ ≺⟨ x→y ⟩ = ≼⟨ x→y ⟩

≼⇒≺ : ∀ {x y} → ((≼⟨ _ ⟩[ d ]) : x ≼ y) → .{{NonZero d}} → x ≺ y
≼⇒≺ ≼⟨ x→y ⟩[ (suc _) ] = ≺⟨ x→y ⟩

≺-irrefl : ∀ {x y} → x ≺ y → x ≢ y
≺-irrefl ≺⟨ x→x ⟩ refl with acyclic x→x
...                        | ()

≺-asym : ∀ {x y} → x ≺ y → ¬ (y ≺ x)
≺-asym ≺⟨ x→y ⟩ ≺⟨ y→x ⟩ with acyclic (trans x→y y→x)
...                           | ()

≺-trans : ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z
≺-trans ≺⟨ x→y ⟩ ≺⟨ y→z ⟩ = ≺⟨ trans x→y y→z ⟩

data Tri (x y : A) : Set where
  tri≡ : x ≡ y → Tri x y
  tri≺ : x ≺ y → Tri x y
  tri≻ : y ≺ x → Tri x y

total : ∀ x y → Tri x y
total x y with path-total x y
...          | tri≡ x≡y = tri≡ x≡y
...          | tri→ _ x→y = tri≺ ≺⟨ x→y ⟩
...          | tri← _ y→x = tri≻ ≺⟨ y→x ⟩
