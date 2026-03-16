module Gregorianum.Data.Nat.Path where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_)
open import Relation.Nullary.Negation using (¬_; contradiction)

data _─[_]→_ (x : ℕ): ℕ → ℕ → Set where
  ε : x ─[ zero ]→ x
  extendʳ : ∀ {y len} → x ─[ len ]→ y → x ─[ suc len ]→ suc y

module _ where
  open import Gregorianum.Relation.Path ℕ _─[_]→_

  extendˡ : ∀ {x y len}
            → suc x ─[ len ]→ y
            → x ─[ suc len ]→ y
  extendˡ ε = extendʳ ε
  extendˡ (extendʳ x) = extendʳ (extendˡ x)

  shiftˡ : ∀ {x y len}
           → suc x ─[ len ]→ suc y
           → x ─[ len ]→ y
  shiftˡ ε = ε
  shiftˡ (extendʳ x→y) = extendˡ x→y

  shiftʳ : ∀ {x y len}
           → x ─[ len ]→ y
           → suc x ─[ len ]→ suc y
  shiftʳ ε = ε
  shiftʳ (extendʳ x→y₀) = extendʳ (shiftʳ x→y₀)

  from-zero : ∀ len → zero ─[ len ]→ len
  from-zero zero = ε
  from-zero (suc len) = extendʳ (from-zero len)

  private
    identity : ∀ {x y} → x ≡ y → x ─[ zero ]→ y
    identity refl = ε

    identity⁻¹ : ∀ {x y} → x ─[ zero ]→ y → x ≡ y
    identity⁻¹ ε = refl

    trans : ∀ {x y z len₁ len₂ : ℕ}
          → x ─[ len₁ ]→ y
          → y ─[ len₂ ]→ z
          → x ─[ len₁ + len₂ ]→ z
    trans ε y→z = y→z
    trans (extendʳ x→y) ε = extendʳ (trans x→y ε)
    trans (extendʳ x→y) (extendʳ y→z) = extendʳ (trans x→y (trans (extendʳ ε) y→z))

    split : ∀ {x z : ℕ}
          → (len₁ len₂ : ℕ)
          → x ─[ len₁ + len₂ ]→ z
          → ∃[ y ] (x ─[ len₁ ]→ y) × (y ─[ len₂ ]→ z)
    split zero len₂ x→z = _ , ε , x→z
    split (suc len₁) len₂ (extendʳ x→z') with split len₁ len₂ x→z'
    ...                                        | y , x→y , y→z' = suc y , extendʳ x→y , shiftʳ y→z'

  isPath : IsPath
  isPath = record
           { identity = identity
           ; identity⁻¹ = identity⁻¹
           ; trans = trans
           ; split = split
           }

  private
    uniqueˡ : ∀ {x y z len}
            → x ─[ len ]→ z
            → y ─[ len ]→ z
            → x ≡ y
    uniqueˡ ε ε = refl
    uniqueˡ (extendʳ x→z) (extendʳ y→z) = uniqueˡ x→z y→z

    uniqueʳ : ∀ {x y z len} → x ─[ len ]→ y → x ─[ len ]→ z → y ≡ z
    uniqueʳ ε ε = refl
    uniqueʳ (extendʳ x→y) (extendʳ x→z) with uniqueʳ x→y x→z
    ...                                          | refl = refl

    ¬1+→ : ∀ {x len} → ¬ (suc x ─[ len ]→ x)
    ¬1+→ {suc x} {suc zero} (extendʳ ())
    ¬1+→ {suc x} {suc (suc _)} ss→s with shiftˡ ss→s
    ...                                  | s→x with ¬1+→ s→x
    ...                                            | ()

    acyclic : ∀ {x y len₁ len₂ : ℕ} → x ─[ len₁ ]→ y → y ─[ len₂ ]→ x → len₁ ≡ 0 × len₂ ≡ 0
    acyclic ε ε = refl , refl
    acyclic ε (extendʳ y) = contradiction y ¬1+→
    acyclic (extendʳ x) ε = contradiction x ¬1+→
    acyclic (extendʳ s→y₁) (extendʳ s→y₂) with extendˡ s→y₁ | extendˡ s→y₂
    ...                                            | x→y₁' | x→y₂' with acyclic x→y₁' x→y₂'
    ...                                                                 | ()

    compare : ∀ x y → Tri x y
    compare zero zero = tri≡ refl
    compare zero (suc y) = tri→ y (from-zero (suc y))
    compare (suc x) zero = tri← x (from-zero (suc x))
    compare (suc x) (suc y) with compare x y
    ... | tri≡ refl = tri≡ refl
    ... | tri→ n x→y = tri→ n (shiftʳ x→y)
    ... | tri← n y→x = tri← n (shiftʳ y→x)

  isLinear : IsLinear
  isLinear = record
              { isPath = isPath
              ; uniqueˡ = uniqueˡ
              ; uniqueʳ = uniqueʳ
              ; acyclic = acyclic
              ; compare = compare
              }
