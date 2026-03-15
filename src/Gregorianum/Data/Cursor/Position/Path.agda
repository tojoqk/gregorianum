open import Data.Nat using (ℕ; zero; suc; _+_; z≤n; s≤s)

module Gregorianum.Data.Cursor.Position.Path {width : ℕ} where

open import Gregorianum.Data.Cursor.Base
open import Gregorianum.Data.Cursor.Position.Base
open import Gregorianum.Data.Cursor.Properties as Cursor
open import Gregorianum.Data.Cursor.Position.Induction

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Nat.Properties using (≤-refl)

data _─[_]→_ (x : Position width): ℕ → Position width → Set where
  ε : x ─[ zero ]→ x
  extendʳ : ∀ {acc rem} {c : Cursor width acc (suc rem)} {len}
          → x ─[ len ]→ mkPos c
          → x ─[ suc len ]→ mkPos (suc c)

open import Gregorianum.Relation.Path (Position width) _─[_]→_

extendˡ : ∀ {acc rem y}
            {c : Cursor width acc (suc rem)}
            { len }
        → mkPos (suc c) ─[ len ]→ y
        → mkPos c ─[ suc len ]→  y
extendˡ ε = extendʳ ε
extendˡ (extendʳ x→y') = extendʳ (extendˡ x→y')

shiftˡ : ∀ {acc₁ rem₁ acc₂ rem₂}
           {c₁ : Cursor width acc₁ (suc rem₁) }
           {c₂ : Cursor width acc₂ (suc rem₂) }
           {len}
       → mkPos (suc c₁) ─[ len ]→ mkPos (suc c₂)
       → mkPos c₁ ─[ len ]→ mkPos c₂
shiftˡ ε = ε
shiftˡ (extendʳ s→y) = extendˡ s→y

shiftʳ : ∀ {acc₁ rem₁ acc₂ rem₂}
           {c₁ : Cursor width acc₁ (suc rem₁) }
           {c₂ : Cursor width acc₂ (suc rem₂) }
           {len}
       → mkPos c₁ ─[ len ]→ mkPos c₂
       → mkPos (suc c₁) ─[ len ]→ mkPos (suc c₂)
shiftʳ ε = ε
shiftʳ (extendʳ p→y) = extendʳ (shiftʳ p→y)

from-first : ∀ p → mkPos zero ─[ Position.toℕ p ]→ p
from-first (mkPos zero) = ε
from-first (mkPos (suc cursor)) = extendʳ (from-first (mkPos cursor))

private
  ¬last↗ : ∀ {c : Cursor width width zero} {p len}
               → ¬ (mkPos c ─[ suc len ]→ p)
  ¬last↗ {len = suc len} (extendʳ p) = ¬last↗ p

identity : ∀ {x y} → x ≡ y → x ─[ zero ]→ y
identity refl = ε

identity⁻¹ : ∀ {x y} → x ─[ zero ]→ y → x ≡ y
identity⁻¹ ε = refl

trans : ∀ {x y z len₁ len₂}
      → x ─[ len₁ ]→ y
      → y ─[ len₂ ]→ z
      → x ─[ len₁ + len₂ ]→ z
trans ε y→z = y→z
trans (extendʳ x→y) ε = extendʳ (trans x→y ε)
trans (extendʳ x→y) (extendʳ y→z) = extendʳ (trans x→y (trans (extendʳ ε) y→z))

split : ∀ {x z}
      → (len₁ len₂ : ℕ)
      → x ─[ len₁ + len₂ ]→ z
      → ∃[ y ] (x ─[ len₁ ]→ y) × (y ─[ len₂ ]→ z)
split zero len₂ x→z = _ , ε , x→z
split (suc len₁) len₂ (extendʳ x→z) with split len₁ len₂ x→z
split (suc len₁) len₂ (extendʳ x→z) | mkPos {rem = suc rem} c , x→y , y→z' = mkPos (suc c) , extendʳ x→y , shiftʳ y→z'
split {_} (suc len₁) len₂ (extendʳ x→z) | mkPos {rem = zero} c , h , extendʳ {c = c'} {len = suc len'} y→z' with Cursor.rem≡0⇒width≡acc c
... | refl = contradiction y→z' ¬last↗

isPath : IsPath
isPath = record { identity = identity ; identity⁻¹ = identity⁻¹ ; trans = trans ; split = split }

uniqueˡ : ∀ {x y z len}
        → x ─[ len ]→ z
        → y ─[ len ]→ z
        → x ≡ y
uniqueˡ ε ε = refl
uniqueˡ (extendʳ x→z) (extendʳ y→z) = uniqueˡ x→z y→z

uniqueʳ : ∀ {x y z len}
        → x ─[ len ]→ y
        → x ─[ len ]→ z
        → y ≡ z
uniqueʳ ε ε = refl
uniqueʳ (extendʳ x→y) (extendʳ x→z) with uniqueʳ x→y x→z
...                                      | refl = refl

private
  ¬circle : ∀ {x len}
          → ¬ (x ─[ suc len ]→ x)
  ¬circle (extendʳ p) = ¬circle (extendˡ p)

import Induction.WellFounded as WF

private
  acyclic' : ∀ {x y len₁ len₂} → x ─[ len₁ ]→ y → y ─[ len₂ ]→ x → WF.Acc _<_ x → len₁ ≡ 0 × len₂ ≡ 0
  acyclic' ε ε wf = refl , refl
  acyclic' ε (extendʳ y→x) wf = contradiction (extendʳ y→x) ¬circle
  acyclic' (extendʳ x→y) ε wf = contradiction (extendʳ x→y) ¬circle
  acyclic' {mkPos {(suc acc)} (suc c)} (extendʳ x→y) (extendʳ y→x) (WF.acc rs) with extendˡ x→y | extendˡ y→x
  ... | p@(extendʳ _) | q@(extendʳ _) with acyclic' p q (rs ≤-refl)
  ...                                    | ()

acyclic : ∀ {x y len₁ len₂} → x ─[ len₁ ]→ y → y ─[ len₂ ]→ x → len₁ ≡ 0 × len₂ ≡ 0
acyclic {x} p q = acyclic' p q (<-wellFounded x)

compare : ∀ x y → Tri x y
compare (mkPos zero) (mkPos zero) = tri≡ refl
compare (mkPos zero) (mkPos (suc c)) = tri→ (from-first (mkPos (suc c)))
compare (mkPos (suc c)) (mkPos zero) = tri← (from-first (mkPos (suc c)))
compare (mkPos (suc c₁)) (mkPos (suc c₂)) with compare (mkPos c₁) (mkPos c₂)
... | tri≡ refl = tri≡ refl
... | tri→ (extendʳ x→y) = tri→ (shiftʳ (extendʳ x→y))
... | tri← (extendʳ y→x) = tri← (shiftʳ (extendʳ y→x))

isLinear : IsLinear
isLinear = record
            { isPath = isPath
            ; uniqueˡ = uniqueˡ
            ; uniqueʳ = uniqueʳ
            ; acyclic = acyclic
            ; compare = compare
            }
