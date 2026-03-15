module Gregorianum.Year.Path where

open import Gregorianum.Year.Base

open import Gregorianum.Year.Properties as Y
open import Gregorianum.Year.Epoch as Y
open import Gregorianum.Year.Epoch.Properties as Y

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
import Gregorianum.Data.Cursor.Properties as Cursor

open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

data _─[_]→_ (x : Year) : ℕ → Year → Set where
  ε : x ─[ zero ]→ x
  extendʳ : ∀ {y z len} → y ⋖ z → x ─[ len ]→ y → x ─[ suc len ]→ z

open import Gregorianum.Relation.Path Year _─[_]→_

extendˡ : ∀ {x y z len}
        → x ⋖ y
        → y ─[ len ]→ z
        → x ─[ suc len ]→ z
extendˡ x⋖y ε = extendʳ x⋖y ε
extendˡ x⋖y (extendʳ y⋖z y→z) = extendʳ y⋖z (extendˡ x⋖y y→z)

shiftˡ : ∀ {x y z w len}
       → x ⋖ y
       → z ⋖ w
       → y ─[ len ]→ w
       → x ─[ len ]→ z
shiftˡ x⋖y z⋖w ε with Y.prevYear-unique x⋖y z⋖w
...                   | refl = ε
shiftˡ x⋖y z⋖w (extendʳ  w'⋖w y→w) with Y.prevYear-unique z⋖w w'⋖w
...                                        | refl = extendˡ x⋖y y→w

shiftʳ : ∀ {x y z w len}
       → x ⋖ y
       → z ⋖ w
       → x ─[ len ]→ z
       → y ─[ len ]→ w
shiftʳ x⋖y z⋖w ε with Y.nextYear-unique x⋖y z⋖w
...                   | refl = ε
shiftʳ x⋖y z⋖w (extendʳ x x→z) = extendʳ z⋖w (shiftʳ x⋖y x x→z)

identity : ∀ {x y} → x ≡ y → x ─[ zero ]→ y
identity refl = ε

identity⁻¹ : ∀ {x y} → x ─[ zero ]→ y → x ≡ y
identity⁻¹ ε = refl

trans : ∀ {x y z len₁ len₂}
      → x ─[ len₁ ]→ y
      → y ─[ len₂ ]→ z
      → x ─[ len₁ + len₂ ]→ z
trans ε y→z = y→z
trans (extendʳ x⋖y x→₂) ε = extendʳ x⋖y (trans x→₂ ε)
trans (extendʳ x⋖y x→₂) (extendʳ y⋖z y→z) = extendʳ y⋖z (trans x→₂ (trans (extendʳ x⋖y ε) y→z))

split : ∀ {x z}
      → ∀ len₁ len₂
      → x ─[ len₁ + len₂ ]→ z
      → ∃[ y ] (x ─[ len₁ ]→ y) × (y ─[ len₂ ]→ z)
split zero len₂ ε = _ , ε , ε
split zero len₂ (extendʳ z'⋖z x→z) = _ , ε , extendʳ z'⋖z x→z
split (suc len₁) len₂ (extendʳ {y = z'} z'⋖z x→z) with split len₁ len₂ x→z
... | y , x₁→y , y→z with nextYear y
... | y' , snd = y' , (extendʳ snd x₁→y , shiftʳ snd z'⋖z y→z)

isPath : IsPath
isPath = record { identity = identity
                ; identity⁻¹ = identity⁻¹
                ; trans = trans
                ; split = split }

uniqueˡ : ∀ {x y z len}
        → x ─[ len ]→ z
        → y ─[ len ]→ z
        → x ≡ y
uniqueˡ ε q with identity⁻¹ q
...            | refl = refl
uniqueˡ (extendʳ z₁⋖z p) (extendʳ z₂⋖z q) with prevYear-unique z₁⋖z z₂⋖z
...                                              | refl with  uniqueˡ p q
...                                                        | refl = refl

uniqueʳ : ∀ {x y z len}
        → x ─[ len ]→ y
        → x ─[ len ]→ z
        → y ≡ z
uniqueʳ ε q with identity⁻¹ q
...            | refl = refl
uniqueʳ (extendʳ x'⋖y p) (extendʳ x'⋖z q) with uniqueʳ p q
...                                              | refl with nextYear-unique x'⋖y x'⋖z
...                                                        | refl = refl

open import Gregorianum.Year.Induction
import Induction.WellFounded as WF

private
  pattern year-first = zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first

  first→first⇒len≡zero : ∀ {len} → year-first ─[ len ]→ year-first → len ≡ zero
  first→first⇒len≡zero {zero} ε = refl
  first→first⇒len≡zero {suc _} (extendʳ () _)

  ¬circle : ∀ {x len}
          → ¬ (x ─[ suc len ]→ x)
  ¬circle {x} x→x with first→first⇒len≡zero (h x x→x (⋖-WellFounded x))
    where
      h : ∀ {len} → ∀ y → y ─[ len ]→ y → WF.Acc _⋖_ y → year-first ─[ len ]→ year-first
      h y ε (WF.acc rs) = ε
      h y (extendʳ y'⋖y y→y) (WF.acc rs) = h _ (extendˡ y'⋖y y→y) (rs y'⋖y)
  ... | ()

acyclic : ∀ {x y m n} → x ─[ m ]→ y → y ─[ n ]→ x → m ≡ 0 × n ≡ 0
acyclic ε ε = refl , refl
acyclic ε (extendʳ x⋖y y→x) = contradiction (extendʳ x⋖y y→x) ¬circle
acyclic (extendʳ x⋖y x→y) ε = contradiction (extendʳ x⋖y x→y) ¬circle
acyclic (extendʳ y'⋖y x→y) (extendʳ x'⋖x y→x) with acyclic x→y (extendʳ x'⋖x (extendˡ y'⋖y y→x))
...                                                    | ()

private
  fromFirst : ∀ {x len} → x HasEpoch len → year-first ─[ len ]→ x
  fromFirst {x} {zero} p with isSuccessor? x
  fromFirst {x} {zero} () | yes suc₁
  fromFirst {x} {zero} () | yes suc₄
  fromFirst {x} {zero} () | yes suc₁₀₀
  fromFirst {x} {zero} () | yes suc₄₀₀
  fromFirst {year-first} {zero} p | no ¬isSuc = ε
  fromFirst {x} {suc len} p with isSuccessor? x
  fromFirst {x} {suc len} p | yes isSuc with prevYear x isSuc
  ... | _ , p' = extendʳ p' (fromFirst (prevYear-epoch p' p))
  fromFirst {x} {suc len} p | no ¬isSuc = contradiction (suc-epoch-is-successor p) ¬isSuc

compare : ∀ x y → Tri x y
compare x y = compare' x y (⋖-WellFounded x)
  where
    compare' : ∀ x y → WF.Acc _⋖_ x → Tri x y
    compare' x y wf with isSuccessor? x | isSuccessor? y
    compare' x y wf | no ¬p | no ¬q with Y.¬IsSuccessor⇒first ¬p | Y.¬IsSuccessor⇒first ¬q
    ... | refl | refl = tri≡ refl
    compare' x y wf | no ¬p | yes _ with Y.¬IsSuccessor⇒first ¬p
    compare' x y wf | no _ | yes isSuc | refl = tri→ (fromFirst (proj₂ (isSuccessor⇒suc-epoch isSuc)))
    compare' x y wf | yes _ | no ¬q with Y.¬IsSuccessor⇒first ¬q
    compare' x y wf | yes isSuc | no _ | refl = tri← (fromFirst (proj₂ (isSuccessor⇒suc-epoch isSuc)))
    compare' x y (WF.acc rs) | yes isSuc₁ | yes isSuc₂ with prevYear x isSuc₁ | prevYear y isSuc₂
    ... | x' , x'⋖x | y' , y'⋖y with compare' x' y' (rs x'⋖x)
    ... | tri≡ refl = tri≡ (nextYear-unique x'⋖x y'⋖y)
    ... | tri→ x'→y' = tri→ (shiftʳ x'⋖x y'⋖y x'→y')
    ... | tri← y'→x' = tri← (shiftʳ y'⋖y x'⋖x y'→x')

isLinear : IsLinear
isLinear = record
             { isPath = isPath
             ; uniqueˡ = uniqueˡ
             ; uniqueʳ = uniqueʳ
             ; acyclic = acyclic
             ; compare = compare
             }
