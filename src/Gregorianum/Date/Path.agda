module Gregorianum.Date.Path where

open import Gregorianum.Date.Base
open import Gregorianum.Date.Properties

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
import Gregorianum.Year.Base as Y
import Gregorianum.YearMonth.Base as YM
open import Gregorianum.Month.Base as M
open import Data.Nat as ℕ using (ℕ; suc; zero; _+_; _*_; z≤n; s≤s; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)
import Induction.WellFounded as WF

data _─[_]→_ (x : Date) : ℕ → Date → Set where
  ε : x ─[ zero ]→ x
  extendʳ : ∀ {y z len} → y ⋖ z → x ─[ len ]→ y → x ─[ suc len ]→ z

open import Gregorianum.Relation.Path Date _─[_]→_

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
shiftˡ x⋖y z⋖w ε with prev-date-unique x⋖y z⋖w
...                 | refl = ε
shiftˡ x⋖y z⋖w (extendʳ  w'⋖w y→w) with prev-date-unique z⋖w w'⋖w
...                                    | refl = extendˡ x⋖y y→w

shiftʳ : ∀ {x y z w len}
       → x ⋖ y
       → z ⋖ w
       → x ─[ len ]→ z
       → y ─[ len ]→ w
shiftʳ x⋖y z⋖w ε with next-date-unique x⋖y z⋖w
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
... | y , x₁→y , y→z with nextDate y
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
uniqueˡ (extendʳ z₁⋖z p) (extendʳ z₂⋖z q) with prev-date-unique z₁⋖z z₂⋖z
...                                          | refl with  uniqueˡ p q
...                                                    | refl = refl

uniqueʳ : ∀ {x y z len}
        → x ─[ len ]→ y
        → x ─[ len ]→ z
        → y ≡ z
uniqueʳ ε q with identity⁻¹ q
...            | refl = refl
uniqueʳ (extendʳ x'⋖y p) (extendʳ x'⋖z q) with uniqueʳ p q
...                                          | refl with next-date-unique x'⋖y x'⋖z
...                                                    | refl = refl

private
  pattern date-first = ((zero Y.×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) YM.- mkPos first) - mkPos first ⟨ YM.mkHasDays Y.leap₄₀₀ january-days ⟩

  first→first⇒len≡zero : ∀ {len} → date-first ─[ len ]→ date-first → len ≡ zero
  first→first⇒len≡zero {zero} ε = refl
  first→first⇒len≡zero {suc _} (extendʳ (stepʸᵐ (YM.stepʸ ())) h)

  ¬circle : ∀ {x len}
          → ¬ (x ─[ suc len ]→ x)
  ¬circle {x} x→x with first→first⇒len≡zero (h x x→x (⋖-wellFounded x))
    where
      h : ∀ {len} → ∀ d → d ─[ len ]→ d → WF.Acc _⋖_ d → date-first ─[ len ]→ date-first
      h d ε (WF.acc rs) = ε
      h d (extendʳ d'⋖d d→d) (WF.acc rs) = h _ (extendˡ d'⋖d d→d) (rs d'⋖d)
  ... | ()

acyclic : ∀ {x n} → x ─[ n ]→ x → n ≡ 0
acyclic ε = refl
acyclic p@(extendʳ _ _) = contradiction p ¬circle

private
  fromFirst : ∀ {x len} → x HasOrdinal len → date-first ─[ len ]→ x
  fromFirst {x} {zero} ho with ordinal≡0⇒first ho
  ... | refl = ε
  fromFirst {x} {suc len} ho with prevDate x (suc-ordinal-is-successor ho)
  ... | x' , x'⋖x = extendʳ x'⋖x (fromFirst (prev-date-ordinal x'⋖x ho))

total : ∀ x y → Tri x y
total x y = total' x y (⋖-wellFounded x)
  where
    total' : ∀ x y → WF.Acc _⋖_ x → Tri x y
    total' x y wf with isSuccessor? x | isSuccessor? y
    total' x y wf | no ¬p | no ¬q with ¬IsSuccessor⇒first ¬p | ¬IsSuccessor⇒first ¬q
    ... | refl | refl = tri≡ refl
    total' x y wf | no ¬p | yes _ with ¬IsSuccessor⇒first ¬p
    total' x y wf | no _ | yes isSuc | refl = tri→ (is-successor⇒suc-ordinal isSuc .proj₁) (fromFirst (proj₂ (is-successor⇒suc-ordinal isSuc)))
    total' x y wf | yes _ | no ¬q with ¬IsSuccessor⇒first ¬q
    total' x y wf | yes isSuc | no _ | refl = tri← (is-successor⇒suc-ordinal isSuc .proj₁) (fromFirst (proj₂ (is-successor⇒suc-ordinal isSuc)))
    total' x y (WF.acc rs) | yes isSuc₁ | yes isSuc₂ with prevDate x isSuc₁ | prevDate y isSuc₂
    ... | x' , x'⋖x | y' , y'⋖y with total' x' y' (rs x'⋖x)
    ... | tri≡ refl = tri≡ (next-date-unique x'⋖x y'⋖y)
    ... | tri→ n x'→y' = tri→ n (shiftʳ x'⋖x y'⋖y x'→y')
    ... | tri← n y'→x' = tri← n (shiftʳ y'⋖y x'⋖x y'→x')
