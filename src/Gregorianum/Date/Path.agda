module Gregorianum.Date.Path where

open import Gregorianum.Date.Base
open import Gregorianum.Date.Properties

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
import Gregorianum.Year.Base as Y
import Gregorianum.YearMonth.Base as YM
open import Gregorianum.Month.Base as M
open import Data.Nat as ℕ using (ℕ; suc; zero; _+_; _*_; _∸_; z≤n; s≤s; _≤_; _≡ᵇ_; _≟_)
import Data.Nat.Properties as ℕ
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; toWitness)
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
  path-ordinal : ∀ {d₁ d₂ k n} → d₁ ─[ k ]→ d₂ → d₁ HasOrdinal n → d₂ HasOrdinal (k + n)
  path-ordinal ε h = h
  path-ordinal {d₁} {d₂} (extendʳ y⋖d₂ y→d₂) ho₁ with path-ordinal y→d₂ ho₁
  ... | hoy = next-date-ordinal y⋖d₂ hoy

acyclic : ∀ {x n} → x ─[ n ]→ x → n ≡ 0
acyclic {x} {n} x→x with toOrdinal x
... | n' , ho' with path-ordinal x→x ho'
... | h with ordinal-unique h ho'
... | eq = ℕ.+-cancelʳ-≡ n' n 0 eq

private
  ¬circle : ∀ {x len} → ¬ (x ─[ suc len ]→ x)
  ¬circle h with acyclic h
  ...          | ()


private
  from : ∀ {d₁ d₂ n k} → d₁ HasOrdinal n → d₂ HasOrdinal (n + k) → d₁ ─[ k ]→ d₂
  from {n = n} {k = zero} p q rewrite ℕ.+-identityʳ n with date-unique p q
  ... | refl = ε
  from {d₂ = d₂} {n = n} {k = suc k} ho₁ ho₂ rewrite ℕ.+-suc n k with prevDate d₂ (suc-ordinal-is-successor ho₂)
  ... | d₂' , d₂'⋖d₂ with prev-date-ordinal d₂'⋖d₂ ho₂
  ... | ho₂' = extendʳ d₂'⋖d₂ (from ho₁ ho₂')

open import Data.Bool using (Bool; true; false; T)
open import Data.Bool.Properties using (T?)

private
  compare-lemma : ∀ {d₁ d₂ n₁ n₂}
            → d₁ HasOrdinal n₁
            → d₂ HasOrdinal n₂
            → n₁ ℕ.< n₂
            → d₁ ─[ suc (ℕ.pred (n₂ ℕ.∸ n₁)) ]→ d₂
  compare-lemma {d₁} {d₂} {n₁} {n₂} ho₁ ho₂ n₁<n₂ with ℕ.m≤n⇒∃[o]m+o≡n n₁<n₂
  ... | k , refl with prevDate d₂ (suc-ordinal-is-successor ho₂)
  ... | d₂' , d₂'⋖d₂ with prev-date-ordinal d₂'⋖d₂ ho₂
  ... | ho₂' = extendʳ d₂'⋖d₂ (from ho₁ (subst (d₂' HasOrdinal_) eq ho₂'))
    where
      eq : n₁ + k ≡ n₁ + (suc (n₁ + k) ∸ n₁ ∸ 1)
      eq = sym (cong (n₁ +_) (begin
             ((1 + (n₁ + k)) ℕ.∸ n₁) ℕ.∸ 1
           ≡⟨ cong (λ x → x ∸ n₁ ∸ 1) (sym (ℕ.+-suc n₁ k)) ⟩
             (n₁ + suc k ∸ n₁) ∸ 1
           ≡⟨ cong (_∸ 1) (ℕ.m+n∸m≡n n₁ (suc k)) ⟩
             k
           ∎))
        where open ≡-Reasoning

open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

compare : ∀ d₁ d₂ → Tri d₁ d₂
compare d₁ d₂ with toOrdinal d₁ | toOrdinal d₂
... | n₁ , ho₁ | n₂ , ho₂ with ℕ.<-cmp n₁ n₂
... | tri< a ¬b ¬c = tri→ (n₂ ∸ n₁ ∸ 1) (compare-lemma ho₁ ho₂ a)
... | tri≈ ¬a refl ¬c = tri≡ (date-unique ho₁ ho₂)
... | tri> ¬a ¬b c = tri← (n₁ ∸ n₂ ∸ 1) (compare-lemma ho₂ ho₁ c)

total = compare

isLinear : IsLinear
isLinear = record
             { isPath = isPath
             ; uniqueˡ = uniqueˡ
             ; uniqueʳ = uniqueʳ
             ; acyclic = acyclic
             ; total = total
             }

addDays : ∀ d₁ n → ∃[ d₂ ] d₁ ─[ n ]→ d₂
addDays d₁ zero = d₁ , ε
addDays d₁ (suc n) with addDays d₁ n
... | d₂' , h with nextDate d₂'
... | d₂ , d₂'⋖d₂ = d₂ , extendʳ d₂'⋖d₂ h

subtractDays? : ∀ d₂ n → Dec (∃[ d₁ ] d₁ ─[ n ]→ d₂)
subtractDays? d₂ zero = yes (d₂ , ε)
subtractDays? d₂ (suc n) with isSuccessor? d₂
... | yes isSuc with prevDate d₂ isSuc
... | d₂' , d₂'⋖d₂ with subtractDays? d₂' n
... | yes (d₁ , h) = yes (d₁ , extendʳ d₂'⋖d₂ h)
... | no ¬p = no h
  where
    h : ¬ Data.Product.Σ Date (λ d₁ → d₁ ─[ suc n ]→ d₂)
    h (d₁ , extendʳ y⋖d₂ d₁→y) with prev-date-unique d₂'⋖d₂ y⋖d₂
    ... | refl = ¬p (d₁ , d₁→y)
subtractDays? d₂ (suc n) | no ¬isSuc = no λ { (_ , extendʳ x _) → ¬isSuc (∃prev⇒IsSuccessor x)}

private
  unique-len' : ∀ {x y m n} → x ─[ m ]→ y → x ─[ n ]→ y → m ≡ n
  unique-len' {x} {y} {m} {n} p q with toOrdinal x | toOrdinal y
  ... | nx , hox | ny , hoy with ordinal-unique (path-ordinal p hox) (path-ordinal q hox)
  ... | eq = ℕ.+-cancelʳ-≡ nx m n eq

_─[_]→?_ : ∀ d₁ n d₂ → Dec (d₁ ─[ n ]→ d₂)
_─[_]→?_ d₁ n d₂ with compare d₁ d₂
(d₁ ─[ zero ]→? d₂) | tri≡ refl = yes ε
(d₁ ─[ suc n ]→? d₂) | tri≡ refl = no λ { (extendʳ x x₁) → ¬circle (extendʳ x x₁) }
(d₁ ─[ n ]→? d₂) | tri→ k d₁→d₂ with n ≟ (suc k)
... | yes refl = yes d₁→d₂
(d₁ ─[ n ]→? d₂) | tri→ k d₁→d₂ | no ¬p = no λ d₁→d₂' → ¬p (unique-len' d₁→d₂' d₁→d₂)
(d₁ ─[ n ]→? d₂) | tri← k x = no λ {x₁ → ¬circle (trans x x₁)}
