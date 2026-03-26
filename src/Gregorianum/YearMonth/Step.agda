module Gregorianum.YearMonth.Step where

open import Gregorianum.YearMonth using (YearMonth; _⋖_; IsSuc; isSuc?; nextYearMonth; prevYearMonth; toOrdinal)
open import Gregorianum.YearMonth.Properties using (¬isSuc-unique; next-year-month-unique; prev-year-month-unique; ⋖-wellFounded; ∃prev⇒IsSuc; suc-ordinal-is-successor; prev-year-month-ordinal; next-year-month-ordinal)
import Gregorianum.YearMonth.Timeline as T

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Gregorianum.Relation.Step YearMonth _⋖_

isStep : IsStep
isStep = record
          { IsSuc = IsSuc
          ; isSuc? = isSuc?
          ; ¬isSuc-unique = ¬isSuc-unique
          ; next = nextYearMonth
          ; prev = prevYearMonth
          ; next-unique = next-year-month-unique
          ; prev-unique = prev-year-month-unique
          ; ⋖-wellFounded = ⋖-wellFounded
          }

open Path isStep public

open import Gregorianum.Relation.Path YearMonth _─[_]→_ using (Tri; tri→; tri←; tri≡) public

forward : ∀ x n → ∃[ y ] x ─[ n ]→ y
forward x zero = x , ε
forward x (suc n) = let (y' , x→y') = forward x n in
                    let (y , x⋖y)  = nextYearMonth y' in y , (x→y' ▸ x⋖y)

backward? : ∀ y n → Dec (∃[ x ] x ─[ n ]→ y)
backward? y zero = yes (y , ε)
backward? y (suc n) with isSuc? y
backward? y (suc n) | yes isSuc with prevYearMonth y isSuc
... | y' , y'⋖y with backward? y' n
... | yes (x , x→y) = yes (x , (x→y ▸ y'⋖y))
... | no ¬p = no λ {(x , x→y) → ¬p (x , (x→y ▸⁻¹ y'⋖y))}
backward? y (suc n) | no ¬isSuc = no λ { (_ , (_ ▸ y'⋖y)) → ¬isSuc (∃prev⇒IsSuc y'⋖y)}

fromTimeline : ∀ {x y n} → x T.─[ n ]→ y → x ─[ n ]→ y
fromTimeline {n = zero} x→y with T.identity⁻¹ x→y
... | refl = ε
fromTimeline {y = y} {n = suc n} T.⟨ start , end ⟩ with prevYearMonth y (suc-ordinal-is-successor end)
... | y' , y'⋖y with prev-year-month-ordinal y'⋖y end
... | ho with fromTimeline T.⟨ start , ho ⟩
... | x→y' = x→y' ▸ y'⋖y

toTimeline : ∀ {x y n} → x ─[ n ]→ y → x T.─[ n ]→ y
toTimeline ε = T.identity refl
toTimeline (x→y' ▸ y'⋖y) with toTimeline x→y'
... | T.⟨ start , end' ⟩ = T.⟨ start , next-year-month-ordinal y'⋖y end' ⟩

compare : ∀ x y → Tri x y
compare x y with T.compare x y
... | T.tri≡ x₁ = tri≡ x₁
... | T.tri→ n x→y = tri→ n (fromTimeline x→y)
... | T.tri← n y→x = tri← n (fromTimeline y→x)

_─[_]→?_ : ∀ x n y → Dec (x ─[ n ]→ y)
x ─[ n ]→? y with x T.─[ n ]→? y
... | yes x→y = yes (fromTimeline x→y)
... | no ¬p = no λ {x→y → ¬p (toTimeline x→y)}
