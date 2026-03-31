module Gregorianum.Year.Base where

open import Gregorianum.Data.Cursor using (Cursor; zero; suc; first; last)
open import Gregorianum.Data.Position using (Position; mkPos)
open import Gregorianum.Data.Cursor.Properties using (rem≡0⇒width≡acc)

open import Data.Nat as ℕ using (ℕ; suc; zero; NonZero; _+_; _*_)
open import Data.Product using (∃-syntax; _,_; proj₁)
open import Relation.Nullary.Decidable using (Dec; yes; no)

data YearType : Set where
  common : YearType
  leap : YearType

record Year : Set where
  constructor _×₄₀₀+_×₁₀₀+_×₄+_
  field
    quadricentennial : ℕ
    pos₁₀₀ : Position 3
    pos₄   : Position 24
    pos₁   : Position 3

pattern year-first = zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first

data _HasYearType_ : Year → YearType → Set where
  common₁ : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄ acc₁ rem₁}
          → {c₁₀₀ : Cursor 3 acc₁₀₀  rem₁₀₀}
          → {c₄ : Cursor 24 acc₄ rem₄}
          → {c₁ : Cursor 3 acc₁ (suc rem₁)}
          → (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos c₄ ×₄+ mkPos (suc c₁)) HasYearType common
  leap₄ : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄}
        → {c₁₀₀ : Cursor 3 acc₁₀₀ rem₁₀₀}
        → {c₄ : Cursor 24 acc₄ (suc rem₄)}
        → (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos (suc c₄) ×₄+ mkPos zero) HasYearType leap
  common₁₀₀ : ∀ {q acc₁₀₀ rem₁₀₀}
            → {c₁₀₀ : Cursor 3 acc₁₀₀ (suc rem₁₀₀)}
            → (q ×₄₀₀+ mkPos (suc c₁₀₀) ×₁₀₀+ mkPos zero ×₄+ mkPos zero) HasYearType common
  leap₄₀₀ : ∀ {q}
          → (q ×₄₀₀+ mkPos zero ×₁₀₀+ mkPos zero ×₄+ mkPos zero) HasYearType leap

data _⋖_ : Year → Year → Set where
  step₁ : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄ acc₁ rem₁}
       → {c₁₀₀ : Cursor 3 acc₁₀₀  rem₁₀₀}
       → {c₄ : Cursor 24 acc₄ rem₄}
       → {c₁ : Cursor 3 acc₁ (suc rem₁)}
       → (q ×₄₀₀+ (mkPos c₁₀₀) ×₁₀₀+ mkPos c₄ ×₄+ mkPos c₁) ⋖ (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos c₄ ×₄+ mkPos (suc c₁))
  step₄ : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄}
       → {c₁₀₀ : Cursor 3 acc₁₀₀ rem₁₀₀}
       → {c₄ : Cursor 24 acc₄ (suc rem₄)}
       → (q ×₄₀₀+ (mkPos c₁₀₀) ×₁₀₀+ mkPos c₄ ×₄+ mkPos last) ⋖ (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos (suc c₄) ×₄+ mkPos first)
  step₁₀₀ : ∀ {q acc₁₀₀ rem₁₀₀}
       → {c₁₀₀ : Cursor 3 acc₁₀₀ (suc rem₁₀₀)}
       → (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos last ×₄+ mkPos last) ⋖ (q ×₄₀₀+ mkPos (suc c₁₀₀) ×₁₀₀+ mkPos first ×₄+ mkPos first)
  step₄₀₀ : ∀ {q}
       → (q ×₄₀₀+ mkPos last ×₁₀₀+ mkPos last ×₄+ mkPos last) ⋖ (suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first)

data IsSuc : Year → Set where
  suc₁ : ∀ {q pos₁₀₀ pos₄ acc₁ rem₁}
        → {c₁ : Cursor 3 acc₁ (suc rem₁)}
        → IsSuc (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc c₁))
  suc₄ : ∀ {q pos₁₀₀ acc₄ rem₄}
        → {c₄ : Cursor 24 acc₄ (suc rem₄)}
        → IsSuc (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc c₄) ×₄+ mkPos zero)
  suc₁₀₀ : ∀ {q acc₁₀₀ rem₁₀₀}
          → {c₁₀₀ : Cursor 3 acc₁₀₀ (suc rem₁₀₀)}
          → IsSuc (q ×₄₀₀+ mkPos (suc c₁₀₀) ×₁₀₀+ mkPos zero ×₄+ mkPos zero)
  suc₄₀₀ : ∀ {q}
          → IsSuc ((suc q) ×₄₀₀+ mkPos zero ×₁₀₀+ mkPos zero ×₄+ mkPos zero)

yearType : (y : Year) → ∃[ yt ] y HasYearType yt
yearType (_ ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos c₄ ×₄+ mkPos (suc c₁)) = common , common₁
yearType (_ ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos (suc c₄) ×₄+ mkPos first) = leap , leap₄
yearType (_ ×₄₀₀+ mkPos (suc c₁₀₀) ×₁₀₀+ mkPos first ×₄+ mkPos first) = common , common₁₀₀
yearType (_ ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) = leap , leap₄₀₀

private
  pattern suc⁴ x = suc (suc (suc (suc x)))
  pattern suc⁵ x = suc (suc⁴ x)
  pattern suc²⁵ x = suc⁵ (suc⁵ (suc⁵ (suc⁵ (suc⁵ x))))
  pattern fourth = (suc (suc (suc zero)))
  pattern twenty-fifth = suc⁴ (suc⁵ (suc⁵ (suc⁵ (suc⁵ zero))))

next : ∀ y₁ → ∃[ y₂ ] y₁ ⋖ y₂
next (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos {rem = suc rem} c₁) = (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc c₁)) , step₁
next (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos {rem = zero} c₁@(suc⁴ _)) with rem≡0⇒width≡acc c₁
...                                                                         | ()
next (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos {rem = suc rem} c₄ ×₄+ mkPos {rem = zero} fourth) = (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc c₄) ×₄+ mkPos first) , step₄
next (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos {rem = zero} c₄@(suc²⁵ _) ×₄+ mkPos {rem = zero} fourth) with rem≡0⇒width≡acc c₄
...                                                                                               | ()
next (q ×₄₀₀+ mkPos { rem = suc rem } pos₁₀₀ ×₁₀₀+ mkPos {rem = zero} twenty-fifth ×₄+ mkPos {rem = zero} fourth) = (q ×₄₀₀+ mkPos (suc pos₁₀₀) ×₁₀₀+ mkPos first ×₄+ mkPos first) , step₁₀₀
next (q ×₄₀₀+ mkPos { rem = zero } c₁₀₀@(suc⁴ _) ×₁₀₀+ mkPos {rem = zero} twenty-fifth ×₄+ mkPos {rem = zero} fourth) with rem≡0⇒width≡acc c₁₀₀
...                                                                                                                           | ()
next (q ×₄₀₀+ mkPos { rem = zero } fourth ×₁₀₀+ mkPos {rem = zero} twenty-fifth ×₄+ mkPos {rem = zero} fourth) = (suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) , step₄₀₀

prev : ∀ y₂ → IsSuc y₂ → ∃[ y₁ ] y₁ ⋖ y₂
prev (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc c₁)) suc₁ = (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos c₁) , step₁
prev (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc c₄) ×₄+ mkPos zero) suc₄ = (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos c₄ ×₄+ mkPos fourth) , step₄
prev (q ×₄₀₀+ mkPos (suc c₁₀₀) ×₁₀₀+ mkPos zero ×₄+ mkPos zero) suc₁₀₀ = (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos twenty-fifth ×₄+ mkPos fourth) , step₁₀₀
prev (suc q ×₄₀₀+ mkPos zero ×₁₀₀+ mkPos zero ×₄+ mkPos zero) suc₄₀₀ = (q ×₄₀₀+ mkPos fourth ×₁₀₀+ mkPos twenty-fifth ×₄+ mkPos fourth) , step₄₀₀

isSuc? : (y : Year) → Dec (IsSuc y)
isSuc? (quadricentennial ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)) = yes suc₁
isSuc? (quadricentennial ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first) = yes suc₄
isSuc? (quadricentennial ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first) = yes suc₁₀₀
isSuc? (suc quadricentennial ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) = yes suc₄₀₀
isSuc? year-first = no λ ()

data _HasOrdinal_ (year : Year) : (n : ℕ) → Set where
  ordinal : year HasOrdinal (Position.toℕ (Year.pos₁ year) + Position.toℕ (Year.pos₄ year) * 4 + Position.toℕ (Year.pos₁₀₀ year) * 100 + Year.quadricentennial year * 400)

toOrdinal : (y : Year) → ∃[ n ] y HasOrdinal n
toOrdinal y = _ , ordinal

_<_ : Year → Year → Set
y₁ < y₂ = proj₁ (toOrdinal y₁) ℕ.< proj₁ (toOrdinal y₂)
