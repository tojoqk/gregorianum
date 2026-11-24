module Gregorianum.Year.Base where

open import Gregorianum.Data.Cursor using (Cursor; first; suc; last)
open import Gregorianum.Data.Position using (Position; mkPos)
open import Gregorianum.Data.Cursor.Properties using (rem≡0⇒width≡acc)

open import Data.Nat as ℕ using (ℕ; suc; zero; NonZero; _+_; _*_)
open import Data.Product using (∃-syntax; _,_; proj₁)
open import Relation.Nullary.Decidable using (Dec; yes; no)

data YearType : Set where
  common : YearType
  leap : YearType

record Year : Set where
  constructor _′_″_‴_
  field
    quadricentennial : ℕ
    pos₁₀₀ : Position 3
    pos₄   : Position 24
    pos₁   : Position 3

pattern year-first = zero ′ mkPos first ″ mkPos first ‴ mkPos first


data _HasYearType_ : Year → YearType → Set where
  common₁ : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄ acc₁ rem₁}
          → {c₁₀₀ : Cursor 3 acc₁₀₀  rem₁₀₀}
          → {c₄ : Cursor 24 acc₄ rem₄}
          → {c₁ : Cursor 3 acc₁ (suc rem₁)}
          → (q ′ mkPos c₁₀₀ ″ mkPos c₄ ‴ mkPos (suc c₁)) HasYearType common
  leap₄ : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄}
        → {c₁₀₀ : Cursor 3 acc₁₀₀ rem₁₀₀}
        → {c₄ : Cursor 24 acc₄ (suc rem₄)}
        → (q ′ mkPos c₁₀₀ ″ mkPos (suc c₄) ‴ mkPos first) HasYearType leap
  common₁₀₀ : ∀ {q acc₁₀₀ rem₁₀₀}
            → {c₁₀₀ : Cursor 3 acc₁₀₀ (suc rem₁₀₀)}
            → (q ′ mkPos (suc c₁₀₀) ″ mkPos first ‴ mkPos first) HasYearType common
  leap₄₀₀ : ∀ {q}
          → (q ′ mkPos first ″ mkPos first ‴ mkPos first) HasYearType leap

data _⋖_ : Year → Year → Set where
  step₁ : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄ acc₁ rem₁}
       → {c₁₀₀ : Cursor 3 acc₁₀₀  rem₁₀₀}
       → {c₄ : Cursor 24 acc₄ rem₄}
       → {c₁ : Cursor 3 acc₁ (suc rem₁)}
       → (q ′ (mkPos c₁₀₀) ″ mkPos c₄ ‴ mkPos c₁) ⋖ (q ′ mkPos c₁₀₀ ″ mkPos c₄ ‴ mkPos (suc c₁))
  step₄ : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄}
       → {c₁₀₀ : Cursor 3 acc₁₀₀ rem₁₀₀}
       → {c₄ : Cursor 24 acc₄ (suc rem₄)}
       → (q ′ (mkPos c₁₀₀) ″ mkPos c₄ ‴ mkPos last) ⋖ (q ′ mkPos c₁₀₀ ″ mkPos (suc c₄) ‴ mkPos first)
  step₁₀₀ : ∀ {q acc₁₀₀ rem₁₀₀}
       → {c₁₀₀ : Cursor 3 acc₁₀₀ (suc rem₁₀₀)}
       → (q ′ mkPos c₁₀₀ ″ mkPos last ‴ mkPos last) ⋖ (q ′ mkPos (suc c₁₀₀) ″ mkPos first ‴ mkPos first)
  step₄₀₀ : ∀ {q}
       → (q ′ mkPos last ″ mkPos last ‴ mkPos last) ⋖ (suc q ′ mkPos first ″ mkPos first ‴ mkPos first)

yearType : (y : Year) → ∃[ yt ] y HasYearType yt
yearType (_ ′ mkPos c₁₀₀ ″ mkPos c₄ ‴ mkPos (suc c₁)) = common , common₁
yearType (_ ′ mkPos c₁₀₀ ″ mkPos (suc c₄) ‴ mkPos first) = leap , leap₄
yearType (_ ′ mkPos (suc c₁₀₀) ″ mkPos first ‴ mkPos first) = common , common₁₀₀
yearType (_ ′ mkPos first ″ mkPos first ‴ mkPos first) = leap , leap₄₀₀

private
  pattern suc⁴ x = suc (suc (suc (suc x)))
  pattern suc⁵ x = suc (suc⁴ x)
  pattern suc²⁵ x = suc⁵ (suc⁵ (suc⁵ (suc⁵ (suc⁵ x))))
  pattern fourth = (suc (suc (suc first)))
  pattern twenty-fifth = suc⁴ (suc⁵ (suc⁵ (suc⁵ (suc⁵ first))))

next : ∀ y₁ → ∃[ y₂ ] y₁ ⋖ y₂
next (q ′ pos₁₀₀ ″ pos₄ ‴ mkPos {rem = suc rem} c₁) = (q ′ pos₁₀₀ ″ pos₄ ‴ mkPos (suc c₁)) , step₁
next (q ′ pos₁₀₀ ″ pos₄ ‴ mkPos {rem = zero} c₁@(suc⁴ _)) with rem≡0⇒width≡acc c₁
...                                                                         | ()
next (q ′ pos₁₀₀ ″ mkPos {rem = suc rem} c₄ ‴ mkPos {rem = zero} fourth) = (q ′ pos₁₀₀ ″ mkPos (suc c₄) ‴ mkPos first) , step₄
next (q ′ pos₁₀₀ ″ mkPos {rem = zero} c₄@(suc²⁵ _) ‴ mkPos {rem = zero} fourth) with rem≡0⇒width≡acc c₄
...                                                                                               | ()
next (q ′ mkPos { rem = suc rem } pos₁₀₀ ″ mkPos {rem = zero} twenty-fifth ‴ mkPos {rem = zero} fourth) = (q ′ mkPos (suc pos₁₀₀) ″ mkPos first ‴ mkPos first) , step₁₀₀
next (q ′ mkPos { rem = zero } c₁₀₀@(suc⁴ _) ″ mkPos {rem = zero} twenty-fifth ‴ mkPos {rem = zero} fourth) with rem≡0⇒width≡acc c₁₀₀
...                                                                                                                           | ()
next (q ′ mkPos { rem = zero } fourth ″ mkPos {rem = zero} twenty-fifth ‴ mkPos {rem = zero} fourth) = (suc q ′ mkPos first ″ mkPos first ‴ mkPos first) , step₄₀₀

prev? : ∀ y₂ → Dec (∃[ y₁ ] y₁ ⋖ y₂)
prev? (quadricentennial ′ pos₁₀₀ ″ pos₄ ‴ mkPos (suc cursor)) = yes (((quadricentennial ′ pos₁₀₀ ″ pos₄ ‴ mkPos cursor)) , step₁)
prev? (quadricentennial ′ pos₁₀₀ ″ mkPos (suc cursor) ‴ mkPos first) = yes ((quadricentennial ′ pos₁₀₀ ″ mkPos cursor ‴ mkPos last) , step₄)
prev? (quadricentennial ′ mkPos (suc cursor) ″ mkPos first ‴ mkPos first) = yes ((quadricentennial ′ mkPos cursor ″ mkPos last ‴ mkPos last) , step₁₀₀)
prev? (suc quadricentennial ′ mkPos first ″ mkPos first ‴ mkPos first) = yes ((quadricentennial ′ mkPos last ″ mkPos last ‴ mkPos last) , step₄₀₀)
prev? year-first = no λ ()

data _HasOrdinal_ (year : Year) : (n : ℕ) → Set where
  ordinal : year HasOrdinal (Position.toℕ (Year.pos₁ year) + Position.toℕ (Year.pos₄ year) * 4 + Position.toℕ (Year.pos₁₀₀ year) * 100 + Year.quadricentennial year * 400)

toOrdinal : (y : Year) → ∃[ n ] y HasOrdinal n
toOrdinal y = _ , ordinal

_<_ : Year → Year → Set
y₁ < y₂ = proj₁ (toOrdinal y₁) ℕ.< proj₁ (toOrdinal y₂)
