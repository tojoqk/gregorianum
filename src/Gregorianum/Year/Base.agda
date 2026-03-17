module Gregorianum.Year.Base where

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position hiding (_<_)
import Gregorianum.Data.Cursor.Properties as Cursor
import Gregorianum.Data.Cursor.Position.Properties as Position
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import Data.Nat as ℕ using (ℕ; suc; zero; NonZero; _+_; _*_)
open import Data.Nat.DivMod using (_divMod_; result)
open import Data.Product using (∃-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

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

data _HasYearType_ : Year → YearType → Set where
  common : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄ acc₁ rem₁}
         → {c₁₀₀ : Cursor 3 acc₁₀₀  rem₁₀₀}
         → {c₄ : Cursor 24 acc₄ rem₄}
         → {c₁ : Cursor 3 (suc acc₁) rem₁}
         → (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos c₄ ×₄+ mkPos c₁) HasYearType common
  leap₄ : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄}
        → {c₁₀₀ : Cursor 3 acc₁₀₀ rem₁₀₀}
        → {c₄ : Cursor 24 (suc acc₄) rem₄}
        → (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos c₄ ×₄+ mkPos zero) HasYearType leap
  common₁₀₀ : ∀ {q acc₁₀₀ rem₁₀₀}
            → {c₁₀₀ : Cursor 3 (suc acc₁₀₀) rem₁₀₀}
            → (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos zero ×₄+ mkPos zero) HasYearType common
  leap₄₀₀ : ∀ {q}
          → (q ×₄₀₀+ mkPos zero ×₁₀₀+ mkPos zero ×₄+ mkPos zero) HasYearType leap

data _⋖_ : Year → Year → Set where
  step : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄ acc₁ rem₁}
       → {c₁₀₀ : Cursor 3 acc₁₀₀  rem₁₀₀}
       → {c₄ : Cursor 24 acc₄ rem₄}
       → {c₁ : Cursor 3 acc₁ (suc rem₁)}
       → (q ×₄₀₀+ (mkPos c₁₀₀) ×₁₀₀+ mkPos c₄  ×₄+ mkPos c₁) ⋖ (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos c₄  ×₄+ mkPos (suc c₁))
  step₄ : ∀ {q acc₁₀₀ rem₁₀₀ acc₄ rem₄}
       → {c₁₀₀ : Cursor 3 acc₁₀₀ rem₁₀₀}
       → {c₄ : Cursor 24 acc₄ (suc rem₄)}
       → (q ×₄₀₀+ (mkPos c₁₀₀) ×₁₀₀+ mkPos c₄ ×₄+ mkPos fourth) ⋖ (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos (suc c₄)  ×₄+ mkPos zero)
  step₁₀₀ : ∀ {q acc₁₀₀ rem₁₀₀}
       → {c₁₀₀ : Cursor 3 acc₁₀₀ (suc rem₁₀₀)}
       → (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos twenty-fifth  ×₄+ mkPos fourth) ⋖ (q ×₄₀₀+ mkPos (suc c₁₀₀) ×₁₀₀+ mkPos zero  ×₄+ mkPos zero)
  step₄₀₀ : ∀ {q}
       → (q ×₄₀₀+ mkPos fourth ×₁₀₀+ mkPos twenty-fifth ×₄+ mkPos fourth) ⋖ (suc q ×₄₀₀+ mkPos zero ×₁₀₀+ mkPos zero  ×₄+ mkPos zero)

_ : Cursor 3 3 zero
_ = fourth

_ : Cursor 24 24 zero
_ = twenty-fifth

data IsSuccessor : Year → Set where
  suc₁ : ∀ {q pos₁₀₀ pos₄ acc₁ rem₁}
        → {c₁ : Cursor 3 (suc acc₁) rem₁}
        → IsSuccessor (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos c₁)
  suc₄ : ∀ {q pos₁₀₀ acc₄ rem₄}
        → {c₄ : Cursor 24 (suc acc₄) rem₄}
        → IsSuccessor (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos c₄ ×₄+ mkPos zero)
  suc₁₀₀ : ∀ {q acc₁₀₀ rem₁₀₀}
          → {c₁₀₀ : Cursor 3 (suc acc₁₀₀) rem₁₀₀}
          → IsSuccessor (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos zero ×₄+ mkPos zero)
  suc₄₀₀ : ∀ {q}
          → IsSuccessor ((suc q) ×₄₀₀+ mkPos zero ×₁₀₀+ mkPos zero ×₄+ mkPos zero)

yearType : (y : Year) → ∃[ yt ] y HasYearType yt
yearType (_ ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos c₄ ×₄+ mkPos (suc c₁)) = common , common
yearType (_ ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos (suc c₄) ×₄+ mkPos first) = leap , leap₄
yearType (_ ×₄₀₀+ mkPos (suc c₁₀₀) ×₁₀₀+ mkPos first ×₄+ mkPos first) = common , common₁₀₀
yearType (_ ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) = leap , leap₄₀₀

nextYear : ∀ y₁ → ∃[ y₂ ] y₁ ⋖ y₂
nextYear (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos {rem = suc rem} c₁) = (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc c₁)) , step
nextYear (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos {rem = zero} c₁@(suc×₄ _)) with Cursor.rem≡0⇒width≡acc c₁
...                                                                         | ()
nextYear (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos {rem = suc rem} c₄ ×₄+ mkPos {rem = zero} fourth) = (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc c₄) ×₄+ mkPos first) , step₄
nextYear (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos {rem = zero} c₄@(suc×₂₅ _) ×₄+ mkPos {rem = zero} fourth) with Cursor.rem≡0⇒width≡acc c₄
...                                                                                               | ()
nextYear (q ×₄₀₀+ mkPos { rem = suc rem } pos₁₀₀ ×₁₀₀+ mkPos {rem = zero} twenty-fifth ×₄+ mkPos {rem = zero} fourth) = (q ×₄₀₀+ mkPos (suc pos₁₀₀) ×₁₀₀+ mkPos first ×₄+ mkPos first) , step₁₀₀
nextYear (q ×₄₀₀+ mkPos { rem = zero } c₁₀₀@(suc×₄ _) ×₁₀₀+ mkPos {rem = zero} twenty-fifth ×₄+ mkPos {rem = zero} fourth) with Cursor.rem≡0⇒width≡acc c₁₀₀
...                                                                                                                           | ()
nextYear (q ×₄₀₀+ mkPos { rem = zero } fourth ×₁₀₀+ mkPos {rem = zero} twenty-fifth ×₄+ mkPos {rem = zero} fourth) = (suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) , step₄₀₀

prevYear : ∀ y₂ → IsSuccessor y₂ → ∃[ y₁ ] y₁ ⋖ y₂
prevYear (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc c₁)) suc₁ = (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos c₁) , step
prevYear (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc c₄) ×₄+ mkPos zero) suc₄ = (q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos c₄ ×₄+ mkPos fourth) , step₄
prevYear (q ×₄₀₀+ mkPos (suc c₁₀₀) ×₁₀₀+ mkPos zero ×₄+ mkPos zero) suc₁₀₀ = (q ×₄₀₀+ mkPos c₁₀₀ ×₁₀₀+ mkPos twenty-fifth ×₄+ mkPos fourth) , step₁₀₀
prevYear (suc q ×₄₀₀+ mkPos zero ×₁₀₀+ mkPos zero ×₄+ mkPos zero) suc₄₀₀ = (q ×₄₀₀+ mkPos fourth ×₁₀₀+ mkPos twenty-fifth ×₄+ mkPos fourth) , step₄₀₀

isSuccessor? : (y : Year) → Dec (IsSuccessor y)
isSuccessor? (quadricentennial ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)) = yes suc₁
isSuccessor? (quadricentennial ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first) = yes suc₄
isSuccessor? (quadricentennial ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first) = yes suc₁₀₀
isSuccessor? (suc quadricentennial ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) = yes suc₄₀₀
isSuccessor? (zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first) = no λ ()

data _HasWeight_ (year : Year) : (n : ℕ) → {{NonZero n}} → Set where
  has-weight : year HasWeight (1 + (Position.toℕ (Year.pos₁ year) + (Position.toℕ (Year.pos₄ year) + (Position.toℕ (Year.pos₁₀₀ year) + Year.quadricentennial year * 4) * 25) * 4))

toWeight : (y : Year) → ∃[ n ] y HasWeight (suc n)
toWeight (q ×₄₀₀+ y₁₀₀ ×₁₀₀+ y₄ ×₄+ y₁) = _ , has-weight

fromWeight : (n : ℕ) → {{_ : NonZero n}} → ∃[ y ] y HasWeight n
fromWeight (suc n) with n divMod 4
... | result q₄ r₄ p₄ with q₄ divMod 25
... | result q₁₀₀ r₁₀₀ p₁₀₀ with q₁₀₀ divMod 4
... | result q₄₀₀ r₄₀₀ p₄₀₀ = (q₄₀₀ ×₄₀₀+ fromFin r₄₀₀ ×₁₀₀+ fromFin r₁₀₀ ×₄+ fromFin r₄) , h
  where
    h : (q₄₀₀ ×₄₀₀+ fromFin r₄₀₀ ×₁₀₀+ fromFin r₁₀₀ ×₄+ fromFin r₄) HasWeight (suc n)
    h rewrite p₄
              | p₁₀₀
              | p₄₀₀
              | sym (Position.toℕ∘fromFin≡toℕ r₄₀₀)
              | sym (Position.toℕ∘fromFin≡toℕ r₁₀₀)
              | sym (Position.toℕ∘fromFin≡toℕ r₄) = has-weight

data _HasLeapWeight_ (year : Year) : (n : ℕ) → {{NonZero n}} → Set where
  has-weight : year HasLeapWeight (suc (Position.toℕ (Year.pos₄ year)) + Position.toℕ (Year.pos₁₀₀ year) * 24 + Year.quadricentennial year * 97)
  
toLeapWeight : (y : Year) → ∃[ n ] y HasLeapWeight (suc n) 
toLeapWeight y = _ , has-weight

data _HasCommonWeight_ (year : Year) : (n : ℕ) → Set where
  has-weight : year HasCommonWeight (Position.toℕ (Year.pos₁ year) + Position.toℕ (Year.pos₄ year) * 3 + Position.toℕ (Year.pos₁₀₀ year) * 76 + Year.quadricentennial year * 303)

toCommonWeight : (y : Year) → ∃[ n ] y HasCommonWeight n 
toCommonWeight y = _ , has-weight

_<_ : Year → Year → Set
y₁ < y₂ = proj₁ (toWeight y₁) ℕ.< proj₁ (toWeight y₂)
