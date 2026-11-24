module Gregorianum.DateHour.Base where

open import Gregorianum.Data.Cursor using (Cursor; first; suc; last)
open import Gregorianum.Data.Cursor.Properties using (width≡acc+rem)
open import Gregorianum.Data.Position using (Position; mkPos)
open import Gregorianum.Date as D using (Date; date-first)
import Gregorianum.YearMonth as YM

import Gregorianum.Date.Properties as D
open import Gregorianum.Hour using (Hour; [_])
open import Data.Nat as ℕ using (ℕ; suc; _+_; _*_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction; ¬_)
open import Data.Product using (∃-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record DateHour : Set where
  constructor _at_
  field
    date : Date
    hour : Hour

private
  pattern suc⁴ x = suc (suc (suc (suc x)))
  pattern suc²⁰ x = suc⁴ (suc⁴ (suc⁴ (suc⁴ (suc⁴ x))))
  pattern twenty-fourth = (suc (suc (suc (suc²⁰ first))))
  pattern suc²⁴ x = suc⁴ (suc²⁰ x)

data _⋖_ : DateHour → DateHour → Set where
  step-hour : ∀ {d acc rem} → {c : Cursor 23 acc (suc rem)} → (d at [ mkPos c ]) ⋖ (d at [ mkPos (suc c) ])
  step-date : ∀ {d₁ d₂} → d₁ D.⋖ d₂ → (d₁ at [ mkPos last ]) ⋖ (d₂ at [ mkPos first ])

next : ∀ (dh₁ : DateHour) → ∃[ dh₂ ] dh₁ ⋖ dh₂
next (date at [ mkPos {rem = suc rem} cursor ]) = (date at [ mkPos (suc cursor) ]) , step-hour
next (d₁ at [ mkPos {rem = ℕ.zero} twenty-fourth ]) = let (d₂ , d₁⋖d₂) = D.next d₁
                                                       in (d₂ at [ mkPos first ]) , step-date d₁⋖d₂
next (d₁ at [ mkPos {rem = ℕ.zero} c@(suc²⁴ _) ]) with width≡acc+rem c
...                                                   | ()

prev? : ∀ dh₂ → Dec (∃[ dh₁ ] dh₁ ⋖ dh₂)
prev? (date at [ mkPos first ]) with D.prev? date
... | yes p = yes ((p .proj₁ at [ mkPos last ]) , step-date (p .Data.Product.proj₂))
... | no ¬p with D.¬∃prev⇒first ¬p
... | refl = no λ { (fst , step-date (D.step-month (YM.step-year ())))}
prev? (date at [ mkPos (suc c) ]) = yes ((date at [ mkPos c ]) , step-hour)

data _HasOrdinal_ (dh : DateHour) : (n : ℕ) → Set where
  ordinal : ∀ {ord}
            → (DateHour.date dh) D.HasOrdinal ord
            → dh HasOrdinal (Position.toℕ (Hour.position (DateHour.hour dh)) + ord * 24)

toOrdinal : (dh : DateHour) → ∃[ n ] dh HasOrdinal n
toOrdinal (date at hour) = let (ord , dho) = D.toOrdinal date
                           in Position.acc (Hour.position hour) + ord * 24 , ordinal dho

_<_ : DateHour → DateHour → Set
dh₁ < dh₂ = proj₁ (toOrdinal dh₁) ℕ.< proj₁ (toOrdinal dh₂)

pattern date-hour-first = date-first at [ mkPos first ]
