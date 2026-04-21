module Gregorianum.DateHour.Base where

open import Gregorianum.Data.Cursor using (Cursor; first; suc; last)
open import Gregorianum.Data.Cursor.Properties using (width≡acc+rem)
open import Gregorianum.Data.Position using (Position; mkPos)
open import Gregorianum.Date as D using (Date; date-first)
import Gregorianum.Date.Properties as D
open import Gregorianum.Hour using (Hour; [_])
open import Data.Nat as ℕ using (ℕ; suc; _+_; _*_)
open import Gregorianum.YearMonth using (suc-year)
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

data IsSuc : DateHour → Set where
  suc-hour : ∀ {acc rem} → {c : Cursor 23 (suc acc) rem} → IsSuc (date-first at [ mkPos c ])
  suc-date : ∀ {dh} → D.IsSuc (DateHour.date dh) → IsSuc dh

isSuc? : ∀ dh → Dec (IsSuc dh)
isSuc? (date at hour) with D.isSuc? date
isSuc? (date at hour) | yes p = yes (suc-date p)
isSuc? (date at [ mkPos (suc cursor) ]) | no ¬isSuc' = yes isSuc
  where
    isSuc : IsSuc (date at [ mkPos (suc cursor) ])
    isSuc with D.¬IsSuc⇒first ¬isSuc'
    ... | refl = suc-hour
isSuc? (date at [ mkPos first ]) | no ¬isSuc' = no ¬isSuc
  where
    ¬isSuc : ¬ IsSuc (date at [ mkPos first ])
    ¬isSuc (suc-date isSuc') = ¬isSuc' isSuc'

next : ∀ (dh₁ : DateHour) → ∃[ dh₂ ] dh₁ ⋖ dh₂
next (date at [ mkPos {rem = suc rem} cursor ]) = (date at [ mkPos (suc cursor) ]) , step-hour
next (d₁ at [ mkPos {rem = ℕ.zero} twenty-fourth ]) = let (d₂ , d₁⋖d₂) = D.next d₁
                                                       in (d₂ at [ mkPos first ]) , step-date d₁⋖d₂
next (d₁ at [ mkPos {rem = ℕ.zero} c@(suc²⁴ _) ]) with width≡acc+rem c
...                                                   | ()

prev : ∀ (dh₂ : DateHour) → IsSuc dh₂ → ∃[ dh₁ ] dh₁ ⋖ dh₂
prev (date at [ mkPos (suc cursor) ]) _ = (date at [ mkPos cursor ]) , step-hour
prev (date at [ mkPos first ]) isSuc with D.isSuc? date
prev (date at [ mkPos first ]) isSuc | yes isSuc' = let (d₁ , d₁⋖d₂) = D.prev date isSuc' in (d₁ at [ mkPos twenty-fourth ]) , step-date d₁⋖d₂
prev (date at [ mkPos first ]) (suc-date isSuc') | no ¬isSuc' = contradiction isSuc' ¬isSuc'

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
