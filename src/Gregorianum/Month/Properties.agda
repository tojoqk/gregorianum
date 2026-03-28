module Gregorianum.Month.Properties where

open import Gregorianum.Month.Base
open import Gregorianum.Data.Cursor.Base
open import Gregorianum.Data.Cursor.Position.Base

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

days-unique : ∀ {ym} {m n : ℕ}
                → ym HasDays m
                → ym HasDays n
                → m ≡ n
days-unique january-days january-days = refl
days-unique february-common-days february-common-days = refl
days-unique february-leap-days february-leap-days = refl
days-unique march-days march-days = refl
days-unique april-days april-days = refl
days-unique may-days may-days = refl
days-unique june-days june-days = refl
days-unique july-days july-days = refl
days-unique august-days august-days = refl
days-unique september-days september-days = refl
days-unique october-days october-days = refl
days-unique november-days november-days = refl
days-unique december-days december-days = refl

has-days-irrelevant : ∀ {ym n} → (p q : ym HasDays n) → p ≡ q
has-days-irrelevant january-days january-days = refl
has-days-irrelevant february-common-days february-common-days = refl
has-days-irrelevant february-leap-days february-leap-days = refl
has-days-irrelevant march-days march-days = refl
has-days-irrelevant april-days april-days = refl
has-days-irrelevant may-days may-days = refl
has-days-irrelevant june-days june-days = refl
has-days-irrelevant july-days july-days = refl
has-days-irrelevant august-days august-days = refl
has-days-irrelevant september-days september-days = refl
has-days-irrelevant october-days october-days = refl
has-days-irrelevant november-days november-days = refl
has-days-irrelevant december-days december-days = refl

open import Data.Product using (_,_; _×_)

day-weight-unique : ∀ {yt m w₁ w₂} → (yt , m) HasDayWeight w₁ → (yt , m) HasDayWeight w₂ → w₁ ≡ w₂
day-weight-unique january-weight january-weight = refl
day-weight-unique february-weight february-weight = refl
day-weight-unique march-common-weight march-common-weight = refl
day-weight-unique april-common-weight april-common-weight = refl
day-weight-unique may-common-weight may-common-weight = refl
day-weight-unique june-common-weight june-common-weight = refl
day-weight-unique july-common-weight july-common-weight = refl
day-weight-unique august-common-weight august-common-weight = refl
day-weight-unique september-common-weight september-common-weight = refl
day-weight-unique october-common-weight october-common-weight = refl
day-weight-unique november-common-weight november-common-weight = refl
day-weight-unique december-common-weight december-common-weight = refl
day-weight-unique march-leap-weight march-leap-weight = refl
day-weight-unique april-leap-weight april-leap-weight = refl
day-weight-unique may-leap-weight may-leap-weight = refl
day-weight-unique june-leap-weight june-leap-weight = refl
day-weight-unique july-leap-weight july-leap-weight = refl
day-weight-unique august-leap-weight august-leap-weight = refl
day-weight-unique september-leap-weight september-leap-weight = refl
day-weight-unique october-leap-weight october-leap-weight = refl
day-weight-unique november-leap-weight november-leap-weight = refl
day-weight-unique december-leap-weight december-leap-weight = refl

next-month-day-weight : ∀ {acc rem yt ds w}
                      → {c : Cursor 11 acc (suc rem)}
                      → (yt , [ mkPos c ]) HasDays ds
                      → (yt , [ mkPos c ]) HasDayWeight w
                      → (yt , [ mkPos (suc c) ]) HasDayWeight (ds + w)
next-month-day-weight january-days january-weight = february-weight
next-month-day-weight february-common-days february-weight = march-common-weight
next-month-day-weight february-leap-days february-weight = march-leap-weight
next-month-day-weight march-days march-common-weight = april-common-weight
next-month-day-weight march-days march-leap-weight = april-leap-weight
next-month-day-weight april-days april-common-weight = may-common-weight
next-month-day-weight april-days april-leap-weight = may-leap-weight
next-month-day-weight may-days may-common-weight = june-common-weight
next-month-day-weight may-days may-leap-weight = june-leap-weight
next-month-day-weight june-days june-common-weight = july-common-weight
next-month-day-weight june-days june-leap-weight = july-leap-weight
next-month-day-weight july-days july-common-weight = august-common-weight
next-month-day-weight july-days july-leap-weight = august-leap-weight
next-month-day-weight august-days august-common-weight = september-common-weight
next-month-day-weight august-days august-leap-weight = september-leap-weight
next-month-day-weight september-days september-common-weight = october-common-weight
next-month-day-weight september-days september-leap-weight = october-leap-weight
next-month-day-weight october-days october-common-weight = november-common-weight
next-month-day-weight october-days october-leap-weight = november-leap-weight
next-month-day-weight november-days november-common-weight = december-common-weight
next-month-day-weight november-days november-leap-weight = december-leap-weight
