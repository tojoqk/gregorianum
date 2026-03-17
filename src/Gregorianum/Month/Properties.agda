module Gregorianum.Month.Properties where

open import Gregorianum.Month.Base

open import Data.Nat using (ℕ)
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
