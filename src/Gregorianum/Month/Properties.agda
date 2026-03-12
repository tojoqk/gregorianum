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

HasDays-irrelevant : ∀ {ym n} → (p q : ym HasDays n) → p ≡ q
HasDays-irrelevant january-days january-days = refl
HasDays-irrelevant february-common-days february-common-days = refl
HasDays-irrelevant february-leap-days february-leap-days = refl
HasDays-irrelevant march-days march-days = refl
HasDays-irrelevant april-days april-days = refl
HasDays-irrelevant may-days may-days = refl
HasDays-irrelevant june-days june-days = refl
HasDays-irrelevant july-days july-days = refl
HasDays-irrelevant august-days august-days = refl
HasDays-irrelevant september-days september-days = refl
HasDays-irrelevant october-days october-days = refl
HasDays-irrelevant november-days november-days = refl
HasDays-irrelevant december-days december-days = refl
