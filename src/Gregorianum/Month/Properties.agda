module Gregorianum.Month.Properties where

open import Gregorianum.Month.Base

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

has-days-irrelevant : ∀ {my n}
                    → (p q : my HasDays n)
                    → p ≡ q
has-days-irrelevant january january = refl
has-days-irrelevant february-common february-common = refl
has-days-irrelevant february-leap february-leap = refl
has-days-irrelevant march march = refl
has-days-irrelevant april april = refl
has-days-irrelevant may may = refl
has-days-irrelevant june june = refl
has-days-irrelevant july july = refl
has-days-irrelevant august august = refl
has-days-irrelevant september september = refl
has-days-irrelevant october october = refl
has-days-irrelevant november november = refl
has-days-irrelevant december december = refl

days-unique : ∀ {ym} {m n : ℕ}
                → ym HasDays m
                → ym HasDays n
                → m ≡ n
days-unique january january = refl
days-unique february-common february-common = refl
days-unique february-leap february-leap = refl
days-unique march march = refl
days-unique april april = refl
days-unique may may = refl
days-unique june june = refl
days-unique july july = refl
days-unique august august = refl
days-unique september september = refl
days-unique october october = refl
days-unique november november = refl
days-unique december december = refl
