module Gregorianum.Month.Plain where

open import Gregorianum.Month.Base

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no)

data _HasPlain_ : Month → ℕ → Set where
  january   : january   HasPlain 1
  february  : february  HasPlain 2
  march     : march     HasPlain 3
  april     : april     HasPlain 4
  may       : may       HasPlain 5
  june      : june      HasPlain 6
  july      : july      HasPlain 7
  august    : august    HasPlain 8
  september : september HasPlain 9
  october   : october   HasPlain 10
  november  : november  HasPlain 11
  december  : december  HasPlain 12

plain-exists : ∀ (m : Month) → ∃[ n ] m HasPlain n
plain-exists january   =  1 , january
plain-exists february  =  2 , february
plain-exists march     =  3 , march
plain-exists april     =  4 , april
plain-exists may       =  5 , may
plain-exists june      =  6 , june
plain-exists july      =  7 , july
plain-exists august    =  8 , august
plain-exists september =  9 , september
plain-exists october   = 10 , october
plain-exists november  = 11 , november
plain-exists december  = 12 , december

plain-unique : ∀ {m n₁ n₂}
                    → m HasPlain n₁
                    → m HasPlain n₂
                    → n₁ ≡ n₂
plain-unique january january = refl
plain-unique february february = refl
plain-unique march march = refl
plain-unique april april = refl
plain-unique may may = refl
plain-unique june june = refl
plain-unique july july = refl
plain-unique august august = refl
plain-unique september september = refl
plain-unique october october = refl
plain-unique november november = refl
plain-unique december december = refl

month-unique : ∀ {m₁ m₂ n}
             → m₁ HasPlain n
             → m₂ HasPlain n
             → m₁ ≡ m₂
month-unique january january = refl
month-unique february february = refl
month-unique march march = refl
month-unique april april = refl
month-unique may may = refl
month-unique june june = refl
month-unique july july = refl
month-unique august august = refl
month-unique september september = refl
month-unique october october = refl
month-unique november november = refl
month-unique december december = refl

toPlain : Month → ℕ
toPlain m = proj₁ (plain-exists m)

fromPlain? : (n : ℕ) → (Dec (∃[ m ] m HasPlain n))
fromPlain? 0 = no λ ()
fromPlain? 1 = yes (january , january)
fromPlain? 2 = yes (february , february)
fromPlain? 3 = yes (march , march)
fromPlain? 4 = yes (april , april)
fromPlain? 5 = yes (may , may)
fromPlain? 6 = yes (june , june)
fromPlain? 7 = yes (july , july)
fromPlain? 8 = yes (august , august)
fromPlain? 9 = yes (september , september)
fromPlain? 10 = yes (october , october)
fromPlain? 11 = yes (november , november)
fromPlain? 12 = yes (december , december)
fromPlain? (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n))))))))))))) = no λ ()
