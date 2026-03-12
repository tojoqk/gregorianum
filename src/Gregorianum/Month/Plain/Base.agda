module Gregorianum.Month.Plain.Base where

open import Gregorianum.Month.Base

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Gregorianum.Data.Cursor.Properties as Cursor

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Nat.Properties using (_≤?_; m≤m+n)
open import Relation.Nullary.Negation using (¬_)

data _HasPlain_ (m : Month) : ℕ → Set where
  plain : m HasPlain (suc (Position.toℕ m))

toPlain : (m : Month) → ∃[ n ] m HasPlain n
toPlain (mkPos {acc = acc} _) = suc acc , plain

private
  pattern suc×₁₃ x = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc x))))))))))))

fromPlain? : (n : ℕ) → Dec (∃[ m ] m HasPlain n)
fromPlain? zero = no λ ()
fromPlain? 1 = yes (january , plain)
fromPlain? 2 = yes (february , plain)
fromPlain? 3 = yes (march , plain)
fromPlain? 4 = yes (april , plain)
fromPlain? 5 = yes (may , plain)
fromPlain? 6 = yes (june , plain)
fromPlain? 7 = yes (july , plain)
fromPlain? 8 = yes (august , plain)
fromPlain? 9 = yes (september , plain)
fromPlain? 10 = yes (october , plain)
fromPlain? 11 = yes (november , plain)
fromPlain? 12 = yes (december , plain)
fromPlain? (suc×₁₃ n) = no h
  where
    h : ¬ (∃[ m ] m HasPlain suc×₁₃ n)
    h (mkPos c@(suc×₁₃ _) , _) with Cursor.width≡acc+rem c
    ...                           | ()
