module Gregorianum.Day.Plain where

open import Gregorianum.Day.Base

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Gregorianum.Data.Cursor.Properties as Cursor
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties using (_≤?_; m≤m+n)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data _HasPlain_ {width} (d : Day width) : ℕ → Set where
  plain : d HasPlain (suc (Position.acc d))

toPlain : ∀ {width} → Day width → ℕ
toPlain (pos {acc = acc} _) = suc acc

fromPlain? : ∀ {width : ℕ} → (n : ℕ) → Dec (Σ[ d ∈ Day width ] d HasPlain n)
fromPlain? zero = no λ ()
fromPlain? {width} (suc n) with n ≤? width
...                         | yes n≤width = yes (pos (fromℕ≤ n≤width) , plain)
...                         | no n≰width  = no (h n≰width)
  where
    h : ∀ {width n}
      → ¬ (n ≤ width)
      → ¬ (Σ[ d ∈ Day width ] d HasPlain suc n)
    h n≰width (pos {acc = acc} {rem = rem} c , plain) with Cursor.width≡acc+rem c
    ...                                                | refl = n≰width (m≤m+n acc rem)
