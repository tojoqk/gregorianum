module Gregorianum.Day.Plain where

open import Gregorianum.Day.Base using (Day; [_])
open import Gregorianum.Data.Cursor using (fromℕ≤)
open import Gregorianum.Data.Cursor.Position using (Position; mkPos)
open import Gregorianum.Data.Cursor.Properties using (width≡acc+rem)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (_≤?_; m≤m+n)
open import Data.Product using (∃-syntax; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

data _HasPlain_ {width} (d : Day width) : ℕ → Set where
  plain : d HasPlain (suc (Position.acc (Day.position d)))

toPlain : ∀ {width} → (d : Day width) → ∃[ n ] d HasPlain n
toPlain ([ mkPos {acc = acc} _ ]) = suc acc , plain

fromPlain? : ∀ {width : ℕ} → (n : ℕ) → Dec (Σ[ d ∈ Day width ] d HasPlain n)
fromPlain? zero = no λ ()
fromPlain? {width} (suc n) with n ≤? width
...                         | yes n≤width = yes ([ mkPos (fromℕ≤ n≤width) ] , plain)
...                         | no n≰width  = no (h n≰width)
  where
    h : ∀ {width n}
      → ¬ (n ≤ width)
      → ¬ (Σ[ d ∈ Day width ] d HasPlain suc n)
    h n≰width ([ mkPos {acc = acc} {rem = rem} c ] , plain) with width≡acc+rem c
    ...                                                    | refl = n≰width (m≤m+n acc rem)
