module Gregorianum.Hour.Plain where

open import Gregorianum.Hour.Base using (Hour; [_])
open import Gregorianum.Data.Cursor using (fromℕ≤)
open import Gregorianum.Data.Position using (Position; mkPos)
open import Gregorianum.Data.Cursor.Properties using (acc≤width)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (∃-syntax; Σ-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

data _HasPlain_ (d : Hour) : ℕ → Set where
  plain : d HasPlain Position.acc (Hour.position d)

toPlain : (d : Hour) → ∃[ n ] d HasPlain n
toPlain ([ mkPos {acc = acc} _ ]) = acc , plain

fromPlain? : ∀ (n : ℕ) → Dec (Σ[ d ∈ Hour ] d HasPlain n)
fromPlain? n with n ≤? 23
... | yes n≤23 = yes ([ (mkPos (fromℕ≤ n≤23)) ] , plain)
... | no n≰23 = no ¬p
  where
    ¬p : ¬ Data.Product.Σ Hour (λ d → d HasPlain n)
    ¬p ([ mkPos c ] , plain) with acc≤width c
    ... | h = n≰23 h
