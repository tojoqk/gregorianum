module Gregorianum.Day.Plain where

open import Gregorianum.Day.Base
open import Gregorianum.Day.Properties hiding (day-unique)

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties using (_≤?_; m≤m+n)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data _HasPlain_ {cap acc rem} (d : Day cap acc rem) : ℕ → Set where
  1+acc-is-plain : d HasPlain (suc acc)

toPlain : ∀ {cap acc rem} → Day cap acc rem → ℕ
toPlain {acc = acc} _ = suc acc

fromPlain? : ∀ {cap : ℕ} → (n : ℕ) → Dec (∃[ acc ] ∃[ rem ] Σ[ d ∈ Day cap acc rem ] d HasPlain n)
fromPlain? zero = no λ ()
fromPlain? {cap} (suc n) with n ≤? cap
...                         | yes n≤cap = yes (n , cap ∸ n , fromℕ≤ n≤cap , 1+acc-is-plain)
...                         | no n≰cap  = no (h n≰cap)
  where
    h : ∀ {cap n}
      → ¬ (n ≤ cap)
      → ¬ (∃[ acc ] ∃[ rem ] Σ[ d ∈ Day cap acc rem ] d HasPlain suc n)
    h n≰cap (acc , rem , d , 1+acc-is-plain) with cap≡acc+rem d
    ...                                         | refl = n≰cap (m≤m+n acc rem)

