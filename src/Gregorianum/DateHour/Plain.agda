module Gregorianum.DateHour.Plain where

open import Gregorianum.DateHour.Base using (DateHour; _at_)

import Gregorianum.Date.Plain as D
import Gregorianum.Hour.Plain as H

open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; toWitness)

data _HasPlain_ (dh : DateHour) : (ℕ × ℕ × ℕ × ℕ) → Set where
  plain : ∀ {y m d h}
        → (DateHour.date dh) D.HasPlain (y , m , d)
        → (DateHour.hour dh) H.HasPlain h
        → dh HasPlain (y , m , d , h)

toPlain : (dh : DateHour) → Σ[ (y , m , d , h) ∈ (ℕ × ℕ × ℕ × ℕ) ] dh HasPlain (y , m , d , h)
toPlain (date at hour) with D.toPlain date
... | _ , D.plain ymp dp = (_ , _ , _ , _) , (plain (D.plain ymp dp) H.plain)

fromPlain? : (q : ℕ × ℕ × ℕ × ℕ) → Dec (∃[ dh ] dh HasPlain q)
fromPlain? (y , m , d , h) with D.fromPlain? (y , m , d) | H.fromPlain? h
... | yes (d , dp) | yes (h , hp) = yes (d at h , plain dp hp)
... | no ¬p | _     = no λ { (dh , plain dp _) → ¬p (DateHour.date dh , dp)}
... | yes _ | no ¬q = no λ { (dh , plain _ hp) → ¬q (DateHour.hour dh , hp)}

⟨_-_-_at_⟩ : (y m d h : ℕ) → {True (fromPlain? (y , m , d , h))} → DateHour
⟨_-_-_at_⟩ y m d h {t} = proj₁ (toWitness t)
