module Gregorianum.Date.Plain where

open import Gregorianum.Date.Base

import Gregorianum.Year.Plain as Y
import Gregorianum.Month.Plain as M
import Gregorianum.Day.Plain as D

import Gregorianum.Year.Base as Y
import Gregorianum.YearMonth.Base as YM
import Gregorianum.YearMonth.Plain as YM
import Gregorianum.Year.Properties as Y
import Gregorianum.Month.Properties as M
import Gregorianum.YearMonth.Properties as YM
open import Gregorianum.Month
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _∸_; z≤n; s≤s)
open import Data.Integer using (ℤ; +_)
open import Data.Nat.Properties using (_≤?_; m≤m+n)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; toWitness)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data _HasPlain_ (date : Date) : (ℤ × ℕ × ℕ) → Set where
  plain : ∀ {y m d}
        → (Date.year-month date) YM.HasPlain (y , m)
        → (Date.day date) D.HasPlain d
        → date HasPlain (y , m , d)

toPlain : Date → ℤ × ℕ × ℕ
toPlain (ym - day) with YM.toPlain ym
...                   | y , m = y , m , (D.toPlain day)

fromPlain? : (tri : ℤ × ℕ × ℕ) → Dec (∃[ date ] date HasPlain tri)
fromPlain? (y , m , d) with YM.fromPlain? (y , m)
fromPlain? (y , m , d) | yes (suc cap , ym , p) with D.fromPlain? {cap} d
fromPlain? (y , m , d) | yes (suc cap , ym , p) | yes (fst , fst₁ , fst₂ , snd) = yes ((ym - fst₂) , plain p snd)
fromPlain? (y , m , d) | yes (suc cap , ((y₁ Y.⟨ yp₁ ⟩ ) YM.- month₁ ⟨ has-days₁ ⟩) , YM.plain (Y.plain refl) mp₁) | no ¬q = no h
  where
    h : ¬ (Σ[ date ∈ Date ] date HasPlain (y , m , d))
    h ((((y₂ Y.⟨ yp₂ ⟩ ) YM.- month₂ ⟨ has-days₂ ⟩) - day) , plain (YM.plain (Y.plain refl) mp₂) dp) with M.month-unique mp₁ mp₂ | Y.year-type-unique yp₁ yp₂
    ... | refl | refl with M.days-unique has-days₁ has-days₂
    ... | refl = ¬q (_ , _ , day , dp)
fromPlain? (y , m , d) | no ¬p = no λ { ((year-month - _) , plain (YM.plain yp mp) D.plain) → ¬p (suc _ , year-month , YM.plain yp mp)}

⟨_-_-_⟩ : (y : ℤ) → (m d : ℕ) → {True (fromPlain? (y , m , d))} → Date
⟨_-_-_⟩ y m d {t} = proj₁ (toWitness t)

⟨+_-_-_⟩ : (y m d : ℕ) → {True (fromPlain? (+ y , m , d))} → Date
⟨+_-_-_⟩ y m d {t} = proj₁ (toWitness t)
