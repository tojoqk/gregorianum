module Gregorianum.Date.Plain where

open import Gregorianum.Date.Base

import Gregorianum.Year.Plain as Y
import Gregorianum.Month.Plain as M
import Gregorianum.Day.Plain as D
import Gregorianum.Day.Base as D

open import Gregorianum.YearMonth.Plain.Properties

import Gregorianum.Year.Base as Y
import Gregorianum.YearMonth.Base as YM
import Gregorianum.YearMonth.Plain as YM
import Gregorianum.Year.Properties as Y
import Gregorianum.Month.Properties as M
import Gregorianum.YearMonth.Properties as YM
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Gregorianum.Data.Cursor.Properties as Cursor
open import Gregorianum.Month
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _∸_; z≤n; s≤s)
open import Data.Integer using (ℤ; +_)
open import Data.Nat.Properties using (_≤?_; m≤m+n)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; toWitness)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


data _HasPlain_ (date : Date) : (ℕ × ℕ × ℕ) → Set where
  plain : ∀ {y m d}
        → (Date.yearMonth date) YM.HasPlain (y , m)
        → (Date.day date) D.HasPlain d
        → date HasPlain (y , m , d)

toPlain : (date : Date) → ∃[ tri ] date HasPlain tri
toPlain (ym - day ⟨ _ ⟩) with YM.toPlain ym
...                         | (y , m) , p = (y , m , suc (Position.toℕ (D.Day.position day))) , plain p D.plain

fromPlain? : (tri : ℕ × ℕ × ℕ) → Dec (∃[ date ] date HasPlain tri)
fromPlain? (y , m , d) with YM.fromPlain? (y , m)
fromPlain? (y , m , d) | yes (ym , pʸᵐ) with YM.days ym
fromPlain? (y , m , d) | yes (ym , pʸᵐ) | suc width , hasDays with D.fromPlain? {width} d
fromPlain? (y , m , d) | yes (ym , pʸᵐ) | suc width , hasDays | yes (day , pᵈ) = yes ((ym - day ⟨ hasDays ⟩) , plain pʸᵐ pᵈ)
fromPlain? (y , m , d) | yes (ym , pʸᵐ) | suc width , hasDays | no ¬q = no h
  where
    h : ¬ (∃[ date ] date HasPlain (y , m , d))
    h ((ym' - d' ⟨ hasDays' ⟩) , plain pʸᵐ' pᵈ') with yearMonth-unique pʸᵐ pʸᵐ'
    h ((ym' - d' ⟨ hasDays' ⟩) , plain pʸᵐ' pᵈ') | refl with YM.days-unique hasDays hasDays'
    ... | refl = ¬q (d' , pᵈ')
fromPlain? (y , m , d) | no ¬p = no λ { (fst , plain x x₁) → ¬p (Date.yearMonth fst , x)}

⟨_-_-_⟩ : (y : ℕ) → (m d : ℕ) → {True (fromPlain? (y , m , d))} → Date
⟨_-_-_⟩ y m d {t} = proj₁ (toWitness t)
