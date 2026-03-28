module Gregorianum.Date.Plain where

open import Gregorianum.Date.Base using (Date; _-_⟨_⟩)
open import Gregorianum.Day.Base using (Day)
open import Gregorianum.YearMonth.Plain.Properties using (yearMonth-unique)
open import Gregorianum.Day.Plain using () renaming (_HasPlain_ to _DayHasPlain_; plain to dayPlain; fromPlain? to dayFromPlain?)
open import Gregorianum.YearMonth.Base using (days)
open import Gregorianum.YearMonth.Plain using () renaming (_HasPlain_ to _YmHasPlain_; toPlain to ymToPlain; fromPlain? to ymFromPlain?)
open import Gregorianum.YearMonth.Properties using (days-unique)
open import Gregorianum.Data.Cursor.Position using (Position)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; toWitness)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data _HasPlain_ (date : Date) : (ℕ × ℕ × ℕ) → Set where
  plain : ∀ {y m d}
        → (Date.yearMonth date) YmHasPlain (y , m)
        → (Date.day date) DayHasPlain d
        → date HasPlain (y , m , d)

toPlain : (date : Date) → ∃[ tri ] date HasPlain tri
toPlain (ym - day ⟨ _ ⟩) with ymToPlain ym
...                         | (y , m) , p = (y , m , suc (Position.toℕ (Day.position day))) , plain p dayPlain

fromPlain? : (tri : ℕ × ℕ × ℕ) → Dec (∃[ date ] date HasPlain tri)
fromPlain? (y , m , d) with ymFromPlain? (y , m)
fromPlain? (y , m , d) | yes (ym , pʸᵐ) with days ym
fromPlain? (y , m , d) | yes (ym , pʸᵐ) | suc width , hasDays with dayFromPlain? {width} d
fromPlain? (y , m , d) | yes (ym , pʸᵐ) | suc width , hasDays | yes (day , pᵈ) = yes ((ym - day ⟨ hasDays ⟩) , plain pʸᵐ pᵈ)
fromPlain? (y , m , d) | yes (ym , pʸᵐ) | suc width , hasDays | no ¬q = no h
  where
    h : ¬ (∃[ date ] date HasPlain (y , m , d))
    h ((ym' - d' ⟨ hasDays' ⟩) , plain pʸᵐ' pᵈ') with yearMonth-unique pʸᵐ pʸᵐ'
    h ((ym' - d' ⟨ hasDays' ⟩) , plain pʸᵐ' pᵈ') | refl with days-unique hasDays hasDays'
    ... | refl = ¬q (d' , pᵈ')
fromPlain? (y , m , d) | no ¬p = no λ { (fst , plain x x₁) → ¬p (Date.yearMonth fst , x)}

⟨_-_-_⟩ : (y : ℕ) → (m d : ℕ) → {True (fromPlain? (y , m , d))} → Date
⟨_-_-_⟩ y m d {t} = proj₁ (toWitness t)
