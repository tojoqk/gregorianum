module Gregorianum.Month.Plain.Properties where

open import Gregorianum.Month.Base
open import Gregorianum.Month.Plain.Base

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Gregorianum.Data.Cursor.Properties as Cursor
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

month-unique : ∀ {m₁ m₂ n} → m₁ HasPlain n → m₂ HasPlain n → m₁ ≡ m₂
month-unique {mkPos first} {mkPos first} plain plain = refl
month-unique {mkPos second} {mkPos second} plain plain = refl
month-unique {mkPos third} {mkPos third} plain plain = refl
month-unique {mkPos fourth} {mkPos fourth} plain plain = refl
month-unique {mkPos fifth} {mkPos fifth} plain plain = refl
month-unique {mkPos sixth} {mkPos sixth} plain plain = refl
month-unique {mkPos seventh} {mkPos seventh} plain plain = refl
month-unique {mkPos eighth} {mkPos eighth} plain plain = refl
month-unique {mkPos ninth} {mkPos ninth} plain plain = refl
month-unique {mkPos tenth} {mkPos tenth} plain plain = refl
month-unique {mkPos eleventh} {mkPos eleventh} plain plain = refl
month-unique {mkPos twelfth} {mkPos twelfth} plain plain = refl
month-unique {mkPos c₁@(suc×₁₂ _)} {mkPos (suc×₁₂ _)} plain plain with Cursor.width≡acc+rem c₁
...                                                                  | ()
