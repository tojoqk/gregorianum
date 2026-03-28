module Gregorianum.Month.Plain.Properties where

open import Gregorianum.Month.Plain.Base using (_HasPlain_; plain)
open import Gregorianum.Month.Base

open import Gregorianum.Data.Cursor using (suc¹²)
open import Gregorianum.Data.Cursor.Position using (mkPos)
open import Gregorianum.Data.Cursor.Properties using (width≡acc+rem)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

month-unique : ∀ {m₁ m₂ n} → m₁ HasPlain n → m₂ HasPlain n → m₁ ≡ m₂
month-unique {january} {january} plain plain = refl
month-unique {february} {february} plain plain = refl
month-unique {march} {march} plain plain = refl
month-unique {april} {april} plain plain = refl
month-unique {may} {may} plain plain = refl
month-unique {june} {june} plain plain = refl
month-unique {july} {july} plain plain = refl
month-unique {august} {august} plain plain = refl
month-unique {september} {september} plain plain = refl
month-unique {october} {october} plain plain = refl
month-unique {november} {november} plain plain = refl
month-unique {december} {december} plain plain = refl
month-unique {[ mkPos c₁@(suc¹² _) ]} {[ mkPos (suc¹² _) ]} plain plain with width≡acc+rem c₁
...                                                                  | ()
