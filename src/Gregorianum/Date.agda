module Gregorianum.Date where

open import Gregorianum.Date.Base public
open import Gregorianum.Date.Properties
open import Gregorianum.Date.Plain using (⟨+_-_-_⟩; ⟨_-_-_⟩ ; toPlain; fromPlain?) public

open import Data.Product using (proj₁)

nextDay : Date → Date
nextDay d = proj₁ (next-day-exists d)

prevDay : Date → Date
prevDay d = proj₁ (prev-day-exists d)
