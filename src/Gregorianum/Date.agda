module Gregorianum.Date where

open import Gregorianum.Date.Base public
open import Gregorianum.Date.Properties
open import Gregorianum.Date.Plain using (⟨+_-_-_⟩; ⟨_-_-_⟩ ; toPlain; fromPlain?) public

open import Data.Product using (proj₁)

tomorrow : Date → Date
tomorrow d = proj₁ (tomorrow-exists d)

yesterday : Date → Date
yesterday d = proj₁ (yesterday-exists d)
