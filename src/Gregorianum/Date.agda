module Gregorianum.Date where

open import Gregorianum.Date.Base public
open import Gregorianum.Date.Plain using (⟨_-_-_⟩ ; toPlain; fromPlain?) public

open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Gregorianum.Date.Properties

prev? : ∀ d₂ → Dec (∃[ d₁ ] d₁ ⋖ d₂)
prev? d₂ with isSuc? d₂
... | yes isSuc = yes (prev d₂ isSuc)
... | no ¬isSuc = no λ { (_ , d₁⋖d₂) → ¬isSuc (∃prev⇒IsSuc d₁⋖d₂)}
