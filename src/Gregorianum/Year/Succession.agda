module Gregorianum.Year.Succession where

open import Gregorianum.Year using (Year; _⋖_; IsSuc; isSuc?; next; prev; toOrdinal)
open import Gregorianum.Year.Properties using (¬isSuc-unique; next-unique; prev-unique; ⋖-wellFounded; ∃prev⇒IsSuc; suc-ordinal⇒IsSuc; prev-ordinal; next-ordinal; ⋖-irrelevant)
import Gregorianum.Year.Timeline as T

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Gregorianum.Relation.Succession Year _⋖_

isSuccession : IsSuccession
isSuccession = record
          { IsSuc = IsSuc
          ; isSuc? = isSuc?
          ; ¬isSuc-unique = ¬isSuc-unique
          ; next = next
          ; prev = prev
          ; next-unique = next-unique
          ; prev-unique = prev-unique
          ; ⋖-wellFounded = ⋖-wellFounded
          ; ∃prev⇒IsSuc = ∃prev⇒IsSuc
          ; ⋖-irrelevant = ⋖-irrelevant
          }

open Path isSuccession public

open import Gregorianum.Year.Timeline using (isTimeline)

isIsoToTimeline : IsIsoToTimeline isSuccession isTimeline
isIsoToTimeline = record
                   { suc-ordinal⇒IsSuc = suc-ordinal⇒IsSuc
                   ; prev-ordinal = prev-ordinal
                   ; next-ordinal = next-ordinal
                   }

open IsoToTimeline isSuccession isTimeline isIsoToTimeline public
