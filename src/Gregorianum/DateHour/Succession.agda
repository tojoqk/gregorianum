module Gregorianum.DateHour.Succession where

open import Gregorianum.DateHour using (DateHour; _⋖_; next; prev?; toOrdinal)
open import Gregorianum.DateHour.Properties using (¬∃prev-unique; suc-ordinal⇒∃prev; next-unique; prev-unique; ⋖-wellFounded; prev-ordinal; next-ordinal; ⋖-irrelevant)
import Gregorianum.DateHour.Timeline as T

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Gregorianum.Relation.Succession DateHour _⋖_

isSuccession : IsSuccession
isSuccession = record
          { next = next
          ; prev? = prev?
          ; ¬∃prev-unique = ¬∃prev-unique
          ; next-unique = next-unique
          ; prev-unique = prev-unique
          ; ⋖-wellFounded = ⋖-wellFounded
          ; ⋖-irrelevant = ⋖-irrelevant
          }

open Path isSuccession public

open import Gregorianum.DateHour.Timeline using (isTimeline)

isIsoToTimeline : IsIsoToTimeline isSuccession isTimeline
isIsoToTimeline = record
                   { suc-ordinal⇒∃prev = suc-ordinal⇒∃prev
                   ; prev-ordinal = prev-ordinal
                   ; next-ordinal = next-ordinal
                   }

open IsoToTimeline isSuccession isTimeline isIsoToTimeline public
