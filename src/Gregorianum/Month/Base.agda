module Gregorianum.Month.Base where

open import Gregorianum.Year using (YearType; common; leap)
open import Data.Nat using (ℕ)

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Gregorianum.Data.Cursor.Properties as Cursor
open import Data.Product using (∃-syntax; _×_; _,_)

Month = Position 11

january : Month
january = mkPos first
february : Month
february = mkPos second
march : Month
march = mkPos third
april : Month
april = mkPos fourth
may : Month
may = mkPos fifth
june : Month
june = mkPos sixth
july : Month
july = mkPos seventh
august : Month
august = mkPos eighth
september : Month
september = mkPos ninth
october : Month
october = mkPos tenth
november : Month
november = mkPos eleventh
december : Month
december = mkPos twelfth

data _HasDays_ : YearType × Month → ℕ → Set where
  january-days         : ∀ {yt} →      (yt , january) HasDays 31
  february-common-days :           (common , february) HasDays 28
  february-leap-days   :             (leap , february) HasDays 29
  march-days           : ∀ {yt} →        (yt , march) HasDays 31
  april-days           : ∀ {yt} →        (yt , april) HasDays 30
  may-days             : ∀ {yt} →          (yt , may) HasDays 31
  june-days            : ∀ {yt} →         (yt , june) HasDays 30
  july-days            : ∀ {yt} →         (yt , july) HasDays 31
  august-days          : ∀ {yt} →       (yt , august) HasDays 31
  september-days       : ∀ {yt} →    (yt , september) HasDays 30
  october-days         : ∀ {yt} →      (yt , october) HasDays 31
  november-days        : ∀ {yt} →     (yt , november) HasDays 30
  december-days        : ∀ {yt} →     (yt , december) HasDays 31

days : (ytm : YearType × Month) → ∃[ ds ] ytm HasDays ds
days (yt , mkPos first) = 31 , january-days
days (yt , mkPos third) = 31 , march-days
days (yt , mkPos fourth) = 30 , april-days
days (yt , mkPos fifth) = 31 , may-days
days (yt , mkPos sixth) = 30 , june-days
days (yt , mkPos seventh) = 31 , july-days
days (yt , mkPos eighth) = 31 , august-days
days (yt , mkPos ninth) = 30 , september-days
days (yt , mkPos tenth) = 31 , october-days
days (yt , mkPos eleventh) = 30 , november-days
days (yt , mkPos twelfth) = 31 , december-days
days (yt , mkPos c@(suc×₁₂ _)) with Cursor.width≡acc+rem c
...                               | ()
days (common , mkPos second) = 28 , february-common-days
days (leap , mkPos second) = 29 , february-leap-days
