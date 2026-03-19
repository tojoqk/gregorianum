module Gregorianum.Month.Base where

open import Gregorianum.Year using (YearType; common; leap)
open import Data.Nat using (ℕ; _+_)

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

data _HasDayOrdinal_ : YearType × Month → ℕ → Set where
  january-ordinal          : ∀ {yt} →  (yt , january) HasDayOrdinal 0
  february-ordinal         : ∀ {yt} → (yt , february) HasDayOrdinal 31
  march-common-ordinal     :          (common , march) HasDayOrdinal 59
  april-common-ordinal     :          (common , april) HasDayOrdinal 90
  may-common-ordinal       :            (common , may) HasDayOrdinal 120
  june-common-ordinal      :           (common , june) HasDayOrdinal 151
  july-common-ordinal      :           (common , july) HasDayOrdinal 181
  august-common-ordinal    :         (common , august) HasDayOrdinal 212
  september-common-ordinal :      (common , september) HasDayOrdinal 243
  october-common-ordinal   :        (common , october) HasDayOrdinal 273
  november-common-ordinal  :       (common , november) HasDayOrdinal 304
  december-common-ordinal  :       (common , december) HasDayOrdinal 334
  march-leap-ordinal     :              (leap , march) HasDayOrdinal 60
  april-leap-ordinal     :              (leap , april) HasDayOrdinal 91
  may-leap-ordinal       :                (leap , may) HasDayOrdinal 121
  june-leap-ordinal      :               (leap , june) HasDayOrdinal 152
  july-leap-ordinal      :               (leap , july) HasDayOrdinal 182
  august-leap-ordinal    :             (leap , august) HasDayOrdinal 213
  september-leap-ordinal :          (leap , september) HasDayOrdinal 244
  october-leap-ordinal   :            (leap , october) HasDayOrdinal 274
  november-leap-ordinal  :           (leap , november) HasDayOrdinal 305
  december-leap-ordinal  :           (leap , december) HasDayOrdinal 335

dayOrdinal : (ytm : YearType × Month) → ∃[ n ] ytm HasDayOrdinal n
dayOrdinal (fst , mkPos first) = 0 , january-ordinal
dayOrdinal (fst , mkPos second) = 31 , february-ordinal
dayOrdinal (common , mkPos third) = 59 , march-common-ordinal
dayOrdinal (common , mkPos fourth) = 90 , april-common-ordinal
dayOrdinal (common , mkPos fifth) = 120 , may-common-ordinal
dayOrdinal (common , mkPos sixth) = 151 , june-common-ordinal
dayOrdinal (common , mkPos seventh) = 181 , july-common-ordinal
dayOrdinal (common , mkPos eighth) = 212 , august-common-ordinal
dayOrdinal (common , mkPos ninth) = 243 , september-common-ordinal
dayOrdinal (common , mkPos tenth) = 273 , october-common-ordinal
dayOrdinal (common , mkPos eleventh) = 304 , november-common-ordinal
dayOrdinal (common , mkPos twelfth) = 334 , december-common-ordinal
dayOrdinal (common , mkPos c@(suc×₁₂ _)) with Cursor.width≡acc+rem c
...                                        | ()
dayOrdinal (leap , mkPos third) = 60 , march-leap-ordinal
dayOrdinal (leap , mkPos fourth) = 91 , april-leap-ordinal
dayOrdinal (leap , mkPos fifth) = 121 , may-leap-ordinal
dayOrdinal (leap , mkPos sixth) = 152 , june-leap-ordinal
dayOrdinal (leap , mkPos seventh) = 182 , july-leap-ordinal
dayOrdinal (leap , mkPos eighth) = 213 , august-leap-ordinal
dayOrdinal (leap , mkPos ninth) = 244 , september-leap-ordinal
dayOrdinal (leap , mkPos tenth) = 274 , october-leap-ordinal
dayOrdinal (leap , mkPos eleventh) = 305 , november-leap-ordinal
dayOrdinal (leap , mkPos twelfth) = 335 , december-leap-ordinal
dayOrdinal (leap , mkPos c@(suc×₁₂ _)) with Cursor.width≡acc+rem c
...                                      | ()
