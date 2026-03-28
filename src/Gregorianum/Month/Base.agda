module Gregorianum.Month.Base where

open import Gregorianum.Year using (YearType; common; leap)
open import Data.Nat using (ℕ; _+_)

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Gregorianum.Data.Cursor.Properties as Cursor
open import Data.Product using (∃-syntax; _×_; _,_)

record Month : Set where
  constructor [_]
  field
    position : Position 11

pattern january = [ mkPos first ]
pattern february = [ mkPos second ]
pattern march = [ mkPos third ]
pattern april = [ mkPos fourth ]
pattern may = [ mkPos fifth ]
pattern june = [ mkPos sixth ]
pattern july = [ mkPos seventh ]
pattern august = [ mkPos eighth ]
pattern september = [ mkPos ninth ]
pattern october = [ mkPos tenth ]
pattern november = [ mkPos eleventh ]
pattern december = [ mkPos twelfth ]

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
days (yt , january) = 31 , january-days
days (yt , march) = 31 , march-days
days (yt , april) = 30 , april-days
days (yt , may) = 31 , may-days
days (yt , june) = 30 , june-days
days (yt , july) = 31 , july-days
days (yt , august) = 31 , august-days
days (yt , september) = 30 , september-days
days (yt , october) = 31 , october-days
days (yt , november) = 30 , november-days
days (yt , december) = 31 , december-days
days (yt , [ mkPos c@(suc¹² _) ]) with Cursor.width≡acc+rem c
...                               | ()
days (common , february) = 28 , february-common-days
days (leap , february) = 29 , february-leap-days

data _HasDayWeight_ : YearType × Month → ℕ → Set where
  january-weight          : ∀ {yt} →  (yt , january) HasDayWeight 0
  february-weight         : ∀ {yt} → (yt , february) HasDayWeight 31
  march-common-weight     :          (common , march) HasDayWeight 59
  april-common-weight     :          (common , april) HasDayWeight 90
  may-common-weight       :            (common , may) HasDayWeight 120
  june-common-weight      :           (common , june) HasDayWeight 151
  july-common-weight      :           (common , july) HasDayWeight 181
  august-common-weight    :         (common , august) HasDayWeight 212
  september-common-weight :      (common , september) HasDayWeight 243
  october-common-weight   :        (common , october) HasDayWeight 273
  november-common-weight  :       (common , november) HasDayWeight 304
  december-common-weight  :       (common , december) HasDayWeight 334
  march-leap-weight     :              (leap , march) HasDayWeight 60
  april-leap-weight     :              (leap , april) HasDayWeight 91
  may-leap-weight       :                (leap , may) HasDayWeight 121
  june-leap-weight      :               (leap , june) HasDayWeight 152
  july-leap-weight      :               (leap , july) HasDayWeight 182
  august-leap-weight    :             (leap , august) HasDayWeight 213
  september-leap-weight :          (leap , september) HasDayWeight 244
  october-leap-weight   :            (leap , october) HasDayWeight 274
  november-leap-weight  :           (leap , november) HasDayWeight 305
  december-leap-weight  :           (leap , december) HasDayWeight 335

dayWeight : (ytm : YearType × Month) → ∃[ n ] ytm HasDayWeight n
dayWeight (fst , january) = 0 , january-weight
dayWeight (fst , february) = 31 , february-weight
dayWeight (common , march) = 59 , march-common-weight
dayWeight (common , april) = 90 , april-common-weight
dayWeight (common , may) = 120 , may-common-weight
dayWeight (common , june) = 151 , june-common-weight
dayWeight (common , july) = 181 , july-common-weight
dayWeight (common , august) = 212 , august-common-weight
dayWeight (common , september) = 243 , september-common-weight
dayWeight (common , october) = 273 , october-common-weight
dayWeight (common , november) = 304 , november-common-weight
dayWeight (common , december) = 334 , december-common-weight
dayWeight (common , [ mkPos c@(suc¹² _) ]) with Cursor.width≡acc+rem c
...                                        | ()
dayWeight (leap , march) = 60 , march-leap-weight
dayWeight (leap , april) = 91 , april-leap-weight
dayWeight (leap , may) = 121 , may-leap-weight
dayWeight (leap , june) = 152 , june-leap-weight
dayWeight (leap , july) = 182 , july-leap-weight
dayWeight (leap , august) = 213 , august-leap-weight
dayWeight (leap , september) = 244 , september-leap-weight
dayWeight (leap , october) = 274 , october-leap-weight
dayWeight (leap , november) = 305 , november-leap-weight
dayWeight (leap , december) = 335 , december-leap-weight
dayWeight (leap , [ mkPos c@(suc¹² _) ]) with Cursor.width≡acc+rem c
...                                      | ()
