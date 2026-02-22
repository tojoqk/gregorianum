module Gregorianum.Date.Properties where

open import Gregorianum.Date.Base

open import Gregorianum.Day.Base using (Day; 1st; suc; last)
open import Gregorianum.Day.Properties using (day-unique; rem≡0⇒cap≡acc)
import Gregorianum.YearMonth.Base as YM
open import Gregorianum.YearMonth.Properties using (next-year-month-unique; prev-year-month-unique; next-days-unique; prev-days-unique; next-year-month-exists; prev-year-month-exists)
open import Data.Product using (∃-syntax; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

next-day-unique : ∀ {d₁ d₂ d₃ : Date}
                → d₁ ⋖ d₂
                → d₁ ⋖ d₃
                → d₂ ≡ d₃
next-day-unique (step _) (step _) = refl
next-day-unique (step-month d₂ ym₁⋖ym₂) (step-month d₃ ym₁⋖ym₃)
                with day-unique d₂ d₃ | next-days-unique ym₁⋖ym₂ ym₁⋖ym₃
...                | refl | refl with next-year-month-unique ym₁⋖ym₂ ym₁⋖ym₃
...                                 | refl = refl

prev-day-unique : ∀ {d₁ d₂ d₃ : Date}
                 → d₁ ⋖ d₃
                 → d₂ ⋖ d₃
                 → d₁ ≡ d₂
prev-day-unique (step _) (step _) = refl
prev-day-unique (step-month d₁ ym₁⋖ym₃) (step-month d₂ ym₂⋖ym₃)
  with prev-days-unique ym₁⋖ym₃ ym₂⋖ym₃
...  | refl with day-unique d₁ d₂ | prev-year-month-unique ym₁⋖ym₃ ym₂⋖ym₃
...            | refl | refl = refl

next-day-exists : ∀ (d₁ : Date) → ∃[ d₂ ] (d₁ ⋖ d₂)
next-day-exists (year-month - day ⟨ _ , zero ⟩) with next-year-month-exists year-month | rem≡0⇒cap≡acc day
... | suc n , ym@(y YM.- m ⟨ has-days ⟩ ) , p | refl = (ym - 1st) , step-month day p
next-day-exists (year-month - day ⟨ _ , suc _ ⟩) = (year-month - suc day) , step day

prev-day-exists : ∀ (d₂ : Date) → ∃[ d₁ ] (d₁ ⋖ d₂)
prev-day-exists (year-month - 1st) with prev-year-month-exists year-month
... | suc n , ym , ym₁⋖ym₂ = (ym - last) , step-month last ym₁⋖ym₂
prev-day-exists (year-month - suc d) = (year-month - d) , step d
