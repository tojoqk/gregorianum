module Gregorianum.Date.Properties where

open import Gregorianum.Date.Base

open import Gregorianum.Day.Base using (Day; 1st; suc; last)
open import Gregorianum.Day.Properties using (day-unique; rem≡0⇒cap≡acc)
import Gregorianum.YearMonth.Base as YM
open import Gregorianum.YearMonth.Properties using (next-year-month-unique; prev-year-month-unique; next-days-unique; prev-days-unique; next-year-month-exists; prev-year-month-exists)
open import Data.Product using (∃-syntax; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

tomorrow-unique : ∀ {d₁ d₂ d₃ : Date}
                → d₁ ⋖ d₂
                → d₁ ⋖ d₃
                → d₂ ≡ d₃
tomorrow-unique (step _) (step _) = refl
tomorrow-unique (step-last d₂ ym₁⋖ym₂) (step-last d₃ ym₁⋖ym₃)
                with day-unique d₂ d₃ | next-days-unique ym₁⋖ym₂ ym₁⋖ym₃
...                | refl | refl with next-year-month-unique ym₁⋖ym₂ ym₁⋖ym₃
...                                 | refl = refl

yesterday-unique : ∀ {d₁ d₂ d₃ : Date}
                 → d₁ ⋖ d₃
                 → d₂ ⋖ d₃
                 → d₁ ≡ d₂
yesterday-unique (step _) (step _) = refl
yesterday-unique (step-last d₁ ym₁⋖ym₃) (step-last d₂ ym₂⋖ym₃)
  with prev-days-unique ym₁⋖ym₃ ym₂⋖ym₃
...  | refl with day-unique d₁ d₂ | prev-year-month-unique ym₁⋖ym₃ ym₂⋖ym₃
...            | refl | refl = refl

tomorrow-exists : ∀ (d₁ : Date) → ∃[ d₂ ] (d₁ ⋖ d₂)
tomorrow-exists (year-month / day ⟨ _ , zero ⟩) with next-year-month-exists year-month | rem≡0⇒cap≡acc day
... | suc n , ym@(y YM./ m ⟨ has-days ⟩ ) , p | refl = (ym / 1st) , step-last day p
tomorrow-exists (year-month / day ⟨ _ , suc _ ⟩) = (year-month / suc day) , step day

yesterday-exists : ∀ (d₂ : Date) → ∃[ d₁ ] (d₁ ⋖ d₂)
yesterday-exists (year-month / 1st) with prev-year-month-exists year-month
... | suc n , ym , ym₁⋖ym₂ = (ym / last) , step-last last ym₁⋖ym₂
yesterday-exists (year-month / suc d) = (year-month / d) , step d
