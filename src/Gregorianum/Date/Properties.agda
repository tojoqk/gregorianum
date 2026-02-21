module Gregorianum.Date.Properties where

open import Data.Product using (∃-syntax; _,_)
open import Gregorianum.Day using (Day; 1st; suc)
open import Gregorianum.YearMonth using (_/_⟨_⟩)
open import Gregorianum.Date using (Date; _⋖_; _/_; step; step-last)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Gregorianum.Day.Properties
open import Gregorianum.YearMonth.Properties using (next-year-month-unique; next-days-unique; next-year-month-exists)

tomorrow-unique : ∀ {d₁ d₂ d₃ : Date}
                → d₁ ⋖ d₂
                → d₁ ⋖ d₃
                → d₂ ≡ d₃
tomorrow-unique (step _) (step _) = refl
tomorrow-unique (step-last d₂ ym₁⋖ym₂) (step-last d₃ ym₁⋖ym₃)
                with day-unique d₂ d₃ | next-days-unique ym₁⋖ym₂ ym₁⋖ym₃
...                | refl | refl with next-year-month-unique ym₁⋖ym₂ ym₁⋖ym₃
...                                 | refl = refl


tomorrow-exists : ∀ (d₁ : Date) → ∃[ d₂ ] (d₁ ⋖ d₂ )
tomorrow-exists (_/_ year-month {rem = zero} day) with next-year-month-exists year-month | rem≡0⇒cap≡acc day
... | suc n , ym@(y / m ⟨ has-days ⟩ ) , p | refl = (ym / 1st) , step-last day p
tomorrow-exists (_/_ year-month {rem = suc _} day) = (year-month / suc day) , step day
