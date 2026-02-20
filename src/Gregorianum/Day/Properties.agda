module Gregorianum.Day.Properties where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties as ℕProps
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Gregorianum.Day

day-unique : ∀ {n i j}
           → (d₁ d₂ : Day n i j)
           → d₁ ≡ d₂
day-unique {n} {zero} {j} 1st 1st = refl
day-unique {n} {suc i} {j} (suc d₁) (suc d₂) = cong suc (day-unique d₁ d₂)

day-n≡i+j : ∀ {n i j} → Day n i j → n ≡ i + j
day-n≡i+j 1st = refl
day-n≡i+j {n} {i} {j} (suc d) with day-n≡i+j d
...                              | refl = ℕProps.+-suc _ j

1st-n≡i : ∀ {n i}
        → Day n i 0
        → n ≡ i
1st-n≡i d with day-n≡i+j d
...          | refl = ℕProps.+-identityʳ _
