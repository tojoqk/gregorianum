module Gregorianum.Day.Properties where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties as ℕProps
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Gregorianum.Day

day-unique : ∀ {cap acc rem}
           → (d₁ d₂ : Day cap acc rem)
           → d₁ ≡ d₂
day-unique {acc = zero} 1st 1st = refl
day-unique {acc = suc i} (suc d₁) (suc d₂) = cong suc (day-unique d₁ d₂)

cap≡acc+rem : ∀ {cap acc rem} → Day cap acc rem → cap ≡ acc + rem
cap≡acc+rem 1st = refl
cap≡acc+rem {rem = rem} (suc d) with cap≡acc+rem d
...                                | refl = ℕProps.+-suc _ rem

acc≡0⇒cap≡rem : ∀ {cap rem}
              → Day cap 0 rem
              → cap ≡ rem
acc≡0⇒cap≡rem 1st = refl

rem≡0⇒cap≡acc : ∀ {cap acc}
              → Day cap acc 0
              → cap ≡ acc
rem≡0⇒cap≡acc d with cap≡acc+rem d
...                 | refl = ℕProps.+-identityʳ _
