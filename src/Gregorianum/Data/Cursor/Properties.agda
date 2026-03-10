module Gregorianum.Data.Cursor.Properties where

open import Gregorianum.Data.Cursor.Base

open import Data.Nat using (zero; suc; _+_)
open import Data.Nat.Properties as ℕProps
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

unique : ∀ {width acc rem}
       → (c₁ c₂ : Cursor width acc rem)
       → c₁ ≡ c₂
unique {acc = zero} zero zero = refl
unique {acc = suc _} (suc c₁) (suc c₂) = cong suc (unique c₁ c₂)

width≡acc+rem : ∀ {width acc rem} → Cursor width acc rem → width ≡ acc + rem
width≡acc+rem zero = refl
width≡acc+rem {rem = rem} (suc c) with width≡acc+rem c
...                                  | refl = ℕProps.+-suc _ rem

acc≡0⇒width≡rem : ∀ {width rem}
                → Cursor width 0 rem
                → width ≡ rem
acc≡0⇒width≡rem zero = refl

rem≡0⇒width≡acc : ∀ {width acc}
                → Cursor width acc 0
                → width ≡ acc
rem≡0⇒width≡acc c with width≡acc+rem c
...                   | refl = ℕProps.+-identityʳ _
