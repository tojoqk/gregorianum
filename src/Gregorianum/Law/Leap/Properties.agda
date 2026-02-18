module Gregorianum.Law.Leap.Properties where

open import Gregorianum.Law.Leap
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc; _≟_; _%_; _*_)
open import Data.Nat.Properties as ℕProps
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Data.Nat.Divisibility using (_∣_; _∤_; n∣m⇒m%n≡0; m%n≡0⇒n∣m; divides)
open import Relation.Nullary.Negation using (¬_)

leap? : (n : ℕ) → Dec (Leap n)
leap? y with y % 4 ≟ 0
leap? y | yes y%4≡0 with y % 100 ≟ 0
leap? y | yes y%4≡0 | yes y%100≡0 with y % 400 ≟ 0
leap? y | yes y%4≡0 | yes y%100≡0 | yes y%400≡0 = yes (mkLeap (m%n≡0⇒n∣m y 4 y%4≡0) (quadricentennial (m%n≡0⇒n∣m y 400 y%400≡0)))
leap? y | yes y%4≡0 | yes y%100≡0 | no y%400≢0 = no λ { (mkLeap _ (non-centennial 100∤y)) → 100∤y (m%n≡0⇒n∣m y 100 y%100≡0)
                                                      ; (mkLeap _ (quadricentennial 400∣y)) → y%400≢0 (n∣m⇒m%n≡0 y 400 400∣y)}
leap? y | yes y%4≡0 | no y%100≢0 = yes (mkLeap (m%n≡0⇒n∣m y 4 y%4≡0) (non-centennial λ { 100∣y → y%100≢0 (n∣m⇒m%n≡0 y 100 100∣y)}))
leap? y | no y%4≢0 = no λ { (mkLeap quadrennial _) → y%4≢0 (n∣m⇒m%n≡0 y 4 quadrennial)}

private
  4∣n⇒4∤1+n : ∀ {n} → 4 ∣ n → 4 ∤ (suc n)
  4∣n⇒4∤1+n (divides zero refl) (divides zero ())
  4∣n⇒4∤1+n (divides zero refl) (divides (suc q2) ())
  4∣n⇒4∤1+n (divides (suc q₁) refl) (divides (suc q₂) eq₂) = 4∣n⇒4∤1+n (divides q₁ refl) (divides q₂ h)
    where
      h : suc (q₁ * 4) ≡ q₂ * 4
      h = ℕProps.suc-injective (ℕProps.suc-injective (ℕProps.suc-injective (ℕProps.suc-injective eq₂)))

  4∣1+n⇒4∤n : ∀ {n} → 4 ∣ (suc n) → 4 ∤ n
  4∣1+n⇒4∤n (divides zero ()) (divides zero refl)
  4∣1+n⇒4∤n (divides (suc _) ()) (divides zero refl)
  4∣1+n⇒4∤n (divides (suc q₁) eq₁) (divides (suc q₂) refl) = 4∣1+n⇒4∤n (divides q₁ h) (divides q₂ refl)
    where
      h : suc (q₂ * 4) ≡ q₁ * 4
      h = ℕProps.suc-injective (ℕProps.suc-injective (ℕProps.suc-injective (ℕProps.suc-injective eq₁)))

leap⇒¬leap+1  : ∀ {n} → Leap n → ¬ (Leap (suc n))
leap⇒¬leap+1 (mkLeap q₁ _) (mkLeap q₂ _) = 4∣n⇒4∤1+n q₁ q₂

leap+1⇒¬leap : ∀ {n} → Leap (suc n) → ¬ Leap n
leap+1⇒¬leap (mkLeap q₁ _) (mkLeap q₂ _) = 4∣1+n⇒4∤n q₁ q₂

¬leap1 : ¬ Leap 1
¬leap1 (mkLeap (divides zero ()) centennial)
¬leap1 (mkLeap (divides (suc quotient) ()) centennial)
