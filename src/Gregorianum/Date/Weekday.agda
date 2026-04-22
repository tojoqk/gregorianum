module Gregorianum.Date.Weekday where

open import Gregorianum.Date.Base using (Date; _HasOrdinal_; toOrdinal)
open import Gregorianum.Date.Properties using (ordinal-unique)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; z≤n; s≤s)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (toℕ-injective; toℕ<n)
open import Data.Nat.DivMod as DivMod using (_%_; DivMod; _divMod_; _div_; result)
open import Data.Product using (∃-syntax; _,_; proj₁)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; toWitness)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open import Function using (_∘_; _↔_)

data Weekday : Set where
  sunday : Weekday
  monday : Weekday
  tuesday : Weekday
  wednesday : Weekday
  thursday : Weekday
  friday : Weekday
  saturday : Weekday

private
  pattern first = Fin.zero
  pattern second = Fin.suc first
  pattern third = Fin.suc second
  pattern fourth = Fin.suc third
  pattern fifth = Fin.suc fourth
  pattern sixth = Fin.suc fifth
  pattern seventh = Fin.suc sixth

data _HasFin_ : Weekday → Fin 7 → Set where
  saturday-fin : saturday HasFin first
  sunday-fin : sunday HasFin second
  monday-fin : monday HasFin third
  tuesday-fin : tuesday HasFin fourth
  wednesday-fin : wednesday HasFin fifth
  thursday-fin : thursday HasFin sixth
  friday-fin : friday HasFin seventh

toFin : (w : Weekday) → ∃[ i ] w HasFin i
toFin sunday = second , sunday-fin
toFin monday = third , monday-fin
toFin tuesday = fourth , tuesday-fin
toFin wednesday = fifth , wednesday-fin
toFin thursday = sixth , thursday-fin
toFin friday = seventh , friday-fin
toFin saturday = first , saturday-fin

fromFin : (i : Fin 7) → ∃[ w ] w HasFin i
fromFin first = saturday , saturday-fin
fromFin second = sunday , sunday-fin
fromFin third = monday , monday-fin
fromFin fourth = tuesday , tuesday-fin
fromFin fifth = wednesday , wednesday-fin
fromFin sixth = thursday , thursday-fin
fromFin seventh = friday , friday-fin

weekday-unique : ∀ {w₁ w₂ i} → w₁ HasFin i → w₂ HasFin i → w₁ ≡ w₂
weekday-unique saturday-fin saturday-fin = refl
weekday-unique sunday-fin sunday-fin = refl
weekday-unique monday-fin monday-fin = refl
weekday-unique tuesday-fin tuesday-fin = refl
weekday-unique wednesday-fin wednesday-fin = refl
weekday-unique thursday-fin thursday-fin = refl
weekday-unique friday-fin friday-fin = refl

fin-unique : ∀ {w i₁ i₂} → w HasFin i₁ → w HasFin i₂ → i₁ ≡ i₂
fin-unique saturday-fin saturday-fin = refl
fin-unique sunday-fin sunday-fin = refl
fin-unique monday-fin monday-fin = refl
fin-unique tuesday-fin tuesday-fin = refl
fin-unique wednesday-fin wednesday-fin = refl
fin-unique thursday-fin thursday-fin = refl
fin-unique friday-fin friday-fin = refl

isoToFin : Weekday ↔ Fin 7
isoToFin = record
            { to = proj₁ ∘ toFin
            ; from = proj₁ ∘ fromFin
            ; to-cong = λ { refl → refl }
            ; from-cong = λ { refl → refl }
            ; inverse = (λ { refl → invˡ}) , λ { refl → invʳ}
            }
  where
    invˡ : ∀ {i} → proj₁ (toFin (proj₁ (fromFin i))) ≡ i
    invˡ {i} with fromFin i
    ... | w , p₁ with toFin w
    ... | i' , p₂ = fin-unique p₂ p₁
    invʳ : ∀ {w} → proj₁ (fromFin (proj₁ (toFin w))) ≡ w
    invʳ {w} with toFin w
    ... | i , p₁ with fromFin i
    ... | w' , p₂ = weekday-unique p₂ p₁

data _HasWeekday_ (d : Date) (w : Weekday) : Set where
  weekday : ∀ {i} n → w HasFin i →  d HasOrdinal (Fin.toℕ i + n * 7) → d HasWeekday w

fromDate : (d : Date) → ∃[ w ] d HasWeekday w
fromDate d with toOrdinal d
... | n , p with n divMod 7
... | result q r eq with fromFin r -- [ r ] , weekday q (subst (d HasOrdinal_) eq p)
... | w , hf = w , (weekday q hf (subst (d HasOrdinal_) eq p))

private
  m+n*p-injective : ∀ (p m n m' n' : ℕ)
                  → m < p
                  → m' < p
                  → m + n * p ≡ m' + n' * p
                  → m ≡ m'
  m+n*p-injective p@(suc _) m n m' n' m<p@(s≤s _) m'<p@(s≤s _) eq with DivMod.m<n⇒m%n≡m m<p | DivMod.m<n⇒m%n≡m m'<p
  ... | m%p≡m | m'%p≡m' =
      begin
        m
      ≡⟨ sym m%p≡m ⟩
        m % p
      ≡⟨ sym (DivMod.[m+kn]%n≡m%n m n p) ⟩
        (m + n * p) % p
      ≡⟨ cong (_% p) eq ⟩
        (m' + n' * p) % p
      ≡⟨ DivMod.[m+kn]%n≡m%n m' n' p ⟩
        m' % p
      ≡⟨ m'%p≡m' ⟩
        m'
      ∎
    where open ≡-Reasoning

weekday? : (d : Date) → (w : Weekday) → Dec (d HasWeekday w)
weekday? d w with toFin w
... | i , hf with toOrdinal d
... | n , ho with n divMod 7
... | result q r eq with r Fin.≟ i
... | yes refl = yes (weekday q hf (subst (d HasOrdinal_) eq ho))
... | no ¬p = no h
  where
    h : ¬ (d HasWeekday w)
    h (weekday n' hf' ho') with fin-unique hf hf'
    ... | refl rewrite eq with ordinal-unique ho ho'
    ... | eq' = ¬p (toℕ-injective (m+n*p-injective 7 (Fin.toℕ r) q (Fin.toℕ i) n' (toℕ<n r) (toℕ<n i) eq'))

_has-weekday_ : (d : Date) → (w : Weekday) → {True (weekday? d w)} → d HasWeekday w
_has-weekday_ d w {t} = toWitness t
