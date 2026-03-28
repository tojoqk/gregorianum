module Gregorianum.Date.Weekday where

open import Gregorianum.Date.Base using (Date; _HasOrdinal_; toOrdinal)
open import Gregorianum.Date.Properties using (ordinal-unique)

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; z≤n; s≤s)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (toℕ-injective; toℕ<n)
open import Data.Nat.DivMod as DivMod using (_%_; DivMod; _divMod_; _div_; result)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; toWitness)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)

record Weekday : Set where
  constructor [_]
  field
    index : Fin 7

private
  pattern saturday-fin = Fin.zero
  pattern sunday-fin = Fin.suc saturday-fin
  pattern monday-fin = Fin.suc sunday-fin
  pattern tuesday-fin = Fin.suc monday-fin
  pattern wednesday-fin = Fin.suc tuesday-fin
  pattern thursday-fin = Fin.suc wednesday-fin
  pattern friday-fin = Fin.suc thursday-fin

pattern saturday = [ saturday-fin ]
pattern sunday = [ sunday-fin ]
pattern monday = [ monday-fin ]
pattern tuesday = [ tuesday-fin ]
pattern wednesday = [ wednesday-fin ]
pattern thursday = [ thursday-fin ]
pattern friday = [ friday-fin ]

data _HasWeekday_ (d : Date) (w : Weekday) : Set where
  has-weekday : ∀ n → d HasOrdinal (Fin.toℕ (Weekday.index w) + n * 7) → d HasWeekday w

fromDate : (d : Date) → ∃[ w ] d HasWeekday w
fromDate d with toOrdinal d
... | n , p with n divMod 7
... | result q r eq = [ r ] , has-weekday q (subst (d HasOrdinal_) eq p)

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
weekday? d [ w ] with toOrdinal d
... | n , ho with n divMod 7
... | result q r eq with r Fin.≟ w
... | yes refl = yes (has-weekday q (subst (d HasOrdinal_) eq ho))
... | no ¬p = no h
  where
    h : ¬ (d HasWeekday [ w ])
    h (has-weekday n' ho') rewrite eq with ordinal-unique ho ho'
    ... | eq' = ¬p (toℕ-injective (m+n*p-injective 7 (Fin.toℕ r) q (Fin.toℕ w) n' (toℕ<n r) (toℕ<n w) eq'))

_⟨_⟩ : (d : Date) → (w : Weekday) → {True (weekday? d w)} → d HasWeekday w
_⟨_⟩ d w {t} = toWitness t
