module Gregorianum.Date.Path where

open import Gregorianum.Date.Base
  using (Date; _HasOrdinal_; toOrdinal; nextDate; isSuccessor?; prevDate)
open import Gregorianum.Date.Properties
  using (date-unique; next-date-ordinal; prev-date-ordinal; suc-ordinal-is-successor; ordinal-unique)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; s≤s; _≟_; <-cmp)
open import Data.Nat.Properties using (+-assoc; +-comm; +-cancelˡ-≡; +-cancelʳ-≡; m∸n+n≡m)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no; True; toWitness)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

record _─[_]→_ (d₁ : Date) (n : ℕ) (d₂ : Date) : Set where
  constructor ⟨_,_⟩
  field
    {ord} : ℕ
    start : d₁ HasOrdinal ord
    end : d₂ HasOrdinal (n + ord)

pattern ⟨_,_⟩[_] start end ord = record { ord = ord; start = start; end = end }

open import Gregorianum.Relation.Path Date _─[_]→_ using (IsPath; IsLinear; Tri; tri≡; tri←; tri→)

addDays : ∀ d₁ n → ∃[ d₂ ] d₁ ─[ n ]→ d₂
addDays d₁ zero = let (_ , ho) = toOrdinal d₁ in d₁ , ⟨ ho , ho ⟩
addDays d₁ (suc n) with addDays d₁ n
... | d₂' , ⟨ ho₁ , ho₂' ⟩ with nextDate d₂'
... | d₂ , d₂'⋖d₂ = d₂ , ⟨ ho₁ , next-date-ordinal d₂'⋖d₂ ho₂' ⟩

subtractDays? : ∀ d₂ n → Dec (∃[ d₁ ] d₁ ─[ n ]→ d₂)
subtractDays? d₂ zero = let (_ , ho) = toOrdinal d₂ in yes (d₂ , ⟨ ho , ho ⟩)
subtractDays? d₂ (suc n) with isSuccessor? d₂
... | yes isSuc with prevDate d₂ isSuc
... | d₂' , d₂'⋖d₂ with subtractDays? d₂' n
... | yes (d₁ , ⟨ ho₁ , ho₂' ⟩) = yes (d₁ , ⟨ ho₁ , next-date-ordinal d₂'⋖d₂ ho₂' ⟩)
... | no ¬p = no h
  where
    h : ¬ (∃[ d₁ ] d₁ ─[ suc n ]→ d₂)
    h (d₁ , ⟨ ho₁ , ho₂ ⟩) = ¬p (d₁ , ⟨ ho₁ , prev-date-ordinal d₂'⋖d₂ ho₂ ⟩)
subtractDays? d₂ (suc n) | no ¬isSuc = no h
  where
    h : ¬ (∃[ d₁ ] d₁ ─[ suc n ]→ d₂)
    h (d₁ , ⟨ ho₁ , ho₂ ⟩) = ¬isSuc (suc-ordinal-is-successor ho₂)

identity : ∀ {x y} → x ≡ y → x ─[ zero ]→ y
identity {x} refl = let (_ , ho) = toOrdinal x in ⟨ ho , ho ⟩

identity⁻¹ : ∀ {x y} → x ─[ zero ]→ y → x ≡ y
identity⁻¹ ⟨ ho₁ , ho₂ ⟩ = date-unique ho₁ ho₂

trans : ∀ {x y z len₁ len₂}
      → x ─[ len₁ ]→ y
      → y ─[ len₂ ]→ z
      → x ─[ len₁ + len₂ ]→ z
trans {x} {y} {z = z} {len₁} {len₂} ⟨ xho₁ , yho₁ ⟩[ ord ] ⟨ yho₂ , zho₂ ⟩ with ordinal-unique yho₁ yho₂
... | refl = ⟨ xho₁ , (subst (z HasOrdinal_) (Eq.trans (sym (+-assoc len₂ len₁ _)) (cong (_+ ord) (+-comm len₂ len₁))) zho₂) ⟩

split : ∀ {x z} → (m n : ℕ) → x ─[ m + n ]→ z → ∃[ y ] (x ─[ m ]→ y × y ─[ n ]→ z)
split {x} {z} m n ⟨ xho , zho ⟩ with addDays x m
... | (y , ⟨ xho' , yho₁ ⟩[ ord ]) with addDays y n
... | (z' , ⟨ yho₂ , zho' ⟩) with ordinal-unique xho xho' | ordinal-unique yho₁ yho₂
... | refl | refl = y , (⟨ xho' , yho₂ ⟩ , ⟨ yho₂ , (subst (z HasOrdinal_) eq zho) ⟩)
  where
    eq : m + n + ord ≡ n + (m + ord)
    eq = begin
           m + n + ord
         ≡⟨ cong (_+ ord) (+-comm m n) ⟩
           n + m + ord
         ≡⟨ +-assoc n m ord ⟩
           n + (m + ord)
         ∎
      where open ≡-Reasoning

isPath : IsPath
isPath = record { identity = identity
                ; identity⁻¹ = identity⁻¹
                ; trans = trans
                ; split = split }

uniqueˡ : ∀ {x y z len}
        → x ─[ len ]→ z
        → y ─[ len ]→ z
        → x ≡ y
uniqueˡ {len = len} ⟨ xho , zho₁ ⟩[ ord₁ ] ⟨ yho , zho₂ ⟩[ ord₂ ] with ordinal-unique zho₁ zho₂
... | eq with +-cancelˡ-≡ len ord₁ ord₂ eq
... | refl = date-unique xho yho

uniqueʳ : ∀ {x y z len}
        → x ─[ len ]→ y
        → x ─[ len ]→ z
        → y ≡ z
uniqueʳ {len = len} ⟨ xho₁ , yho ⟩[ ord₁ ] ⟨ xho₂ , zho ⟩[ ord₂ ] with ordinal-unique xho₁ xho₂
... | refl = date-unique yho zho

acyclic : ∀ {x n} → x ─[ n ]→ x → n ≡ 0
acyclic {_} {n} ⟨ ho₁ , ho₂ ⟩[ ord ] with ordinal-unique ho₁ ho₂
... | h = sym (+-cancelʳ-≡ ord 0 n h)

compare : ∀ d₁ d₂ → Tri d₁ d₂
compare d₁ d₂ with toOrdinal d₁ | toOrdinal d₂
compare d₁ d₂ | n₁ , ho₁ | n₂ , ho₂ with <-cmp n₁ n₂
compare d₁ d₂ | n₁ , ho₁ | n₂ , ho₂ | tri≈ ¬a refl ¬c = tri≡ (date-unique ho₁ ho₂)
compare d₁ d₂ | n₁ , ho₁ | (suc n₂) , ho₂ | tri< (s≤s a) ¬b ¬c = tri→ (n₂ ∸ n₁) ⟨ ho₁ , subst (d₂ HasOrdinal_) (cong suc (sym (m∸n+n≡m a))) ho₂ ⟩
compare d₁ d₂ | (suc n₁) , ho₁ | n₂ , ho₂ | tri> ¬a ¬b (s≤s c) = tri← (n₁ ∸ n₂) ⟨ ho₂ , subst (d₁ HasOrdinal_) (cong suc (sym (m∸n+n≡m c))) ho₁ ⟩

total = compare

isLinear : IsLinear
isLinear = record
             { isPath = isPath
             ; uniqueˡ = uniqueˡ
             ; uniqueʳ = uniqueʳ
             ; acyclic = acyclic
             ; total = total
             }

private
  ¬circle : ∀ {x n} → ¬ (x ─[ suc n ]→ x)
  ¬circle x with acyclic x
  ... | ()

  uniqueᶜ : ∀ {d₁ d₂ m n} → d₁ ─[ m ]→ d₂ →  d₁ ─[ n ]→ d₂ → m ≡ n
  uniqueᶜ {m = m} {n = n} ⟨ ho₁ , ho₂ ⟩[ ord ] ⟨ ho₁' , ho₂' ⟩ with ordinal-unique ho₁ ho₁'
  ... | refl = +-cancelʳ-≡ ord m n (ordinal-unique ho₂ ho₂')

_─[_]→?_ : ∀ d₁ n d₂ → Dec (d₁ ─[ n ]→ d₂)
d₁ ─[ n ]→? d₂ with compare d₁ d₂
(d₁ ─[ zero ]→? d₂) | tri≡ eq = yes (identity eq)
(d₁ ─[ suc n ]→? d₂) | tri≡ refl = no ¬circle
d₁ ─[ n ]→? d₂ | tri→ k d₁→d₂ with n ≟ suc k
... | yes refl = yes d₁→d₂
... | no ¬eq = no λ d₁→d₂' → ¬eq (uniqueᶜ d₁→d₂' d₁→d₂)
d₁ ─[ n ]→? d₂ | tri← _ d₁→d₂ = no λ d₂→d₁ → ¬circle (trans d₁→d₂ d₂→d₁)

_─⟨_⟩→_ : ∀ d₁ n d₂ → {True (d₁ ─[ n ]→? d₂)} → d₁ ─[ n ]→ d₂
_─⟨_⟩→_ _ _ _ {t} = toWitness t
