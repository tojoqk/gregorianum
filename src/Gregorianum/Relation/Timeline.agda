module Gregorianum.Relation.Timeline (A : Set) where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; <-cmp; s≤s; _≟_)
open import Data.Nat.Properties using (+-assoc; +-comm; +-cancelˡ-≡; +-cancelʳ-≡; m∸n+n≡m)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open import Relation.Nullary.Negation using (¬_)

record IsTimeline : Set₁ where
  field
    _HasOrdinal_ : A → ℕ → Set
    toOrdinal : (x : A) → ∃[ n ] x HasOrdinal n
    unique : ∀ {x y n} → x HasOrdinal n → y HasOrdinal n → x ≡ y
    ordinal-unique : ∀ {x n₁ n₂} → x HasOrdinal n₁ → x HasOrdinal n₂ → n₁ ≡ n₂
    shift : ∀ {n} → (x : A) → (k : ℕ) → x HasOrdinal n → ∃[ y ] y HasOrdinal (k + n)

module Path (isTimeline : IsTimeline) where
  open IsTimeline isTimeline

  record _─[_]→_ (d₁ : A) (n : ℕ) (d₂ : A) : Set where
    constructor ⟨_,_⟩
    field
      {ord} : ℕ
      start : d₁ HasOrdinal ord
      end : d₂ HasOrdinal (n + ord)

  pattern ⟨_,_⟩[_] start end ord = record { ord = ord; start = start; end = end }

  open import Gregorianum.Relation.Path A _─[_]→_ using (IsPath)

  identity : ∀ {x y} → x ≡ y → x ─[ zero ]→ y
  identity {x} refl = let (_ , ho) = toOrdinal x in ⟨ ho , ho ⟩

  identity⁻¹ : ∀ {x y} → x ─[ zero ]→ y → x ≡ y
  identity⁻¹ ⟨ s , e ⟩ = unique s e

  trans : ∀ {x y z n₁ n₂}
        → x ─[ n₁ ]→ y
        → y ─[ n₂ ]→ z
        → x ─[ n₁ + n₂ ]→ z
  trans {x} {y} {z} {n₁} {n₂} ⟨ s₁ , e₁ ⟩[ ord ] ⟨ s₂ , e₂ ⟩ with ordinal-unique e₁ s₂
  ... | refl = ⟨ s₁ , subst (z HasOrdinal_) eq e₂ ⟩
    where
      eq : n₂ + (n₁ + ord) ≡ n₁ + n₂ + ord
      eq = begin
            n₂ +(n₁ + ord)
          ≡⟨ sym (+-assoc n₂ n₁ ord) ⟩
            n₂ + n₁ + ord
          ≡⟨ cong (_+ ord) (+-comm n₂ n₁) ⟩
            n₁ + n₂ + ord
          ∎
        where open ≡-Reasoning

  split : ∀ {x z} → (m n : ℕ) → x ─[ m + n ]→ z → ∃[ y ] (x ─[ m ]→ y × y ─[ n ]→ z)
  split {x} {z} m n ⟨ s , e ⟩[ ord ] with shift x m s
  ... | y , yho with shift y n yho
  ... | z' , zho' with unique zho' h
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
      h : z HasOrdinal (n + (m + ord))
      h =  subst (z HasOrdinal_) eq e
  ... | refl = y , ⟨ s , yho ⟩ , ⟨ yho , zho' ⟩

  isPath : IsPath
  isPath = record { identity = identity
                  ; identity⁻¹ = identity⁻¹
                  ; trans = trans
                  ; split = split }

  open import Gregorianum.Relation.Path A _─[_]→_ using (IsLinear)
  open import Gregorianum.Relation.Path A _─[_]→_ using (Tri; tri≡; tri←; tri→) public

  uniqueˡ : ∀ {x y z n} → x ─[ n ]→ z → y ─[ n ]→ z → x ≡ y
  uniqueˡ {n = n} ⟨ s₁ , e₁ ⟩ ⟨ s₂ , e₂ ⟩ with ordinal-unique e₁ e₂
  ... | eq rewrite +-cancelˡ-≡ n _ _ eq = unique s₁ s₂

  uniqueʳ : ∀ {x y z n} → x ─[ n ]→ y → x ─[ n ]→ z → y ≡ z
  uniqueʳ {n = n} ⟨ s₁ , e₁ ⟩ ⟨ s₂ , e₂ ⟩ with ordinal-unique s₁ s₂
  ... | refl = unique e₁ e₂

  acyclic : ∀ {x n} → x ─[ n ]→ x → n ≡ 0
  acyclic ⟨ s , e ⟩[ ord ] = +-cancelʳ-≡ ord _ _ (ordinal-unique e s)

  private
    ¬circle : ∀ {x n} → ¬ (x ─[ suc n ]→ x)
    ¬circle x with acyclic x
    ... | ()

  uniqueᶜ : ∀ {x y m n} → x ─[ m ]→ y →  x ─[ n ]→ y → m ≡ n
  uniqueᶜ {m = m} {n = n} ⟨ ho₁ , ho₂ ⟩[ ord ] ⟨ ho₁' , ho₂' ⟩ with ordinal-unique ho₁ ho₁'
  ... | refl = +-cancelʳ-≡ ord m n (ordinal-unique ho₂ ho₂')

  compare : ∀ x y → Tri x y
  compare x y with toOrdinal x | toOrdinal y
  compare x y | n₁ , ho₁ | n₂ , ho₂ with <-cmp n₁ n₂
  compare x y | n₁ , ho₁ | n₂ , ho₂ | tri≈ ¬a refl ¬c = tri≡ (unique ho₁ ho₂)
  compare x y | n₁ , ho₁ | (suc n₂) , ho₂ | tri< (s≤s a) ¬b ¬c = tri→ (n₂ ∸ n₁) ⟨ ho₁ , subst (y HasOrdinal_) (cong suc (sym (m∸n+n≡m a))) ho₂ ⟩
  compare x y | (suc n₁) , ho₁ | n₂ , ho₂ | tri> ¬a ¬b (s≤s c) = tri← (n₁ ∸ n₂) ⟨ ho₂ , subst (x HasOrdinal_) (cong suc (sym (m∸n+n≡m c))) ho₁ ⟩

  total : ∀ x y → Tri x y
  total = compare

  isLinear : IsLinear
  isLinear = record
              { isPath = isPath
              ; uniqueˡ = uniqueˡ
              ; uniqueᶜ = uniqueᶜ
              ; uniqueʳ = uniqueʳ
              ; acyclic = acyclic
              ; total = total
              }

  _─[_]→?_ : ∀ x n y → Dec (x ─[ n ]→ y)
  x ─[ n ]→? y with compare x y
  (x ─[ zero ]→? y) | tri≡ eq = yes (identity eq)
  (x ─[ suc n ]→? y) | tri≡ refl = no ¬circle
  x ─[ n ]→? y | tri→ k x→y with n ≟ suc k
  ... | yes refl = yes x→y
  ... | no ¬eq = no λ x→y' → ¬eq (uniqueᶜ x→y' x→y)
  x ─[ n ]→? y | tri← _ x→y = no λ y→x → ¬circle (trans x→y y→x)
