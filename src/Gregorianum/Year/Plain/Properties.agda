module Gregorianum.Year.Plain.Properties where

open import Gregorianum.Year.Plain.Base using (_HasPlain_; plain)

open import Gregorianum.Year.Base using (year-first; _⋖_; IsSuc; _×₄₀₀+_×₁₀₀+_×₄+_; suc₁; suc₄; suc₁₀₀; suc₄₀₀; prev; step₁; step₄; step₁₀₀; step₄₀₀)
open import Gregorianum.Year.Properties hiding (year-unique)
open import Gregorianum.Data.Cursor using (zero; suc; first)
open import Gregorianum.Data.Cursor.Position using (mkPos)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

next-plain : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₁ HasPlain n → y₂ HasPlain (suc n)
next-plain step₁ plain = plain
next-plain step₄ plain = plain
next-plain step₁₀₀ plain = plain
next-plain step₄₀₀ plain = plain

prev-plain : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₂ HasPlain (suc n) → y₁ HasPlain n
prev-plain step₁ plain = plain
prev-plain step₄ plain = plain
prev-plain step₁₀₀ plain = plain
prev-plain step₄₀₀ plain = plain

suc-plain-IsSuc : ∀ {y n} → y HasPlain (suc n) → IsSuc y
suc-plain-IsSuc {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)} p = suc₁
suc-plain-IsSuc {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} p = suc₄
suc-plain-IsSuc {q ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} p = suc₁₀₀
suc-plain-IsSuc {suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} p = suc₄₀₀

year-unique : ∀ {y₁ y₂ n} → y₁ HasPlain n → y₂ HasPlain n → y₁ ≡ y₂
year-unique {y₁} {y₂} {ℕ.suc n} p q with prev y₁ (suc-plain-IsSuc p) | prev y₂ (suc-plain-IsSuc q)
... | y₁' , y₁'⋖y₁ | y₂' , y₂'⋖y₂ with year-unique {y₁'} {y₂'} {n} (prev-plain y₁'⋖y₁ p) (prev-plain y₂'⋖y₂ q)
... | refl = next-unique y₁'⋖y₁ y₂'⋖y₂
year-unique {year-first} {year-first} {ℕ.zero} plain plain = refl
