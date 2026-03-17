module Gregorianum.Year.Plain.Properties where

open import Gregorianum.Year.Plain.Base

open import Gregorianum.Year.Base
open import Gregorianum.Year.Properties hiding (year-unique)
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

next-year-plain : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₁ HasPlain n → y₂ HasPlain (suc n)
next-year-plain step plain = plain
next-year-plain step₄ plain = plain
next-year-plain step₁₀₀ plain = plain
next-year-plain step₄₀₀ plain = plain

prev-year-plain : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₂ HasPlain (suc n) → y₁ HasPlain n
prev-year-plain step plain = plain
prev-year-plain step₄ plain = plain
prev-year-plain step₁₀₀ plain = plain
prev-year-plain step₄₀₀ plain = plain

suc-plain-is-successor : ∀ {y n} → y HasPlain (suc n) → IsSuccessor y
suc-plain-is-successor {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)} p = suc₁
suc-plain-is-successor {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} p = suc₄
suc-plain-is-successor {q ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} p = suc₁₀₀
suc-plain-is-successor {suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} p = suc₄₀₀

year-unique : ∀ {y₁ y₂ n} → y₁ HasPlain n → y₂ HasPlain n → y₁ ≡ y₂
year-unique {y₁} {y₂} {ℕ.suc n} p q with prevYear y₁ (suc-plain-is-successor p) | prevYear y₂ (suc-plain-is-successor q)
... | y₁' , y₁'⋖y₁ | y₂' , y₂'⋖y₂ with year-unique {y₁'} {y₂'} {n} (prev-year-plain y₁'⋖y₁ p) (prev-year-plain y₂'⋖y₂ q)
... | refl = next-year-unique y₁'⋖y₁ y₂'⋖y₂
year-unique {ℕ.zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {ℕ.zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {ℕ.zero} plain plain = refl
