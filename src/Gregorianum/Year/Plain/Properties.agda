module Gregorianum.Year.Plain.Properties where

open import Gregorianum.Year.Plain.Base using (_HasPlain_; plain)

open import Gregorianum.Year.Base using (year-first; _⋖_; _′_″_‴_; step₁; step₄; step₁₀₀; step₄₀₀)
open import Gregorianum.Year.Properties hiding (year-unique)
open import Gregorianum.Data.Cursor using (first; suc)
open import Gregorianum.Data.Position using (mkPos)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; ∃-syntax)
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

suc-plain-∃prev : ∀ {y n} → y HasPlain (suc n) → ∃[ y′ ] y′ ⋖ y
suc-plain-∃prev {q ′ pos₁₀₀ ″ pos₄ ‴ mkPos (suc cursor)} p = _ , step₁
suc-plain-∃prev {q ′ pos₁₀₀ ″ mkPos (suc cursor) ‴ mkPos first} p = _ , step₄
suc-plain-∃prev {q ′ mkPos (suc cursor) ″ mkPos first ‴ mkPos first} p = _ , step₁₀₀
suc-plain-∃prev {suc q ′ mkPos first ″ mkPos first ‴ mkPos first} p = _ , step₄₀₀

year-unique : ∀ {y₁ y₂ n} → y₁ HasPlain n → y₂ HasPlain n → y₁ ≡ y₂
year-unique {y₁} {y₂} {ℕ.suc n} p q with suc-plain-∃prev p | suc-plain-∃prev q
... | y₁' , y₁'⋖y₁ | y₂' , y₂'⋖y₂ with year-unique {y₁'} {y₂'} {n} (prev-plain y₁'⋖y₁ p) (prev-plain y₂'⋖y₂ q)
... | refl = next-unique y₁'⋖y₁ y₂'⋖y₂
year-unique {year-first} {year-first} {ℕ.zero} plain plain = refl
