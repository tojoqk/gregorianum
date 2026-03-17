module Gregorianum.Year.Weight.Properties where

open import Gregorianum.Year.Weight.Base

open import Gregorianum.Year.Base
open import Gregorianum.Year.Properties
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

next-year-weight : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₁ HasWeight n → y₂ HasWeight (suc n)
next-year-weight step weight = weight
next-year-weight step₄ weight = weight
next-year-weight step₁₀₀ weight = weight
next-year-weight step₄₀₀ weight = weight

prev-year-weight : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₂ HasWeight (suc n) → y₁ HasWeight n
prev-year-weight step weight = weight
prev-year-weight step₄ weight = weight
prev-year-weight step₁₀₀ weight = weight
prev-year-weight step₄₀₀ weight = weight

suc-weight-is-successor : ∀ {y n} → y HasWeight (suc n) → IsSuccessor y
suc-weight-is-successor {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)} p = suc₁
suc-weight-is-successor {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} p = suc₄
suc-weight-is-successor {q ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} p = suc₁₀₀
suc-weight-is-successor {suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} p = suc₄₀₀

year-unique : ∀ {y₁ y₂ n} → y₁ HasWeight n → y₂ HasWeight n → y₁ ≡ y₂
year-unique {y₁} {y₂} {ℕ.suc n} p q with prevYear y₁ (suc-weight-is-successor p) | prevYear y₂ (suc-weight-is-successor q)
... | y₁' , y₁'⋖y₁ | y₂' , y₂'⋖y₂ with year-unique {y₁'} {y₂'} {n} (prev-year-weight y₁'⋖y₁ p) (prev-year-weight y₂'⋖y₂ q)
... | refl = next-year-unique y₁'⋖y₁ y₂'⋖y₂
year-unique {ℕ.zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {ℕ.zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {ℕ.zero} weight weight = refl

weight-unique : ∀ {y n₁ n₂} → y HasWeight n₁ → y HasWeight n₂ → n₁ ≡ n₂
weight-unique weight weight = refl

is-successor⇒suc-weight : ∀ {y} → IsSuccessor y → ∃[ n ] y HasWeight (suc n)
is-successor⇒suc-weight suc₁ = _ , weight
is-successor⇒suc-weight suc₄ = _ , weight
is-successor⇒suc-weight suc₁₀₀ = _ , weight
is-successor⇒suc-weight suc₄₀₀ = _ , weight
