module Gregorianum.Year.Weight.Properties where

open import Gregorianum.Year.Weight.Base

open import Gregorianum.Year.Base
open import Gregorianum.Year.Properties
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

nextYear-weight : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₁ HasWeight n → y₂ HasWeight (suc n)
nextYear-weight step weight = weight
nextYear-weight step₄ weight = weight
nextYear-weight step₁₀₀ weight = weight
nextYear-weight step₄₀₀ weight = weight

prevYear-weight : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₂ HasWeight (suc n) → y₁ HasWeight n
prevYear-weight step weight = weight
prevYear-weight step₄ weight = weight
prevYear-weight step₁₀₀ weight = weight
prevYear-weight step₄₀₀ weight = weight

suc-weight-is-successor : ∀ {y n} → y HasWeight (suc n) → IsSuccessor y
suc-weight-is-successor {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)} p = suc₁
suc-weight-is-successor {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} p = suc₄
suc-weight-is-successor {q ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} p = suc₁₀₀
suc-weight-is-successor {suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} p = suc₄₀₀

year-unique : ∀ {y₁ y₂ n} → y₁ HasWeight n → y₂ HasWeight n → y₁ ≡ y₂
year-unique {y₁} {y₂} {ℕ.suc n} p q with prevYear y₁ (suc-weight-is-successor p) | prevYear y₂ (suc-weight-is-successor q)
... | y₁' , y₁'⋖y₁ | y₂' , y₂'⋖y₂ with year-unique {y₁'} {y₂'} {n} (prevYear-weight y₁'⋖y₁ p) (prevYear-weight y₂'⋖y₂ q)
... | refl = nextYear-unique y₁'⋖y₁ y₂'⋖y₂
year-unique {ℕ.zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {ℕ.zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {ℕ.zero} weight weight = refl

weight-unique : ∀ {y n₁ n₂} → y HasWeight n₁ → y HasWeight n₂ → n₁ ≡ n₂
weight-unique weight weight = refl

isSuccessor⇒suc-weight : ∀ {y} → IsSuccessor y → ∃[ n ] y HasWeight (suc n)
isSuccessor⇒suc-weight suc₁ = _ , weight
isSuccessor⇒suc-weight suc₄ = _ , weight
isSuccessor⇒suc-weight suc₁₀₀ = _ , weight
isSuccessor⇒suc-weight suc₄₀₀ = _ , weight
