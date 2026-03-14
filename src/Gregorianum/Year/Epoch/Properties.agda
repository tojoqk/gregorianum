module Gregorianum.Year.Epoch.Properties where

open import Gregorianum.Year.Epoch.Base

open import Gregorianum.Year.Base
open import Gregorianum.Year.Properties
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

nextYear-epoch : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₁ HasEpoch n → y₂ HasEpoch (suc n)
nextYear-epoch step epoch = epoch
nextYear-epoch step₄ epoch = epoch
nextYear-epoch step₁₀₀ epoch = epoch
nextYear-epoch step₄₀₀ epoch = epoch

prevYear-epoch : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₂ HasEpoch (suc n) → y₁ HasEpoch n
prevYear-epoch step epoch = epoch
prevYear-epoch step₄ epoch = epoch
prevYear-epoch step₁₀₀ epoch = epoch
prevYear-epoch step₄₀₀ epoch = epoch

suc-epoch-is-successor : ∀ {y n} → y HasEpoch (suc n) → IsSuccessor y
suc-epoch-is-successor {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)} p = suc₁
suc-epoch-is-successor {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} p = suc₄
suc-epoch-is-successor {q ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} p = suc₁₀₀
suc-epoch-is-successor {suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} p = suc₄₀₀

year-unique : ∀ {y₁ y₂ n} → y₁ HasEpoch n → y₂ HasEpoch n → y₁ ≡ y₂
year-unique {y₁} {y₂} {ℕ.suc n} p q with prevYear y₁ (suc-epoch-is-successor p) | prevYear y₂ (suc-epoch-is-successor q)
... | y₁' , y₁'⋖y₁ | y₂' , y₂'⋖y₂ with year-unique {y₁'} {y₂'} {n} (prevYear-epoch y₁'⋖y₁ p) (prevYear-epoch y₂'⋖y₂ q)
... | refl = nextYear-unique y₁'⋖y₁ y₂'⋖y₂
year-unique {ℕ.zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {ℕ.zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {ℕ.zero} epoch epoch = refl

epoch-unique : ∀ {y n₁ n₂} → y HasEpoch n₁ → y HasEpoch n₂ → n₁ ≡ n₂
epoch-unique epoch epoch = refl

isSuccessor⇒suc-epoch : ∀ {y} → IsSuccessor y → ∃[ n ] y HasEpoch (suc n)
isSuccessor⇒suc-epoch suc₁ = _ , epoch
isSuccessor⇒suc-epoch suc₄ = _ , epoch
isSuccessor⇒suc-epoch suc₁₀₀ = _ , epoch
isSuccessor⇒suc-epoch suc₄₀₀ = _ , epoch
