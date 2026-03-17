module Gregorianum.Year.Properties where

open import Gregorianum.Year.Base

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
import Gregorianum.Data.Cursor.Properties as Cursor
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary.Negation using (¬_; contradiction)

year-type-unique : ∀ {y yt₁ yt₂}
                → y HasYearType yt₁
                → y HasYearType yt₂
                → yt₁ ≡ yt₂
year-type-unique common common = refl
year-type-unique leap₄ leap₄ = refl
year-type-unique common₁₀₀ common₁₀₀ = refl
year-type-unique leap₄₀₀ leap₄₀₀ = refl

has-year-type-irrelevant : ∀ {y yt} → (p q : y HasYearType yt) → p ≡ q
has-year-type-irrelevant common common = refl
has-year-type-irrelevant leap₄ leap₄ = refl
has-year-type-irrelevant common₁₀₀ common₁₀₀ = refl
has-year-type-irrelevant leap₄₀₀ leap₄₀₀ = refl

prev-year-unique : ∀ {y₁ y₂ y₃}
                → y₁ ⋖ y₃
                → y₂ ⋖ y₃
                → y₁ ≡ y₂
prev-year-unique step step = refl
prev-year-unique step₄ step₄ = refl
prev-year-unique step₁₀₀ step₁₀₀ = refl
prev-year-unique step₄₀₀ step₄₀₀ = refl

next-year-unique : ∀ {y₁ y₂ y₃}
                → y₁ ⋖ y₂
                → y₁ ⋖ y₃
                → y₂ ≡ y₃
next-year-unique step step = refl
next-year-unique step₄ step₄ = refl
next-year-unique step₁₀₀ step₁₀₀ = refl
next-year-unique step₄₀₀ step₄₀₀ = refl

¬IsSuccessor⇒first : ∀ {y} → ¬ (IsSuccessor y) → y ≡ (zero ×₄₀₀+ (mkPos first) ×₁₀₀+ (mkPos first) ×₄+ (mkPos first))
¬IsSuccessor⇒first {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)} ¬isSuc = contradiction suc₁ ¬isSuc
¬IsSuccessor⇒first {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} ¬isSuc = contradiction suc₄ ¬isSuc
¬IsSuccessor⇒first {q ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = contradiction suc₁₀₀ ¬isSuc
¬IsSuccessor⇒first {suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = contradiction suc₄₀₀ ¬isSuc
¬IsSuccessor⇒first {zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = refl
