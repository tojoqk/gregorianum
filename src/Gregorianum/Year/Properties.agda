module Gregorianum.Year.Properties where

open import Gregorianum.Year.Base

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
import Gregorianum.Data.Cursor.Properties as Cursor
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary.Negation using (¬_; contradiction)

yearType-unique : ∀ {y yt₁ yt₂}
                → y HasYearType yt₁
                → y HasYearType yt₂
                → yt₁ ≡ yt₂
yearType-unique common common = refl
yearType-unique leap₄ leap₄ = refl
yearType-unique common₁₀₀ common₁₀₀ = refl
yearType-unique leap₄₀₀ leap₄₀₀ = refl

HasYearType-irrelevant : ∀ {y yt} → (p q : y HasYearType yt) → p ≡ q
HasYearType-irrelevant common common = refl
HasYearType-irrelevant leap₄ leap₄ = refl
HasYearType-irrelevant common₁₀₀ common₁₀₀ = refl
HasYearType-irrelevant leap₄₀₀ leap₄₀₀ = refl

prevYear-unique : ∀ {y₁ y₂ y₃}
                → y₁ ⋖ y₃
                → y₂ ⋖ y₃
                → y₁ ≡ y₂
prevYear-unique step step = refl
prevYear-unique step₄ step₄ = refl
prevYear-unique step₁₀₀ step₁₀₀ = refl
prevYear-unique step₄₀₀ step₄₀₀ = refl

nextYear-unique : ∀ {y₁ y₂ y₃}
                → y₁ ⋖ y₂
                → y₁ ⋖ y₃
                → y₂ ≡ y₃
nextYear-unique step step = refl
nextYear-unique step₄ step₄ = refl
nextYear-unique step₁₀₀ step₁₀₀ = refl
nextYear-unique step₄₀₀ step₄₀₀ = refl

¬IsSuccessor⇒first : ∀ {y} → ¬ (IsSuccessor y) → y ≡ (zero ×₄₀₀+ (mkPos first) ×₁₀₀+ (mkPos first) ×₄+ (mkPos first))
¬IsSuccessor⇒first {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)} ¬isSuc = contradiction suc₁ ¬isSuc
¬IsSuccessor⇒first {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} ¬isSuc = contradiction suc₄ ¬isSuc
¬IsSuccessor⇒first {q ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = contradiction suc₁₀₀ ¬isSuc
¬IsSuccessor⇒first {suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = contradiction suc₄₀₀ ¬isSuc
¬IsSuccessor⇒first {zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = refl
