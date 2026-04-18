module Gregorianum.Year.Properties where

open import Gregorianum.Year.Base

open import Gregorianum.Data.Cursor using (suc; first)
open import Gregorianum.Data.Position using (mkPos)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Product using (∃-syntax; _,_; proj₁; _×_)

year-type-unique : ∀ {y yt₁ yt₂}
                → y HasYearType yt₁
                → y HasYearType yt₂
                → yt₁ ≡ yt₂
year-type-unique common₁ common₁ = refl
year-type-unique leap₄ leap₄ = refl
year-type-unique common₁₀₀ common₁₀₀ = refl
year-type-unique leap₄₀₀ leap₄₀₀ = refl

has-type-irrelevant : ∀ {y yt} → (p q : y HasYearType yt) → p ≡ q
has-type-irrelevant common₁ common₁ = refl
has-type-irrelevant leap₄ leap₄ = refl
has-type-irrelevant common₁₀₀ common₁₀₀ = refl
has-type-irrelevant leap₄₀₀ leap₄₀₀ = refl

prev-unique : ∀ {y₁ y₂ y₃}
                → y₁ ⋖ y₃
                → y₂ ⋖ y₃
                → y₁ ≡ y₂
prev-unique step₁ step₁ = refl
prev-unique step₄ step₄ = refl
prev-unique step₁₀₀ step₁₀₀ = refl
prev-unique step₄₀₀ step₄₀₀ = refl

next-unique : ∀ {y₁ y₂ y₃}
                → y₁ ⋖ y₂
                → y₁ ⋖ y₃
                → y₂ ≡ y₃
next-unique step₁ step₁ = refl
next-unique step₄ step₄ = refl
next-unique step₁₀₀ step₁₀₀ = refl
next-unique step₄₀₀ step₄₀₀ = refl

⋖-irrelevant : ∀ {y₁ y₂} → (p₁ p₂ : y₁ ⋖ y₂) → p₁ ≡ p₂
⋖-irrelevant step₁ step₁ = refl
⋖-irrelevant step₄ step₄ = refl
⋖-irrelevant step₁₀₀ step₁₀₀ = refl
⋖-irrelevant step₄₀₀ step₄₀₀ = refl

∃prev⇒IsSuc : ∀ {y₁ y₂ : Year} → y₁ ⋖ y₂ → IsSuc y₂
∃prev⇒IsSuc step₁ = suc₁
∃prev⇒IsSuc step₄ = suc₄
∃prev⇒IsSuc step₁₀₀ = suc₁₀₀
∃prev⇒IsSuc step₄₀₀ = suc₄₀₀

¬IsSuc⇒first : ∀ {y} → ¬ (IsSuc y) → y ≡ year-first
¬IsSuc⇒first {q ′ pos₁₀₀ ″ pos₄ ‴ mkPos (suc cursor)} ¬isSuc = contradiction suc₁ ¬isSuc
¬IsSuc⇒first {q ′ pos₁₀₀ ″ mkPos (suc cursor) ‴ mkPos first} ¬isSuc = contradiction suc₄ ¬isSuc
¬IsSuc⇒first {q ′ mkPos (suc cursor) ″ mkPos first ‴ mkPos first} ¬isSuc = contradiction suc₁₀₀ ¬isSuc
¬IsSuc⇒first {suc q ′ mkPos first ″ mkPos first ‴ mkPos first} ¬isSuc = contradiction suc₄₀₀ ¬isSuc
¬IsSuc⇒first {year-first} ¬isSuc = refl

¬isSuc-unique : ∀ {d₁ d₂} → ¬ IsSuc d₁ → ¬ IsSuc d₂ → d₁ ≡ d₂
¬isSuc-unique ¬isSuc₁ ¬isSuc₂ with ¬IsSuc⇒first ¬isSuc₁ | ¬IsSuc⇒first ¬isSuc₂
... | refl | refl = refl

next-ordinal : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₁ HasOrdinal n → y₂ HasOrdinal (suc n)
next-ordinal step₁ ordinal = ordinal
next-ordinal step₄ ordinal = ordinal
next-ordinal step₁₀₀ ordinal = ordinal
next-ordinal step₄₀₀ ordinal = ordinal

prev-ordinal : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₂ HasOrdinal (suc n) → y₁ HasOrdinal n
prev-ordinal step₁ ordinal = ordinal
prev-ordinal step₄ ordinal = ordinal
prev-ordinal step₁₀₀ ordinal = ordinal
prev-ordinal step₄₀₀ ordinal = ordinal

suc-ordinal⇒IsSuc : ∀ {y n} → y HasOrdinal (suc n) → IsSuc y
suc-ordinal⇒IsSuc {quadricentennial ′ pos₁₀₀ ″ mkPos cursor ‴ mkPos (suc cursor₁)} {n = _} ordinal = suc₁
suc-ordinal⇒IsSuc {quadricentennial ′ pos₁₀₀ ″ mkPos (suc cursor) ‴ mkPos first} {n = _} ordinal = suc₄
suc-ordinal⇒IsSuc {quadricentennial ′ mkPos (suc cursor) ″ mkPos first ‴ mkPos first} {n = _} ordinal = suc₁₀₀
suc-ordinal⇒IsSuc {suc quadricentennial ′ mkPos first ″ mkPos first ‴ mkPos first} {n = _} ordinal = suc₄₀₀

IsSuc⇒suc-ordinal : ∀ {y} → IsSuc y → ∃[ n ] y HasOrdinal (suc n)
IsSuc⇒suc-ordinal suc₁ = _ , ordinal
IsSuc⇒suc-ordinal suc₄ = _ , ordinal
IsSuc⇒suc-ordinal suc₁₀₀ = _ , ordinal
IsSuc⇒suc-ordinal suc₄₀₀ = _ , ordinal

import Data.Nat.Induction as ℕ
open import Induction.WellFounded
import Relation.Binary.Construct.On as On
open import Function using (_∘_)

<-WellFounded : WellFounded _<_
<-WellFounded y = On.accessible (proj₁ ∘ toOrdinal) (ℕ.<-wellFounded-fast (proj₁ (toOrdinal y)))

⋖⇒suc : ∀ {y₁ y₂} → y₁ ⋖ y₂ → ∃[ n ] (y₁ HasOrdinal n) × (y₂ HasOrdinal (suc n))
⋖⇒suc {y₁} {y₂} p with next-ordinal p ordinal
...                  | epₙ = _ , ordinal , epₙ

ordinal-unique : ∀ {y n₁ n₂} → y HasOrdinal n₁ → y HasOrdinal n₂ → n₁ ≡ n₂
ordinal-unique ordinal ordinal = refl

⋖⇒< : ∀ {y₁ y₂} → y₁ ⋖ y₂ → y₁ < y₂
⋖⇒< {y₁} {y₂} p with ⋖⇒suc p | toOrdinal y₁ | toOrdinal y₂
... | n , ep₁ , ep₂ | n₁ , ordinal | n₂ , ordinal with ordinal-unique ep₁ ordinal | ordinal-unique ep₂ ordinal
... | eq₁ | eq₂ rewrite sym eq₂ | sym eq₁ = ≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded y = Subrelation.accessible ⋖⇒< (<-WellFounded y)

year-unique : ∀ {y₁ y₂ n} → y₁ HasOrdinal n → y₂ HasOrdinal n → y₁ ≡ y₂
year-unique {y₁} {y₂} {suc n} p q with prev y₁ (suc-ordinal⇒IsSuc p) | prev y₂ (suc-ordinal⇒IsSuc q)
... | y₁' , y₁'⋖y₁ | y₂' , y₂'⋖y₂ with year-unique {y₁'} {y₂'} (prev-ordinal y₁'⋖y₁ p) (prev-ordinal y₂'⋖y₂ q)
... | refl = next-unique y₁'⋖y₁ y₂'⋖y₂
year-unique {year-first} {year-first} {zero} ordinal ordinal = refl

common⇒IsSuc : ∀ {y} → y HasYearType common → IsSuc y
common⇒IsSuc common₁ = suc₁
common⇒IsSuc common₁₀₀ = suc₁₀₀

has-ordinal-irrelevant : ∀ {y n} → (p₁ p₂ : y HasOrdinal n) → p₁ ≡ p₂
has-ordinal-irrelevant ordinal ordinal = refl
