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

¬∃prev⇒first : ∀ {y} → ¬ (∃[ y′ ] y′ ⋖ y) → y ≡ year-first
¬∃prev⇒first {q ′ pos₁₀₀ ″ pos₄ ‴ mkPos (suc cursor)} p = contradiction (_ , step₁) p
¬∃prev⇒first {q ′ pos₁₀₀ ″ mkPos (suc cursor) ‴ mkPos first} p = contradiction (_ , step₄) p
¬∃prev⇒first {q ′ mkPos (suc cursor) ″ mkPos first ‴ mkPos first} p = contradiction (_ , step₁₀₀) p
¬∃prev⇒first {suc q ′ mkPos first ″ mkPos first ‴ mkPos first} p = contradiction (_ , step₄₀₀) p
¬∃prev⇒first {year-first} p = refl

¬∃prev-unique : ∀ {y₁ y₂} → ¬ (∃[ y′ ] y′ ⋖ y₁) → ¬ (∃[ y′ ] y′ ⋖ y₂) → y₁ ≡ y₂
¬∃prev-unique {y₁} {y₂} p₁ p₂ rewrite ¬∃prev⇒first p₁ | ¬∃prev⇒first p₂ = refl

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

suc-ordinal⇒∃prev : ∀ {y n} → y HasOrdinal (suc n) → ∃[ y′ ] y′ ⋖ y
suc-ordinal⇒∃prev {quadricentennial ′ pos₁₀₀ ″ mkPos cursor ‴ mkPos (suc cursor₁)} {n = _} ordinal = _ , step₁
suc-ordinal⇒∃prev {quadricentennial ′ pos₁₀₀ ″ mkPos (suc cursor) ‴ mkPos first} {n = _} ordinal = _ , step₄
suc-ordinal⇒∃prev {quadricentennial ′ mkPos (suc cursor) ″ mkPos first ‴ mkPos first} {n = _} ordinal = _ , step₁₀₀
suc-ordinal⇒∃prev {suc quadricentennial ′ mkPos first ″ mkPos first ‴ mkPos first} {n = _} ordinal = _ , step₄₀₀

∃prev⇒suc-ordinal : ∀ {y} → ∃[ y′ ] y′ ⋖ y → ∃[ n ] y HasOrdinal (suc n)
∃prev⇒suc-ordinal (_ , step₁) = _ , ordinal
∃prev⇒suc-ordinal (_ , step₄) = _ , ordinal
∃prev⇒suc-ordinal (_ , step₁₀₀) = _ , ordinal
∃prev⇒suc-ordinal (_ , step₄₀₀) = _ , ordinal

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
year-unique {y₁} {y₂} {suc n} p q with suc-ordinal⇒∃prev p | suc-ordinal⇒∃prev q
... | y₁' , y₁'⋖y₁ | y₂' , y₂'⋖y₂ with year-unique {y₁'} {y₂'} (prev-ordinal y₁'⋖y₁ p) (prev-ordinal y₂'⋖y₂ q)
... | refl = next-unique y₁'⋖y₁ y₂'⋖y₂
year-unique {year-first} {year-first} {zero} ordinal ordinal = refl

common⇒∃prev : ∀ {y} → y HasYearType common → ∃[ y′ ] y′ ⋖ y
common⇒∃prev common₁ = _ , step₁
common⇒∃prev common₁₀₀ = _ , step₁₀₀

has-ordinal-irrelevant : ∀ {y n} → (p₁ p₂ : y HasOrdinal n) → p₁ ≡ p₂
has-ordinal-irrelevant ordinal ordinal = refl
