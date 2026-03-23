module Gregorianum.Year.Properties where

open import Gregorianum.Year.Base

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position hiding (_<_)
import Gregorianum.Data.Cursor.Properties as Cursor
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat as ℕ using (ℕ; _+_; _*_; zero; suc; NonZero)
open import Data.Nat.Properties using (suc-injective; ≤-refl)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Data.Product using (∃-syntax; _,_; proj₁; _×_)
open import Data.Nat.Solver using (module +-*-Solver)

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

∃prev⇒IsSuccessor : ∀ {y₁ y₂ : Year} → y₁ ⋖ y₂ → IsSuccessor y₂
∃prev⇒IsSuccessor step = suc₁
∃prev⇒IsSuccessor step₄ = suc₄
∃prev⇒IsSuccessor step₁₀₀ = suc₁₀₀
∃prev⇒IsSuccessor step₄₀₀ = suc₄₀₀

¬IsSuccessor⇒first : ∀ {y} → ¬ (IsSuccessor y) → y ≡ (zero ×₄₀₀+ (mkPos first) ×₁₀₀+ (mkPos first) ×₄+ (mkPos first))
¬IsSuccessor⇒first {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)} ¬isSuc = contradiction suc₁ ¬isSuc
¬IsSuccessor⇒first {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} ¬isSuc = contradiction suc₄ ¬isSuc
¬IsSuccessor⇒first {q ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = contradiction suc₁₀₀ ¬isSuc
¬IsSuccessor⇒first {suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = contradiction suc₄₀₀ ¬isSuc
¬IsSuccessor⇒first {zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = refl

next-year-ordinal : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₁ HasOrdinal n → y₂ HasOrdinal (suc n)
next-year-ordinal step has-ordinal = has-ordinal
next-year-ordinal step₄ has-ordinal = has-ordinal
next-year-ordinal step₁₀₀ has-ordinal = has-ordinal
next-year-ordinal step₄₀₀ has-ordinal = has-ordinal

prev-year-ordinal : ∀ {y₁ y₂ n} → y₁ ⋖ y₂ → y₂ HasOrdinal (suc n) → y₁ HasOrdinal n
prev-year-ordinal step has-ordinal = has-ordinal
prev-year-ordinal step₄ has-ordinal = has-ordinal
prev-year-ordinal step₁₀₀ has-ordinal = has-ordinal
prev-year-ordinal step₄₀₀ has-ordinal = has-ordinal

suc-ordinal-is-successor : ∀ {y n} → y HasOrdinal (suc n) → IsSuccessor y
suc-ordinal-is-successor {quadricentennial ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos cursor ×₄+ mkPos (suc cursor₁)} {n = _} has-ordinal = suc₁
suc-ordinal-is-successor {quadricentennial ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} {n = _} has-ordinal = suc₄
suc-ordinal-is-successor {quadricentennial ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} {n = _} has-ordinal = suc₁₀₀
suc-ordinal-is-successor {suc quadricentennial ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {n = _} has-ordinal = suc₄₀₀

is-successor⇒suc-ordinal : ∀ {y} → IsSuccessor y → ∃[ n ] y HasOrdinal (suc n)
is-successor⇒suc-ordinal suc₁ = _ , has-ordinal
is-successor⇒suc-ordinal suc₄ = _ , has-ordinal
is-successor⇒suc-ordinal suc₁₀₀ = _ , has-ordinal
is-successor⇒suc-ordinal suc₄₀₀ = _ , has-ordinal

import Data.Nat.Induction as ℕ
open import Induction.WellFounded
import Relation.Binary.Construct.On as On
open import Function using (_∘_)

<-WellFounded : WellFounded _<_
<-WellFounded y = On.accessible (proj₁ ∘ toOrdinal) (ℕ.<-wellFounded-fast (proj₁ (toOrdinal y)))

⋖⇒suc : ∀ {y₁ y₂} → y₁ ⋖ y₂ → ∃[ n ] (y₁ HasOrdinal n) × (y₂ HasOrdinal (suc n))
⋖⇒suc {y₁} {y₂} p with next-year-ordinal p has-ordinal
...                  | epₙ = _ , has-ordinal , epₙ

ordinal-unique : ∀ {y n₁ n₂} → y HasOrdinal n₁ → y HasOrdinal n₂ → n₁ ≡ n₂
ordinal-unique has-ordinal has-ordinal = refl

⋖⇒< : ∀ {y₁ y₂} → y₁ ⋖ y₂ → y₁ < y₂
⋖⇒< {y₁} {y₂} p with ⋖⇒suc p | toOrdinal y₁ | toOrdinal y₂
... | n , ep₁ , ep₂ | n₁ , has-ordinal | n₂ , has-ordinal with ordinal-unique ep₁ has-ordinal | ordinal-unique ep₂ has-ordinal
... | eq₁ | eq₂ rewrite sym eq₂ | sym eq₁ = ≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded y = Subrelation.accessible ⋖⇒< (<-WellFounded y)

year-unique : ∀ {y₁ y₂ n} → y₁ HasOrdinal n → y₂ HasOrdinal n → y₁ ≡ y₂
year-unique {y₁} {y₂} {suc n} p q with prevYear y₁ (suc-ordinal-is-successor p) | prevYear y₂ (suc-ordinal-is-successor q)
... | y₁' , y₁'⋖y₁ | y₂' , y₂'⋖y₂ with year-unique {y₁'} {y₂'} (prev-year-ordinal y₁'⋖y₁ p) (prev-year-ordinal y₂'⋖y₂ q)
... | refl = next-year-unique y₁'⋖y₁ y₂'⋖y₂
year-unique {zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {zero} has-ordinal has-ordinal = refl

common⇒is-successor : ∀ {y} → y HasYearType common → IsSuccessor y
common⇒is-successor common = suc₁
common⇒is-successor common₁₀₀ = suc₁₀₀
