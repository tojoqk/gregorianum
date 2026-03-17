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

¬IsSuccessor⇒first : ∀ {y} → ¬ (IsSuccessor y) → y ≡ (zero ×₄₀₀+ (mkPos first) ×₁₀₀+ (mkPos first) ×₄+ (mkPos first))
¬IsSuccessor⇒first {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor)} ¬isSuc = contradiction suc₁ ¬isSuc
¬IsSuccessor⇒first {q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} ¬isSuc = contradiction suc₄ ¬isSuc
¬IsSuccessor⇒first {q ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = contradiction suc₁₀₀ ¬isSuc
¬IsSuccessor⇒first {suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = contradiction suc₄₀₀ ¬isSuc
¬IsSuccessor⇒first {zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} ¬isSuc = refl

next-year-weight : ∀ {y₁ y₂ n} → {{_ : NonZero n}} → y₁ ⋖ y₂ → y₁ HasWeight n → y₂ HasWeight (suc n)
next-year-weight step has-weight = has-weight
next-year-weight step₄ has-weight = has-weight
next-year-weight step₁₀₀ has-weight = has-weight
next-year-weight step₄₀₀ has-weight = has-weight

prev-year-weight : ∀ {y₁ y₂ n} → {{_ : NonZero n}} → y₁ ⋖ y₂ → y₂ HasWeight (suc n) → y₁ HasWeight n
prev-year-weight step has-weight = has-weight
prev-year-weight step₄ has-weight = has-weight
prev-year-weight step₁₀₀ has-weight = has-weight
prev-year-weight step₄₀₀ has-weight = has-weight

suc-weight-is-successor : ∀ {y n} → {{_ : NonZero n}} → y HasWeight (suc n) → IsSuccessor y
suc-weight-is-successor {quadricentennial ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos cursor ×₄+ mkPos (suc cursor₁)} {n = _} has-weight = suc₁
suc-weight-is-successor {quadricentennial ×₄₀₀+ pos₁₀₀ ×₁₀₀+ mkPos (suc cursor) ×₄+ mkPos first} {n = _} has-weight = suc₄
suc-weight-is-successor {quadricentennial ×₄₀₀+ mkPos (suc cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first} {n = _} has-weight = suc₁₀₀
suc-weight-is-successor {suc quadricentennial ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {n = _} has-weight = suc₄₀₀

is-successor⇒suc-weight : ∀ {y} → IsSuccessor y → ∃[ n ] y HasWeight (suc (suc n))
is-successor⇒suc-weight suc₁ = _ , has-weight
is-successor⇒suc-weight suc₄ = _ , has-weight
is-successor⇒suc-weight suc₁₀₀ = _ , has-weight
is-successor⇒suc-weight suc₄₀₀ = _ , has-weight

import Data.Nat.Induction as ℕ
open import Induction.WellFounded
import Relation.Binary.Construct.On as On
open import Function using (_∘_)

<-WellFounded : WellFounded _<_
<-WellFounded y = On.accessible (proj₁ ∘ toWeight) (ℕ.<-wellFounded-fast (proj₁ (toWeight y)))

⋖⇒suc : ∀ {y₁ y₂} → y₁ ⋖ y₂ → ∃[ n ] (y₁ HasWeight (suc n)) × (y₂ HasWeight (suc (suc n)))
⋖⇒suc {y₁} {y₂} p with next-year-weight p has-weight
...                  | epₙ = _ , has-weight , epₙ

weight-unique : ∀ {y n₁ n₂} → {{_ : NonZero n₁}} → {{_ : NonZero n₂}} → y HasWeight n₁ → y HasWeight n₂ → n₁ ≡ n₂
weight-unique has-weight has-weight = refl

⋖⇒< : ∀ {y₁ y₂} → y₁ ⋖ y₂ → y₁ < y₂
⋖⇒< {y₁} {y₂} p with ⋖⇒suc p | toWeight y₁ | toWeight y₂
... | n , ep₁ , ep₂ | n₁ , has-weight | n₂ , has-weight with weight-unique ep₁ has-weight | weight-unique ep₂ has-weight
... | eq₁ | eq₂ rewrite sym (suc-injective eq₂) | sym eq₁ = ≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded y = Subrelation.accessible ⋖⇒< (<-WellFounded y)

private
  year-unique' : ∀ {y₁ y₂ n} → {{_ : NonZero n}} → y₁ HasWeight n → y₂ HasWeight n → Acc _⋖_ y₁ → y₁ ≡ y₂
  year-unique' {y₁} {y₂} {suc (suc n)} p q (acc rs) with prevYear y₁ (suc-weight-is-successor p) | prevYear y₂ (suc-weight-is-successor q)
  ... | y₁' , y₁'⋖y₁ | y₂' , y₂'⋖y₂ with year-unique' {y₁'} {y₂'} (prev-year-weight y₁'⋖y₁ p) (prev-year-weight y₂'⋖y₂ q) (rs y₁'⋖y₁)
  ... | refl = next-year-unique y₁'⋖y₁ y₂'⋖y₂
  year-unique' {zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {zero ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first} {suc zero} has-weight has-weight _ = refl

year-unique : ∀ {y₁ y₂ n} → {{_ : NonZero n}} → y₁ HasWeight n → y₂ HasWeight n → y₁ ≡ y₂
year-unique p q = year-unique' p q (⋖-wellFounded _)

weight≡leap+common : ∀ {y w l c} {{_ : NonZero w}} {{_ : NonZero l}}
                   → y HasWeight w → y HasLeapWeight l → y HasCommonWeight c → w ≡ l + c
weight≡leap+common {y} has-weight has-weight has-weight =
  solve 4 (λ a b c q → con 1 :+ (a :+ (b :+ (c :+ q :* con 4) :* con 25) :* con 4)
                       := (con 1 :+ q) :+ (b :+ (c :+ q :* con 4) :* con 24)
                          :+ (a :+ c :+ (q :* con 3) :+ (b :+ (c :+ q :* con 4) :* con 25) :* con 3))
        refl
        (Position.toℕ (Year.pos₁ y)) (Position.toℕ (Year.pos₄ y)) (Position.toℕ (Year.pos₁₀₀ y)) (Year.quadricentennial y)
  where open +-*-Solver
