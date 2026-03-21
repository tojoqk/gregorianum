module Gregorianum.Year.Weight.Properties where

open import Gregorianum.Year.Base hiding (_<_)
open import Gregorianum.Year.Weight.Base

open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position hiding (_<_)
open import Data.Nat as ℕ using (ℕ; suc; zero; NonZero; _+_; _*_)
open import Data.Product using (∃-syntax; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Unit using (⊤; tt)

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

weight-unique : ∀ {y n₁ n₂} → {{_ : NonZero n₁}} → {{_ : NonZero n₂}} → y HasWeight n₁ → y HasWeight n₂ → n₁ ≡ n₂
weight-unique has-weight has-weight = refl

leap-weight-unique : ∀ {y n₁ n₂} → {{_ : NonZero n₁}} → {{_ : NonZero n₂}} → y HasLeapWeight n₁ → y HasLeapWeight n₂ → n₁ ≡ n₂
leap-weight-unique has-weight has-weight = refl

common-weight-unique : ∀ {y n₁ n₂} → y HasCommonWeight n₁ → y HasCommonWeight n₂ → n₁ ≡ n₂
common-weight-unique has-weight has-weight = refl

weight≡leap+common : ∀ {y w l c} {{_ : NonZero w}} {{_ : NonZero l}}
                   → y HasWeight w → y HasLeapWeight l → y HasCommonWeight c → w ≡ l + c
weight≡leap+common {y} has-weight has-weight has-weight =
  solve 4 (λ a b c q → con 1 :+ (a :+ (b :+ (c :+ q :* con 4) :* con 25) :* con 4)
                     := (con 1 :+ b) :+ c :* con 24 :+ q :* con 97
                     :+ (a :+ b :* con 3 :+ c :* con 76 :+ q :* con 303))
        refl
        (Position.toℕ (Year.pos₁ y)) (Position.toℕ (Year.pos₄ y)) (Position.toℕ (Year.pos₁₀₀ y)) (Year.quadricentennial y)
  where open +-*-Solver

is-successor⇒suc-common-weight : ∀ {y} → IsSuccessor y → ∃[ n ] y HasCommonWeight (suc n)
is-successor⇒suc-common-weight {(q ×₄₀₀+ pos₁₀₀ ×₁₀₀+ pos₄ ×₄+ mkPos (suc cursor))} suc₁ = _ , has-weight
is-successor⇒suc-common-weight {(q ×₄₀₀+ mkPos {acc = c} _ ×₁₀₀+ mkPos (suc {acc = b} cursor) ×₄+ mkPos first)} suc₄ = _ , has-weight
is-successor⇒suc-common-weight {(q ×₄₀₀+ mkPos (suc {acc = n} cursor) ×₁₀₀+ mkPos first ×₄+ mkPos first)} suc₁₀₀ = _ , has-weight
is-successor⇒suc-common-weight {(suc q ×₄₀₀+ mkPos first ×₁₀₀+ mkPos first ×₄+ mkPos first)} suc₄₀₀ = _ , has-weight

next-leap-year-is-common : ∀ {y₁ y₂} → y₁ ⋖ y₂ → y₁ HasYearType leap → y₂ HasYearType common
next-leap-year-is-common step leap₄ = common
next-leap-year-is-common step leap₄₀₀ = common

next-year-leap-common-weight : ∀ {y₁ y₂ lw cw}
                             → {{_ : NonZero lw}}
                             → y₁ ⋖ y₂
                             → y₁ HasLeapWeight lw
                             → y₁ HasCommonWeight cw
                             → (y₂ HasYearType leap × y₂ HasLeapWeight (suc lw) × y₂ HasCommonWeight cw)
                             ⊎ (y₂ HasYearType common × y₂ HasLeapWeight lw × y₂ HasCommonWeight (suc cw))
next-year-leap-common-weight step has-weight has-weight = inj₂ (common , has-weight , has-weight)
next-year-leap-common-weight step₄ has-weight has-weight = inj₁ (leap₄ , has-weight , has-weight)
next-year-leap-common-weight step₁₀₀ has-weight has-weight = inj₂ (common₁₀₀ , has-weight , has-weight)
next-year-leap-common-weight step₄₀₀ has-weight has-weight = inj₁ (leap₄₀₀ , has-weight , has-weight)
