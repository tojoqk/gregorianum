module Gregorianum.Year.Weight.Properties where

open import Gregorianum.Year.Weight.Base using (_HasWeight_; _HasLeapWeight_; _HasCommonWeight_; weight)
open import Gregorianum.Year.Base using (Year; _′_″_‴_; _⋖_; suc₁; suc₄; suc₁₀₀; suc₄₀₀; IsSuc; _HasYearType_; leap; common; common₁; leap₄; common₁₀₀; leap₄₀₀; step₁; step₄; step₁₀₀; step₄₀₀)
open import Gregorianum.Data.Cursor using (suc; first)
open import Gregorianum.Data.Position using (Position; mkPos)

open import Data.Nat using (ℕ; suc; zero; NonZero; _+_; _*_)
open import Data.Nat.Properties using (+-assoc; +-comm; *-suc; *-distribˡ-+)
open import Data.Product using (∃-syntax; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; module ≡-Reasoning)

next-weight : ∀ {y₁ y₂ n} → {{_ : NonZero n}} → y₁ ⋖ y₂ → y₁ HasWeight n → y₂ HasWeight (suc n)
next-weight step₁ weight = weight
next-weight step₄ weight = weight
next-weight step₁₀₀ weight = weight
next-weight step₄₀₀ weight = weight

prev-weight : ∀ {y₁ y₂ n} → {{_ : NonZero n}} → y₁ ⋖ y₂ → y₂ HasWeight (suc n) → y₁ HasWeight n
prev-weight step₁ weight = weight
prev-weight step₄ weight = weight
prev-weight step₁₀₀ weight = weight
prev-weight step₄₀₀ weight = weight

suc-weight-IsSuc : ∀ {y n} → {{_ : NonZero n}} → y HasWeight (suc n) → IsSuc y
suc-weight-IsSuc {quadricentennial ′ pos₁₀₀ ″ mkPos cursor ‴ mkPos (suc cursor₁)} {n = _} weight = suc₁
suc-weight-IsSuc {quadricentennial ′ pos₁₀₀ ″ mkPos (suc cursor) ‴ mkPos first} {n = _} weight = suc₄
suc-weight-IsSuc {quadricentennial ′ mkPos (suc cursor) ″ mkPos first ‴ mkPos first} {n = _} weight = suc₁₀₀
suc-weight-IsSuc {suc quadricentennial ′ mkPos first ″ mkPos first ‴ mkPos first} {n = _} weight = suc₄₀₀

IsSuc⇒suc-weight : ∀ {y} → IsSuc y → ∃[ n ] y HasWeight (suc (suc n))
IsSuc⇒suc-weight suc₁ = _ , weight
IsSuc⇒suc-weight suc₄ = _ , weight
IsSuc⇒suc-weight suc₁₀₀ = _ , weight
IsSuc⇒suc-weight suc₄₀₀ = _ , weight

weight-unique : ∀ {y n₁ n₂} → {{_ : NonZero n₁}} → {{_ : NonZero n₂}} → y HasWeight n₁ → y HasWeight n₂ → n₁ ≡ n₂
weight-unique weight weight = refl

leap-weight-unique : ∀ {y n₁ n₂} → {{_ : NonZero n₁}} → {{_ : NonZero n₂}} → y HasLeapWeight n₁ → y HasLeapWeight n₂ → n₁ ≡ n₂
leap-weight-unique weight weight = refl

common-weight-unique : ∀ {y n₁ n₂} → y HasCommonWeight n₁ → y HasCommonWeight n₂ → n₁ ≡ n₂
common-weight-unique weight weight = refl


private
  m+k₁+n+k₂≡m+n+k₁+k₂ : ∀ m k₁ n k₂ → (m + k₁) + (n + k₂) ≡ (m + n) + (k₁ + k₂)
  m+k₁+n+k₂≡m+n+k₁+k₂ m k₁ n k₂ =
    begin
      (m + k₁) + (n + k₂)
    ≡⟨ +-assoc m k₁ (n + k₂) ⟩
      m + (k₁ + (n + k₂))
    ≡⟨ cong (m +_) (sym (+-assoc k₁ n k₂)) ⟩
      m + (k₁ + n + k₂)
    ≡⟨ cong (λ e → m + (e + k₂)) (+-comm k₁ n) ⟩
      m + (n + k₁ + k₂)
    ≡⟨ cong (m +_) (+-assoc n k₁ k₂) ⟩
      m + (n + (k₁ + k₂))
    ≡⟨ sym (+-assoc m n (k₁ + k₂)) ⟩
      m + n + (k₁ + k₂)
    ∎
    where open ≡-Reasoning

weight≡leap+common : ∀ {y w l c} {{_ : NonZero w}} {{_ : NonZero l}}
                   → y HasWeight w → y HasLeapWeight l → y HasCommonWeight c → w ≡ l + c
weight≡leap+common {y} weight weight weight =
  let q = Year.quadricentennial y in
  let a = Position.toℕ (Year.pos₁ y) in
  let b = Position.toℕ (Year.pos₄ y) in
  let c = Position.toℕ (Year.pos₁₀₀ y) in
  sym (cong suc (begin
    ((b + c * 24) + q * 97) + (((a + b * 3) + c * 76) + q * 303)
  ≡⟨ m+k₁+n+k₂≡m+n+k₁+k₂ (b + c * 24) (q * 97) ((a + b * 3) + c * 76) (q * 303) ⟩
     ((b + c * 24) + ((a + b * 3) + c * 76)) + (q * 97 + q * 303)
  ≡⟨ cong ((b + c * 24) + ((a + b * 3) + c * 76) +_) (sym (*-distribˡ-+ q 97 303)) ⟩
    ((b + c * 24) + ((a + b * 3) + c * 76)) + (q * 400)
  ≡⟨ cong (_+  q * 400) (m+k₁+n+k₂≡m+n+k₁+k₂ b (c * 24) (a + b * 3) (c * 76)) ⟩
    (b + (a + b * 3)) + (c * 24 + c * 76) +  (q * 400)
  ≡⟨ cong (λ e → (b + (a + b * 3)) + e +  (q * 400)) (sym (*-distribˡ-+ c 24 76)) ⟩
    (b + (a + b * 3)) + (c * 100) +  (q * 400)
  ≡⟨ cong (λ e → e + (c * 100) +  (q * 400)) (trans (+-comm b (a + b * 3)) (+-assoc a (b * 3) b)) ⟩
   a + (b * 3 + b) + (c * 100) +  (q * 400)
  ≡⟨ cong (λ e → a + e + (c * 100) +  (q * 400)) (trans (+-comm (b * 3) b) (sym (*-suc b 3))) ⟩
    a + b * 4 + c * 100 + q * 400
  ∎))
  where open ≡-Reasoning

IsSuc⇒suc-common-weight : ∀ {y} → IsSuc y → ∃[ n ] y HasCommonWeight (suc n)
IsSuc⇒suc-common-weight {(q ′ pos₁₀₀ ″ pos₄ ‴ mkPos (suc cursor))} suc₁ = _ , weight
IsSuc⇒suc-common-weight {(q ′ mkPos {acc = c} _ ″ mkPos (suc {acc = b} cursor) ‴ mkPos first)} suc₄ = _ , weight
IsSuc⇒suc-common-weight {(q ′ mkPos (suc {acc = n} cursor) ″ mkPos first ‴ mkPos first)} suc₁₀₀ = _ , weight
IsSuc⇒suc-common-weight {(suc q ′ mkPos first ″ mkPos first ‴ mkPos first)} suc₄₀₀ = _ , weight

next-leap-is-common : ∀ {y₁ y₂} → y₁ ⋖ y₂ → y₁ HasYearType leap → y₂ HasYearType common
next-leap-is-common step₁ leap₄ = common₁
next-leap-is-common step₁ leap₄₀₀ = common₁

next-leap-common-weight : ∀ {y₁ y₂ lw cw}
                             → {{_ : NonZero lw}}
                             → y₁ ⋖ y₂
                             → y₁ HasLeapWeight lw
                             → y₁ HasCommonWeight cw
                             → (y₂ HasYearType leap × y₂ HasLeapWeight (suc lw) × y₂ HasCommonWeight cw)
                             ⊎ (y₂ HasYearType common × y₂ HasLeapWeight lw × y₂ HasCommonWeight (suc cw))
next-leap-common-weight step₁ weight weight = inj₂ (common₁ , weight , weight)
next-leap-common-weight step₄ weight weight = inj₁ (leap₄ , weight , weight)
next-leap-common-weight step₁₀₀ weight weight = inj₂ (common₁₀₀ , weight , weight)
next-leap-common-weight step₄₀₀ weight weight = inj₁ (leap₄₀₀ , weight , weight)
