module Gregorianum.DateHour.Properties where

open import Gregorianum.DateHour.Base

open import Gregorianum.Data.Cursor using (Cursor; first; last; suc)
open import Gregorianum.Hour using (Hour; [_])
open import Gregorianum.Data.Position as Position using (Position; mkPos)
open import Gregorianum.Year as Y using (leap₄₀₀)
open import Gregorianum.Year.Weight using (weight)
open import Gregorianum.Month as M using (january-weight)
import Gregorianum.YearMonth as YM
open import Gregorianum.Date as D using (leap-ordinal)
import Gregorianum.Date.Properties as D
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_; s≤s)
open import Data.Nat.Properties using (+-cancelˡ-≡; *-cancelʳ-≡; ≤-refl; +-comm)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂; _×_)
open import Induction.WellFounded using (WellFounded; module Subrelation)
import Relation.Binary.Construct.On as On
open import Function using (_∘_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

⋖-irrelevant : ∀ {dh₁ dh₂} → (p₁ p₂ : dh₁ ⋖ dh₂) → p₁ ≡ p₂
⋖-irrelevant step-hour step-hour = refl
⋖-irrelevant (step-date p₁) (step-date p₂) with D.⋖-irrelevant p₁ p₂
... | refl = refl

next-unique : ∀ {dh₁ dh₂ dh₃}
            → dh₁ ⋖ dh₂
            → dh₁ ⋖ dh₃
            → dh₂ ≡ dh₃
next-unique step-hour step-hour = refl
next-unique (step-date d₁⋖d₂) (step-date d₁⋖d₃) with D.next-unique d₁⋖d₂ d₁⋖d₃
... | refl = refl

prev-unique : ∀ {dh₁ dh₂ dh₃}
            → dh₁ ⋖ dh₃
            → dh₂ ⋖ dh₃
            → dh₁ ≡ dh₂
prev-unique step-hour step-hour = refl
prev-unique (step-date d₁⋖d₃) (step-date d₂⋖d₃) with D.prev-unique d₁⋖d₃ d₂⋖d₃
... | refl = refl

<-WellFounded : WellFounded _<_
<-WellFounded d = On.accessible (proj₁ ∘ toOrdinal) (<-wellFounded-fast (proj₁ (toOrdinal d)))

next-ordinal : ∀ {dh₁ dh₂ n} → dh₁ ⋖ dh₂ → dh₁ HasOrdinal n → dh₂ HasOrdinal (suc n)
next-ordinal step-hour (ordinal dho) = ordinal dho
next-ordinal (step-date d₁⋖d₂) (ordinal dho) = ordinal (D.next-ordinal d₁⋖d₂ dho)

ordinal-unique : ∀ {d n₁ n₂} → d HasOrdinal n₁ → d HasOrdinal n₂ → n₁ ≡ n₂
ordinal-unique (ordinal dho₁) (ordinal dho₂) with D.ordinal-unique dho₁ dho₂
... | refl = refl

⋖⇒suc : ∀ {dh₁ dh₂} → dh₁ ⋖ dh₂ → ∃[ n ] (dh₁ HasOrdinal n) × (dh₂ HasOrdinal (suc n))
⋖⇒suc {dh₁} {dh₂} dh₁⋖dh₂ with toOrdinal dh₁
... | n , ho₁ with next-ordinal dh₁⋖dh₂ ho₁
... | ho₂ = n , ho₁ , ho₂

private
  pattern suc⁴ x = suc (suc (suc (suc x)))
  pattern suc²⁰ x = suc⁴ (suc⁴ (suc⁴ (suc⁴ (suc⁴ x))))
  pattern suc²³ x = suc²⁰ (suc (suc (suc x)))
  pattern suc²⁴ x = suc⁴ (suc²⁰ x)

⋖⇒< : ∀ {dh₁ dh₂} → dh₁ ⋖ dh₂ → dh₁ < dh₂
⋖⇒< step-hour = s≤s ≤-refl
⋖⇒< (step-date {d₁} {d₂} d₁⋖d₂) = h
  where
    h : 23 +  proj₁ (D.toOrdinal d₁) * 24 ℕ.< proj₁ (D.toOrdinal d₂) * 24
    h with D.toOrdinal d₁ | D.toOrdinal d₂
    ... | n₁ , dho₁ | n₂ , dho₂ with D.next-ordinal d₁⋖d₂ dho₁
    ... | dho₂' with D.ordinal-unique dho₂ dho₂'
    ... | refl = ≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded dh = Subrelation.accessible ⋖⇒< (<-WellFounded dh)

∃prev⇒suc-ordinal : ∀ {dh} → ∃[ dh′ ] dh′ ⋖ dh → ∃[ n ] dh HasOrdinal (suc n)
∃prev⇒suc-ordinal (dh′ , h) with toOrdinal dh′
... | n′ , ho′ = n′ , (next-ordinal h ho′)

suc-ordinal⇒∃prev : ∀ {dh n} → dh HasOrdinal (suc n) → ∃[ dh′ ] dh′ ⋖ dh
suc-ordinal⇒∃prev {date at [ mkPos first ]} {n} ho with D.prev? date
... | yes (date , ∃prev) = (date at [ mkPos last ]) , step-date ∃prev
... | no ¬∃prev with D.¬∃prev⇒first ¬∃prev
... | refl with ordinal-unique ho (ordinal (leap-ordinal leap₄₀₀ weight weight january-weight))
... | ()
suc-ordinal⇒∃prev {date at [ mkPos (suc c) ]} {n} p = (date at [ mkPos c ]) , step-hour

¬∃prev⇒first : ∀ {dh} → ¬ (∃[ dh′ ] dh′ ⋖ dh) → dh ≡ D.date-first at [ mkPos first ]
¬∃prev⇒first {date at [ mkPos first ]} ¬∃prev with D.prev? date
... | yes (d , p) = contradiction ((d at [ mkPos last ]) , step-date p) ¬∃prev
... | no ¬p with D.¬∃prev⇒first ¬p
... | refl = refl
¬∃prev⇒first {date at [ mkPos (suc cursor) ]} ¬∃prev = contradiction ((date at [ mkPos cursor ]) , step-hour) ¬∃prev

ordinal≡0⇒first : ∀ {dh} → dh HasOrdinal 0 → dh ≡ date-hour-first
ordinal≡0⇒first {dh} ho with prev? dh
ordinal≡0⇒first {dh} ho | yes ∃prev with ∃prev⇒suc-ordinal ∃prev
ordinal≡0⇒first {dh} ho | yes _ | n , ho′ with ordinal-unique ho ho′
... | ()
ordinal≡0⇒first {dh} ho | no ¬∃prev with ¬∃prev⇒first ¬∃prev
... | refl = refl

prev-ordinal : ∀ {dh₁ dh₂ n} → dh₁ ⋖ dh₂ → dh₂ HasOrdinal (suc n) → dh₁ HasOrdinal n
prev-ordinal dh₁⋖dh₂ ho with ⋖⇒suc dh₁⋖dh₂
... | _ , ho₁ , ho₂ with ordinal-unique ho ho₂
... | refl = ho₁

¬∃prev-unique : ∀ {dh₁ dh₂} → ¬ (∃[ dh₁′ ] dh₁′ ⋖ dh₁) → ¬ (∃[ dh₂′ ] dh₂′ ⋖ dh₂) → dh₁ ≡ dh₂
¬∃prev-unique ¬∃prev₁ ¬∃prev₂ with ¬∃prev⇒first ¬∃prev₁ | ¬∃prev⇒first ¬∃prev₂
... | refl | refl = refl

date-hour-unique : ∀ {dh₁ dh₂ n} → dh₁ HasOrdinal n → dh₂ HasOrdinal n → dh₁ ≡ dh₂
date-hour-unique {dh₁} {dh₂} {zero} ho₁ ho₂ with ordinal≡0⇒first ho₁ | ordinal≡0⇒first ho₂
... | refl | refl = refl
date-hour-unique {dh₁} {dh₂} {suc n} ho₁ ho₂ with suc-ordinal⇒∃prev ho₁ | suc-ordinal⇒∃prev ho₂
... | dh₁′ , dh₁′⋖dh₁ | dh₂′ , dh₂′⋖dh₂ with prev-ordinal dh₁′⋖dh₁ ho₁ | prev-ordinal dh₂′⋖dh₂ ho₂
... | ho₁′ | ho₂′ with date-hour-unique ho₁′ ho₂′
... | refl = next-unique dh₁′⋖dh₁ dh₂′⋖dh₂

module _ where
  open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; ≅-to-≡)

  private
    has-ordinal-irrelevant' : ∀ {dh n₁ n₂} → (p₁ : dh HasOrdinal n₁) → (p₂ : dh HasOrdinal n₂) → n₁ ≡ n₂ → p₁ ≅ p₂
    has-ordinal-irrelevant' {dh} (ordinal {ord₁} dho₁) (ordinal {ord₂} dho₂) eq with ord₁≡ord₂
      where
        ord₁≡ord₂ : ord₁ ≡ ord₂
        ord₁≡ord₂ = *-cancelʳ-≡ ord₁ ord₂ 24 (+-cancelˡ-≡ (Position.toℕ (Hour.position (DateHour.hour dh))) (ord₁ * 24) (ord₂ * 24) eq)
    ... | refl with D.has-ordinal-irrelevant dho₁ dho₂
    ... | refl = refl

  has-ordinal-irrelevant : ∀ {dh n} → (p₁ p₂ : dh HasOrdinal n) → p₁ ≡ p₂
  has-ordinal-irrelevant p₁ p₂ = ≅-to-≡ (has-ordinal-irrelevant' p₁ p₂ refl)
