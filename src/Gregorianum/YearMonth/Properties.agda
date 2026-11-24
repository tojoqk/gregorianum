module Gregorianum.YearMonth.Properties where

open import Gregorianum.YearMonth.Base

open import Gregorianum.Year as Y using (common₁; common₁₀₀)
open import Gregorianum.Year.Properties as Y using (year-type-unique; has-type-irrelevant)
open import Gregorianum.Year.Weight.Base using (weight)
open import Gregorianum.Year.Weight.Properties using (next-weight)
open import Gregorianum.Month as M hiding (_HasDays_)
open import Gregorianum.Data.Cursor using (first; suc)
open import Gregorianum.Data.Position using (mkPos)
import Gregorianum.Month.Properties as M

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (suc-injective; ≤-refl)
import Data.Nat.Induction as ℕ
open import Data.Product using (∃-syntax; _×_; _,_; proj₁)
open import Induction.WellFounded
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)
import Relation.Binary.Construct.On as On
open import Function using (_∘_)

⋖-irrelevant : ∀ {ym₁ ym₂} → (p₁ p₂ : ym₁ ⋖ ym₂) → p₁ ≡ p₂
⋖-irrelevant step-month step-month = refl
⋖-irrelevant (step-year p₁) (step-year p₂) with Y.⋖-irrelevant p₁ p₂
... | refl = refl

next-unique : ∀ {ym₁ ym₂ ym₃}
                     → ym₁ ⋖ ym₂
                     → ym₁ ⋖ ym₃
                     → ym₂ ≡ ym₃
next-unique step-month step-month = refl
next-unique (step-year p) (step-year q) with Y.next-unique p q
... | refl = refl

prev-unique : ∀ {ym₁ ym₂ ym₃}
                     → ym₁ ⋖ ym₃
                     → ym₂ ⋖ ym₃
                     → ym₁ ≡ ym₂
prev-unique step-month step-month = refl
prev-unique (step-year p) (step-year q) with Y.prev-unique p q
... | refl = refl

days-unique : ∀ {ym days₁ days₂}
               → ym HasDays days₁
               → ym HasDays days₂
               → days₁ ≡ days₂
days-unique (mkHasDays _ M.january-days) (mkHasDays _ M.january-days) = refl
days-unique (mkHasDays _ M.february-common-days) (mkHasDays _ M.february-common-days) = refl
days-unique (mkHasDays common₁ M.february-common-days) (mkHasDays () M.february-leap-days)
days-unique (mkHasDays common₁₀₀ M.february-common-days) (mkHasDays () M.february-leap-days)
days-unique (mkHasDays _ M.february-leap-days) (mkHasDays _ M.february-leap-days) = refl
days-unique (mkHasDays () M.february-leap-days) (mkHasDays common₁ M.february-common-days)
days-unique (mkHasDays () M.february-leap-days) (mkHasDays common₁₀₀ M.february-common-days)
days-unique (mkHasDays _ M.march-days) (mkHasDays _ M.march-days) = refl
days-unique (mkHasDays _ M.april-days) (mkHasDays _ M.april-days) = refl
days-unique (mkHasDays _ M.may-days) (mkHasDays _ M.may-days) = refl
days-unique (mkHasDays _ M.june-days) (mkHasDays _ M.june-days) = refl
days-unique (mkHasDays _ M.july-days) (mkHasDays _ M.july-days) = refl
days-unique (mkHasDays _ M.august-days) (mkHasDays _ M.august-days) = refl
days-unique (mkHasDays _ M.september-days) (mkHasDays _ M.september-days) = refl
days-unique (mkHasDays _ M.october-days) (mkHasDays _ M.october-days) = refl
days-unique (mkHasDays _ M.november-days) (mkHasDays _ M.november-days) = refl
days-unique (mkHasDays _ M.december-days) (mkHasDays _ M.december-days) = refl

has-days-irrelevant : ∀ {ym days} → (p q : ym HasDays days) → p ≡ q
has-days-irrelevant (mkHasDays hasYearType₁ hasDays₁) (mkHasDays hasYearType₂ hasDays₂) with year-type-unique hasYearType₁ hasYearType₂
... | refl with has-type-irrelevant hasYearType₁ hasYearType₂ | M.has-days-irrelevant hasDays₁ hasDays₂
... | refl | refl = refl

<-WellFounded : WellFounded _<_
<-WellFounded ym = On.accessible (proj₁ ∘ toOrdinal) (ℕ.<-wellFounded-fast (proj₁ (toOrdinal ym)))

next-ordinal : ∀ {ym₁ ym₂ n} → ym₁ ⋖ ym₂ → ym₁ HasOrdinal n → ym₂ HasOrdinal (suc n)
next-ordinal (step-year {y₁} {y₂} y₁⋖y₂) (ordinal Y.ordinal) with Y.next-ordinal y₁⋖y₂ Y.ordinal
...                                                                         | h = ordinal h
next-ordinal (step-month {y} {ac} {rm} {c}) (ordinal {n} Y.ordinal) = ordinal Y.ordinal

⋖⇒suc : ∀ {ym₁ ym₂} → ym₁ ⋖ ym₂ → ∃[ n ] (ym₁ HasOrdinal n) × (ym₂ HasOrdinal (suc n))
⋖⇒suc ym₁⋖ym₂ with next-ordinal ym₁⋖ym₂ (ordinal Y.ordinal)
... | h = _ , ((ordinal Y.ordinal) , h)

ordinal-unique : ∀ {ym n₁ n₂} → ym HasOrdinal n₁ → ym HasOrdinal n₂ → n₁ ≡ n₂
ordinal-unique (ordinal Y.ordinal) (ordinal Y.ordinal) = refl

¬∃prev⇒first : ∀ {ym} → ¬ (∃[ ym′ ] ym′ ⋖ ym) → ym ≡ (zero Y.′ mkPos first ″ mkPos first ‴ mkPos first) - january
¬∃prev⇒first {y - january} ¬∃prev with Y.prev? y
... | yes (y′ , y′⋖y) = contradiction ((y′ - december) , step-year y′⋖y) ¬∃prev
... | no y-¬∃prev with Y.¬∃prev⇒first y-¬∃prev
... | refl = refl
¬∃prev⇒first {y - [ mkPos (suc c) ]} ¬∃prev = contradiction ((y - [ mkPos c ]) , step-month) ¬∃prev

first-ordinal≡zero : ∀ {n} → year-month-first HasOrdinal n → n ≡ 0
first-ordinal≡zero p with ordinal-unique p (ordinal Y.ordinal)
... | refl = refl

suc-ordinal⇒∃prev : ∀ {ym n} → ym HasOrdinal (suc n) → ∃[ ym′ ] ym′ ⋖ ym
suc-ordinal⇒∃prev {ym} p with prev? ym
... | yes (ym′ , ym′⋖ym) = ym′ , ym′⋖ym
... | no ¬∃prev with ¬∃prev⇒first ¬∃prev
... | refl with first-ordinal≡zero p
... | ()

∃prev⇒suc-ordinal : ∀ {ym} → ∃[ ym′ ] ym′ ⋖ ym → ∃[ n ] ym HasOrdinal (suc n)
∃prev⇒suc-ordinal (_ , step-month) = _ , ordinal Y.ordinal
∃prev⇒suc-ordinal (ym′ , step-year y′⋖y) with Y.∃prev⇒suc-ordinal (_ , y′⋖y)
... | _ , ho = _ , ordinal ho

¬∃prev-unique : ∀ {d₁ d₂} → ¬ (∃[ d′ ] d′ ⋖ d₁) → ¬ (∃[ d′ ] d′ ⋖ d₂) → d₁ ≡ d₂
¬∃prev-unique ¬∃prev₁ ¬∃prev₂ with ¬∃prev⇒first ¬∃prev₁ | ¬∃prev⇒first ¬∃prev₂
... | refl | refl = refl

prev-ordinal : ∀ {ym₁ ym₂ n} → ym₁ ⋖ ym₂ → ym₂ HasOrdinal (suc n) → ym₁ HasOrdinal n
prev-ordinal ym₁⋖ym₂ p with ⋖⇒suc ym₁⋖ym₂
... | _ , q , p' with ordinal-unique p p'
... | refl = q

⋖⇒< : ∀ {ym₁ ym₂} → ym₁ ⋖ ym₂ → ym₁ < ym₂
⋖⇒< {ym₁} {ym₂} p with ⋖⇒suc p | toOrdinal ym₁ | toOrdinal ym₂
... | n , ep₁ , ep₂ | n₁ , ordinal _ | n₂ , ordinal _ with ordinal-unique ep₁ (ordinal Y.ordinal) | ordinal-unique ep₂ (ordinal Y.ordinal)
... | eq₁ | eq₂ rewrite sym eq₁ | sym eq₂ = ≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded y = Subrelation.accessible ⋖⇒< (<-WellFounded y)

ordinal≡0⇒first : ∀ {ym} → ym HasOrdinal 0 → ym ≡ year-month-first
ordinal≡0⇒first {ym} p with prev? ym
ordinal≡0⇒first {ym} p | yes isSuc with ∃prev⇒suc-ordinal isSuc
... | fst , snd with ordinal-unique snd p
... | ()
ordinal≡0⇒first {ym} p | no q with ¬∃prev⇒first q
ordinal≡0⇒first {ym} p | no q | refl = refl

year-month-unique : ∀ {ym₁ ym₂ n} → ym₁ HasOrdinal n → ym₂ HasOrdinal n → ym₁ ≡ ym₂
year-month-unique {ym₁} {ym₂} {zero} p q rewrite ordinal≡0⇒first p | ordinal≡0⇒first q = refl
year-month-unique {ym₁} {ym₂} {suc n} p q with suc-ordinal⇒∃prev p | suc-ordinal⇒∃prev q
... | ym₁′ , ym₁′⋖ym₁ | ym₂′ , ym₂′⋖ym₂ with ⋖⇒suc ym₁′⋖ym₁ | ⋖⇒suc ym₂′⋖ym₂
... | n₁′ , h₁′ , h₁ | n₂′ , h₂′ , h₂ with ordinal-unique h₁ p | ordinal-unique h₂ q
... | refl | refl with year-month-unique h₁′ h₂′
... | refl = next-unique ym₁′⋖ym₁ ym₂′⋖ym₂

module _ where
  open import Relation.Binary.HeterogeneousEquality using (_≅_; refl; ≅-to-≡)

  private
    has-ordinal-irrelevant' : ∀ {ym n₁ n₂} → (p₁ : ym HasOrdinal n₁) → (p₂ : ym HasOrdinal n₂) → n₁ ≡ n₂ → p₁ ≅ p₂
    has-ordinal-irrelevant' (ordinal Y.ordinal) (ordinal Y.ordinal) refl = refl

  has-ordinal-irrelevant : ∀ {ym n} → (p₁ p₂ : ym HasOrdinal n) → p₁ ≡ p₂
  has-ordinal-irrelevant p₁ p₂ = ≅-to-≡ (has-ordinal-irrelevant' p₁ p₂ refl)
