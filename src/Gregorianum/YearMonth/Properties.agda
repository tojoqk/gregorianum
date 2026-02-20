module Gregorianum.YearMonth.Properties where

open import Gregorianum.YearMonth
open import Gregorianum.Month

open import Gregorianum.Year as Y using (_th⟨_⟩)
open import Gregorianum.Year.Properties using (next-year-unique; has-year-type-irrelevant; next-year-exists)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)

has-days-irrelevant : ∀ {my n}
                    → (p q : my HasDays n)
                    → p ≡ q
has-days-irrelevant january january = refl
has-days-irrelevant february-common february-common = refl
has-days-irrelevant february-leap february-leap = refl
has-days-irrelevant march march = refl
has-days-irrelevant april april = refl
has-days-irrelevant may may = refl
has-days-irrelevant june june = refl
has-days-irrelevant july july = refl
has-days-irrelevant august august = refl
has-days-irrelevant september september = refl
has-days-irrelevant october october = refl
has-days-irrelevant november november = refl
has-days-irrelevant december december = refl

days-unique : ∀ {ym} {m n : ℕ}
                → ym HasDays m
                → ym HasDays n
                → m ≡ n
days-unique january january = refl
days-unique february-common february-common = refl
days-unique february-leap february-leap = refl
days-unique march march = refl
days-unique april april = refl
days-unique may may = refl
days-unique june june = refl
days-unique july july = refl
days-unique august august = refl
days-unique september september = refl
days-unique october october = refl
days-unique november november = refl
days-unique december december = refl

next-days-unique : ∀ {n₁ n₂ n₃}
                 → { ym₁ : YearMonth n₁}
                 → { ym₂ : YearMonth n₂}
                 → { ym₃ : YearMonth n₃}
                 → ym₁ ⋖ ym₂
                 → ym₁ ⋖ ym₃
                 → n₂ ≡ n₃
next-days-unique january-feburary-common january-feburary-common = refl
next-days-unique january-feburary-leap january-feburary-leap = refl
next-days-unique february-common-march february-common-march = refl
next-days-unique february-leap-march february-leap-march = refl
next-days-unique march-april march-april = refl
next-days-unique april-may april-may = refl
next-days-unique may-june may-june = refl
next-days-unique june-july june-july = refl
next-days-unique july-august july-august = refl
next-days-unique august-september august-september = refl
next-days-unique september-october september-october = refl
next-days-unique october-november october-november = refl
next-days-unique november-december november-december = refl
next-days-unique (december-january _) (december-january _) = refl

next-year-month-unique : ∀ {n n'}
                       → { ym₁ : YearMonth n }
                       → { ym₂ : YearMonth n'}
                       → { ym₃ : YearMonth n'}
                       → ym₁ ⋖ ym₂
                       → ym₁ ⋖ ym₃
                       → ym₂ ≡ ym₃
next-year-month-unique january-feburary-common january-feburary-common = refl
next-year-month-unique january-feburary-leap january-feburary-leap = refl
next-year-month-unique february-common-march february-common-march = refl
next-year-month-unique february-leap-march february-leap-march = refl
next-year-month-unique march-april march-april = refl
next-year-month-unique april-may april-may = refl
next-year-month-unique may-june may-june = refl
next-year-month-unique june-july june-july = refl
next-year-month-unique july-august july-august = refl
next-year-month-unique august-september august-september = refl
next-year-month-unique september-october september-october = refl
next-year-month-unique october-november october-november = refl
next-year-month-unique november-december november-december = refl
next-year-month-unique {ym₂ = ((_ th⟨ p₂ ⟩) / _ ⟨ _ ⟩)} {ym₃ = ((_ th⟨ p₃ ⟩) / _ ⟨ _ ⟩)} (december-january y₁⋖y₂) (december-january y₁⋖y₃)
                       with next-year-unique y₁⋖y₂ y₁⋖y₃
...                       | refl , refl with has-year-type-irrelevant p₂ p₃
...                                        | refl = refl

next-year-month-exists : ∀ {n} (ym : YearMonth n) → ∃[ n' ] Σ[ ym' ∈ YearMonth n' ] ym ⋖ ym'
next-year-month-exists (year / march ⟨ march ⟩) = 30 , (year / april ⟨ april ⟩) , march-april
next-year-month-exists (year / april ⟨ april ⟩) = 31 , (year / may ⟨ may ⟩) , april-may
next-year-month-exists (year / may ⟨ may ⟩) = 30 , (year / june ⟨ june ⟩) , may-june
next-year-month-exists (year / june ⟨ june ⟩) = 31 , (year / july ⟨ july ⟩) , june-july
next-year-month-exists (year / july ⟨ july ⟩) = 31 , (year / august ⟨ august ⟩) , july-august
next-year-month-exists (year / august ⟨ august ⟩) = 30 , (year / september ⟨ september ⟩) , august-september
next-year-month-exists (year / september ⟨ september ⟩) = 31 , (year / october ⟨ october ⟩) , september-october
next-year-month-exists (year / october ⟨ october ⟩) = 30 , (year / november ⟨ november ⟩) , october-november
next-year-month-exists (year / november ⟨ november ⟩) = 31 , (year / december ⟨ december ⟩) , november-december
next-year-month-exists (year / december ⟨ december ⟩) with next-year-exists year
...                                                      | _ , y , p = 31 , (y / january ⟨ january ⟩) , december-january p
next-year-month-exists ((year th⟨ Y.common x ⟩) / january ⟨ january ⟩) = 28 , (((year th⟨ Y.common x ⟩) / february ⟨ february-common ⟩) , january-feburary-common)
next-year-month-exists ((year th⟨ Y.leap x ⟩) / january ⟨ january ⟩) = 29 , ((year th⟨ Y.leap x ⟩) / february ⟨ february-leap ⟩) , january-feburary-leap
next-year-month-exists (year / february ⟨ february-common ⟩) = 31 , (year / march ⟨ march ⟩) , february-common-march
next-year-month-exists (year / february ⟨ february-leap ⟩) = 31 , (year / march ⟨ march ⟩) , february-leap-march
