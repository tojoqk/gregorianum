module Gregorianum.YearMonth.Plain where

open import Gregorianum.YearMonth.Base
open import Gregorianum.Year.Base using (YearType; common; leap)
open import Gregorianum.Month.Base
import Gregorianum.Year.Plain as Y
import Gregorianum.Month.Plain as M

open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data _HasPlain_ {days} (ym : YearMonth days) : (ℤ × ℕ) → Set where
  plain : ∀ {y m}
        → (YearMonth.year ym) Y.HasPlain y
        → (YearMonth.month ym) M.HasPlain m
        → ym HasPlain (y , m)

toPlain : ∀ {days} → YearMonth days → ℤ × ℕ
toPlain (year / month ⟨ _ ⟩) = (Y.toPlain year) , (M.toPlain month)

fromPlain? : (tup : ℤ × ℕ) → Dec (∃[ days ] Σ[ ym ∈ YearMonth days ] ym HasPlain tup)
fromPlain? (y , m) with Y.fromPlain y | M.fromPlain? m
... | yt , year | no ¬p = no λ { (_ , ym , plain _ p) → ¬p (YearMonth.month ym , p)}
... | yt , y' , Y.plain refl | yes (january , M.january) = yes (31 , (y' / january ⟨ january ⟩) , plain (Y.plain refl) M.january)
... | common , year , Y.plain refl | yes (february , M.february) = yes (28 , (year / february ⟨ february-common ⟩) , plain (Y.plain refl) M.february)
... | leap , year , Y.plain refl | yes (february , M.february) = yes (29 , (year / february ⟨ february-leap ⟩) , plain (Y.plain refl) M.february)
... | yt , year , Y.plain refl | yes (march , M.march) = yes (31 , (year / march ⟨ march ⟩) , plain (Y.plain refl) M.march)
... | yt , year , Y.plain refl | yes (april , M.april) = yes (30 , (year / april ⟨ april ⟩) , plain (Y.plain refl) M.april)
... | yt , year , Y.plain refl | yes (may , M.may) =  yes (31 , (year / may ⟨ may ⟩) , plain (Y.plain refl) M.may)
... | yt , year , Y.plain refl | yes (june , M.june) = yes (30 , (year / june ⟨ june ⟩) , plain (Y.plain refl) M.june)
... | yt , year , Y.plain refl | yes (july , M.july) = yes (31 , (year / july ⟨ july ⟩) , plain (Y.plain refl) M.july)
... | yt , year , Y.plain refl | yes (august , M.august) = yes (31 , (year / august ⟨ august ⟩) , plain (Y.plain refl) M.august)
... | yt , year , Y.plain refl | yes (september , M.september) = yes (30 , (year / september ⟨ september ⟩) , plain (Y.plain refl) M.september)
... | yt , year , Y.plain refl | yes (october , M.october) = yes (31 , (year / october ⟨ october ⟩) , plain (Y.plain refl) M.october)
... | yt , year , Y.plain refl | yes (november , M.november) = yes (30 , (year / november ⟨ november ⟩) , plain (Y.plain refl) M.november)
... | yt , year , Y.plain refl | yes (december , M.december) = yes (31 , (year / december ⟨ december ⟩) , plain (Y.plain refl) M.december)
