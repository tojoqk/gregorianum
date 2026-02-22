module Gregorianum.Day where

open import Data.Nat using (ℕ; suc; zero)

data Day (cap : ℕ) : (acc rem : ℕ) → Set where
  1st : Day cap zero cap
  suc : ∀ {acc rem} → Day cap acc (suc rem) → Day cap (suc acc) rem

injectˡ : ∀ {cap acc rem} → Day cap acc rem → Day (suc cap) (suc acc) rem
injectˡ 1st = suc 1st
injectˡ (suc d) = suc (injectˡ d)

injectʳ : ∀ {cap acc rem} → Day cap acc rem → Day (suc cap) acc (suc rem)
injectʳ 1st = 1st
injectʳ (suc d) = suc (injectʳ d)

last : ∀ {cap} →  Day cap cap 0
last {zero} = 1st
last {suc _} = injectˡ last
