module Gregorianum.Data.Cursor.Base where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _∸_)

data Cursor (width : ℕ) : ℕ → ℕ → Set where
  zero : Cursor width 0 width
  suc : ∀ {acc rem} → Cursor width acc (suc rem) → Cursor width (suc acc) rem

injectˡ : ∀ {width acc rem} → Cursor width acc rem → Cursor (suc width) (suc acc) rem
injectˡ zero = suc zero
injectˡ (suc x) = suc (injectˡ x)

injectʳ : ∀ {width acc rem} → Cursor width acc rem → Cursor (suc width) acc (suc rem)
injectʳ zero = zero
injectʳ (suc x) = suc (injectʳ x)

last : ∀ {width} → Cursor width width 0
last {zero} = zero
last {suc width} = injectˡ last

fromℕ≤ : ∀ {width n} → n ≤ width → Cursor width n (width ∸ n)
fromℕ≤ z≤n = zero
fromℕ≤ (s≤s n≤width) = injectˡ (fromℕ≤ n≤width)

toℕ : ∀ {width acc rem} → Cursor width acc rem → ℕ
toℕ {acc} _ = acc
