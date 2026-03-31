module Gregorianum.Data.Cursor.Base where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _∸_)

data Cursor (width : ℕ) : ℕ → ℕ → Set where
  first : Cursor width 0 width
  suc : ∀ {acc rem} → Cursor width acc (suc rem) → Cursor width (suc acc) rem

inject-left : ∀ {width acc rem} → Cursor width acc rem → Cursor (suc width) (suc acc) rem
inject-left first = suc first
inject-left (suc x) = suc (inject-left x)

inject-right : ∀ {width acc rem} → Cursor width acc rem → Cursor (suc width) acc (suc rem)
inject-right first = first
inject-right (suc x) = suc (inject-right x)

last : ∀ {width} → Cursor width width 0
last {zero} = first
last {suc width} = inject-left last

fromℕ≤ : ∀ {width n} → n ≤ width → Cursor width n (width ∸ n)
fromℕ≤ z≤n = first
fromℕ≤ (s≤s n≤width) = inject-left (fromℕ≤ n≤width)

toℕ : ∀ {width acc rem} → Cursor width acc rem → ℕ
toℕ {acc} _ = acc
