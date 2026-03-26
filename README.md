# Gregorianum

**Gregorianum** is a formally verified, correct-by-construction library for the Proleptic Gregorian Calendar, implemented in Agda.

Unlike traditional libraries that rely on runtime validation, Gregorianum encodes the structural laws of the calendar—such as month lengths, leap years, and era transitions—directly into the type system.

## Core Abstractions: `Cursor` and `Position`

The heart of Gregorianum is the `Cursor`, which replaces raw integers with a type that guarantees boundary conditions.

### 1. Boundary-Safe `Cursor`
`Cursor width acc rem` is indexed by the total width (`width`), the number of elements passed (`acc`), and the number of elements remaining (`rem`). Consequently, **"boundaries" (such as the end of a month or year) are not mere value comparisons but are expressed as type-level states (`rem ≡ 0`).**

```agda
data Cursor (width : ℕ) : ℕ → ℕ → Set where
  zero : Cursor width 0 width
  suc  : ∀ {acc rem} → Cursor width acc (suc rem) → Cursor width (suc acc) rem
```

### 2. Structured `Year`
To handle the complexities of Gregorian leap year rules, a `Year` is defined not as a simple number, but as a record that structures the 400-year cycle.

```agda
record Year : Set where
  field
    quadricentennial : ℕ        -- Count of 400-year cycles
    pos₁₀₀ : Position 3         -- 100-year position (0-3)
    pos₄   : Position 24        -- 4-year position (0-24)
    pos₁   : Position 3         -- 1-year position (0-3)
```
With this structure, leap year logic (divisibility by 400, 100, and 4) is naturally described through type-level pattern matching.

## Linear Ordering and Paths

Gregorianum treats dates not as isolated data points, but as a **linearly ordered set connected by "Paths."**

### 1. Adjacency `_⋖_`
The relationship between a date `d1` and its immediate successor `d2` is defined by the `d1 ⋖ d2` data type. This specification covers all "valid transitions," including month rollovers and leap year logic.

### 2. Paths between dates `_─[ n ]→_`
An interval of `n` days between two dates is defined as the transitive closure of the adjacency relation (a path of length `n`). This allows for the formal proof of the following properties:
- **Acyclicity**: If `d ─[ n ]→ d`, then `n ≡ 0`. Dates never loop.
- **Totality**: For any two dates `d1` and `d2`, it is decidable whether one precedes the other or they are identical.

## Key Features

- **Type-Level Correctness**: Functions like `nextDate` and `forward` are total functions based on proofs of existence. It is logically impossible to generate an invalid date.
- **Decidable Interface**: The conversion from a simple numeric tuple `(y, m, d)` to a verified `Date` type is `Dec` (decidable). You can write dates verified at compile-time using the elegant syntax `⟨ 2026 - 3 - 23 ⟩`.
- **Mapping to Ordinals**: The `toOrdinal` function maps dates to the number line (`ℕ`), enabling mathematically rigorous date comparisons and arithmetic.

## Usage Examples

```agda
module Gregorianum.Examples where

open import Gregorianum.Date
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Compile-time verified dates via decidable predicates
_ : Date
_ = ⟨ 2026 - 3 - 23 ⟩

-- Leap years are handled automatically; 2024-02-29 is valid
_ : Date
_ = ⟨ 2024 - 2 - 29 ⟩

-- This would result in a compile-time error:
-- invalidDay : Date
-- invalidDay = ⟨ 2026 - 2 - 29 ⟩

_ : proj₁ (nextDate ⟨ 2024 - 2 - 29 ⟩) ≡ ⟨ 2024 - 3 - 1 ⟩
_ = refl

_ : ⟨ 2024 - 2 - 29 ⟩ ⋖ ⟨ 2024 - 3 - 1 ⟩
_ = proj₂ (nextDate ⟨ 2024 - 2 - 29 ⟩)

_ : proj₁ (from-yes (prevDate? ⟨ 2024 - 3 - 1 ⟩)) ≡ ⟨ 2024 - 2 - 29 ⟩
_ = refl

_ : ⟨ 2024 - 2 - 29 ⟩ ⋖ ⟨ 2024 - 3 - 1 ⟩
_ = proj₂ (from-yes (prevDate? ⟨ 2024 - 3 - 1 ⟩))

_ : ⟨ 2024 - 12 - 31 ⟩ ⋖ ⟨ 2025 - 1 - 1 ⟩
_ = proj₂ (nextDate ⟨ 2024 - 12 - 31 ⟩)

_ : ⟨ 2024 - 12 - 31 ⟩ ⋖ ⟨ 2025 - 1 - 1 ⟩
_ = proj₂ (from-yes (prevDate? ⟨ 2025 - 1 - 1 ⟩))

_ : proj₁ (forward ⟨ 2024 - 2 - 22 ⟩ 366) ≡ ⟨ 2025 - 2 - 22 ⟩
_ = refl

_ : ⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→ ⟨ 2025 - 2 - 22 ⟩
_ = proj₂ (forward ⟨ 2024 - 2 - 22 ⟩ 366)

_ : ⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→ ⟨ 2025 - 2 - 22 ⟩
_ = proj₂ (from-yes (backward? ⟨ 2025 - 2 - 22 ⟩ 366))

_ : ⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→ ⟨ 2025 - 2 - 22 ⟩
_ = from-yes (⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→? ⟨ 2025 - 2 - 22 ⟩)

_ : ⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→ ⟨ 2025 - 2 - 22 ⟩
_ = from-yes (⟨ 2024 - 2 - 22 ⟩ ─[ 366 ]→? ⟨ 2025 - 2 - 22 ⟩)
```

## Project Structure

- `Gregorianum.Date`: Core verified date types and total transitions.
- `Gregorianum.Year`: Structured year definitions based on the 400-year cycle.
- `Gregorianum.YearMonth`: Logic for month capacities and year-type dependencies.
- `Gregorianum.Data.Cursor`: Core data structures for managing boundary conditions.
- `Gregorianum.Date.Path`: Path theory for treating dates as a linearly ordered set.
- `Gregorianum.Date.Plain`: Decidable conversion between raw data and verified types.

## Installation

1.  Clone the repository:
    ```shell
    git clone https://github.com/tojoqk/gregorianum.git
    ```
2.  Register the library in your `~/.agda/libraries`:
    ```text
    /path/to/gregorianum/gregorianum.agda-lib
    ```
3.  Add `gregorianum` to your project's `.agda-lib` dependencies.

## Development Environment

-   **Agda**: 2.8.0
-   **standard-library**: v2.3

Older versions of Agda or the standard library may work, but they are currently untested.

## License

MIT
