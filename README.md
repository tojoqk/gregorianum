# Gregorianum

**Gregorianum** is a formally verified, correct-by-construction library for the Proleptic Gregorian Calendar, implemented in Agda.

Unlike traditional libraries that rely on runtime validation, Gregorianum encodes the structural laws of the calendar—such as month lengths, leap years, and era transitions—directly into the type system.


## Structural Elegance of `Day`

The heart of Gregorianum is the `Day` type. It is not merely a wrapper for an integer; it is a type-level representation of a day's **Successor Capacity**.


### 1. Successor Capacity and Remainder

A `Day` is indexed by its capacity (`cap`), the number of days already passed (`acc`), and the **remaining successor applications** (`rem`) within a month.

```agda
data Day (cap : ℕ) : (acc rem : ℕ) → Set where
  1st : Day cap zero cap
  suc : ∀ {acc rem} → Day cap acc (suc rem) → Day cap (suc acc) rem
```

This indexing makes the **"end-of-month"** a type-level state (`rem ≡ 0`). By identifying this state, the library can distinguish between an internal transition (same month) and a boundary transition (next month) with absolute logical certainty.


### 2. The Inductive Nature of `last`

The "last day" of any month is not defined by numerical constants, but by a recursive proof using structural induction:

```agda
last : ∀ {cap} → Day cap cap 0
last {zero}  = 1st
last {suc _} = injectˡ last
```

By using `injectˡ`, the library derives the end of a month of any length as a structural property, ensuring that `prevDay` logic is always grounded in the month's actual capacity.

## The Date Type and Adjacency

Atop the `Day` type lies the `Date` record and a formal adjacency relation `_⋖_`. This relation defines the legal "next day" logic as a type-level specification.

### 1. The `Date` Record

A `Date` is a dependent record where the `YearMonth` dictates the legal capacity of the `Day`.

```agda
record Date : Set where
  constructor _-_
  field
    {cap}     : ℕ
    year-month : YearMonth (suc cap) -- suc cap ≡ days
    {acc} : ℕ
    {rem} : ℕ
    day : Day cap acc rem

  open YearMonth year-month public
```

### 2. Adjacency

We define what it means for one date to succeed another using a data type. This captures the logic of the calendar as a set of logical rules:

```agda
data _⋖_ : Date → Date → Set where
  step : ∀ {cap acc rem} {ym : YearMonth (suc cap)}
       → (d : Day cap acc (suc rem))
       → (ym - d) ⋖ (ym - suc d)
  step-month : ∀ {cap₁ cap₂} {ym₁ : YearMonth (suc cap₁)} {ym₂ : YearMonth (suc cap₂)}
             → (d : Day cap₁ cap₁ 0)
             → ym₁ YM.⋖ ym₂
             → (ym₁ - d) ⋖ (ym₂ - 1st)
```

The `nextDay` function is a projection from an existence proof (`next-day-exists`), ensuring that transitions are total and always land on a valid date.


## Key Features

-   **Correct-by-Construction Transitions**: `nextDay` and `prevDay` are derived from existence proofs (`next-day-exists`). They are **total functions** that seamlessly handle month boundaries, leap years.
-   **Proof Irrelevance**: Internal witnesses (such as leap year proofs) are proven irrelevant. This ensures that date equality (`_≡_`) behaves intuitively, based only on calendar values, without being hindered by underlying proof structures.
-   **Proleptic Support**: Full support for dates in the deep past and far future using arbitrary-precision integers (`ℤ`).
-   **Decidable Interface**: Conversion from raw integers to verified `Date` types is **decidable**. Using the `True` witness pattern, you can construct verified dates with elegant syntax.


## Usage

```agda
open import Gregorianum.Date

-- Compile-time verified dates via decidable predicates
today : Date
today = ⟨+ 2024 - 2 - 23 ⟩

-- Leap years are handled automatically; 2024-02-29 is valid
leapDay : Date
leapDay = ⟨+ 2024 - 2 - 29 ⟩

-- This would result in a compile-time error:
-- invalidDay : Date
-- invalidDay = ⟨+ 2025 - 2 - 29 ⟩ 

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Safe, total transitions guaranteed by existence proofs
_ : nextDay today ≡ ⟨+ 2024 - 2 - 24 ⟩
_ = refl

_ : prevDay today ≡ ⟨+ 2024 - 2 - 22 ⟩
_ = refl

_ : nextDay leapDay ≡ ⟨+ 2024 - 3 - 1 ⟩
_ = refl

_ : prevDay ⟨+ 2024 - 3 - 1 ⟩ ≡ leapDay
_ = refl

_ : nextDay ⟨+ 2024 - 12 - 31 ⟩ ≡ ⟨+ 2025 - 1 - 1 ⟩
_ = refl

_ : prevDay ⟨+ 2025 - 1 - 1 ⟩ ≡ ⟨+ 2024 - 12 - 31 ⟩
_ = refl
```


## Project Structure

-   `Gregorianum.Date`: Core verified date types and total transitions.
-   `Gregorianum.Day`: The `Day` type indexed by successor capacity.
-   `Gregorianum.YearMonth`: Logic for month capacities and year-type dependencies.
-   `Gregorianum.Law.Leap`: Formal logic and irrelevance proofs for leap years.
-   `Gregorianum.Date.Plain`: Decidable conversion between raw data and verified types.


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
