module Gregorianum.YearMonth.Path where

open import Gregorianum.YearMonth.Base

open import Gregorianum.Year.Base
open import Gregorianum.Year.Properties as Y
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position
import Gregorianum.Data.Cursor.Properties as Cursor
import Gregorianum.Year.Path as Y
import Gregorianum.Data.Cursor.Position.Path as P
import Gregorianum.Data.Cursor.Position.Path.Properties as P
open import Data.Nat using (ℕ; suc; zero; _+_; _*_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym; module ≡-Reasoning) renaming (trans to ≡-trans)
import Data.Nat.Properties as ℕ
open import Data.Nat.Solver using (module +-*-Solver)

data _─[_]→_ (x : YearMonth) : ℕ → YearMonth → Set where
  ε : x ─[ zero ]→ x
  month→ : ∀ {y lenᵐ len}
          → x .YearMonth.year ≡ y .YearMonth.year
          → x .YearMonth.month P.─[ suc lenᵐ ]→ y .YearMonth.month
          → len ≡ suc lenᵐ
          → x ─[ len ]→ y
  year→ : ∀ {y pre lenʸ post len}
          → x .YearMonth.month P.─[ pre ]→ mkPos last
          → x .YearMonth.year Y.─[ suc lenʸ ]→ y .YearMonth.year
          → mkPos first P.─[ post ]→ y .YearMonth.month
          → len ≡ suc (pre + lenʸ * 12 + post)
          → x ─[ len ]→ y

private
  identity : ∀ {x y} → x ≡ y → x ─[ zero ]→ y
  identity refl = ε

  identity⁻¹ : ∀ {x y} → x ─[ zero ]→ y → x ≡ y
  identity⁻¹ ε = refl

  trans : ∀ {x y z len₁ len₂}
        → x ─[ len₁ ]→ y
        → y ─[ len₂ ]→ z
        → x ─[ len₁ + len₂ ]→ z
  trans ε y→z = y→z
  trans (month→ {lenᵐ = lenᵐ} refl m→ refl) (year→ {pre = pre} {lenʸ = lenʸ} {post = post} pre→ y→ post→ refl) =
        year→ (P.trans m→ pre→) y→ post→ (begin
          suc lenᵐ + suc (pre + lenʸ * 12 + post)
        ≡⟨ cong suc (ℕ.+-suc lenᵐ _) ⟩
          suc (suc (lenᵐ + (pre + lenʸ * 12 + post)))
        ≡⟨ cong (λ x → (suc (suc x))) (sym (ℕ.+-assoc lenᵐ (pre + lenʸ * 12) post))  ⟩
          suc (suc (lenᵐ + (pre + lenʸ * 12) + post))
        ≡⟨ cong (λ x → (suc (suc (x + post)))) (sym (ℕ.+-assoc lenᵐ pre (lenʸ * 12))) ⟩
          suc (suc lenᵐ + pre + lenʸ * 12 + post)
        ∎)
    where open ≡-Reasoning
  trans (month→ refl p refl) ε = month→ refl p (cong suc (ℕ.+-identityʳ _))
  trans (month→ refl p refl) (month→ refl q refl) = month→ refl (P.trans p q) refl
  trans (year→ x x₁ p refl) ε = year→ x x₁ p (ℕ.+-identityʳ _)
  trans (year→ {pre = pre} {lenʸ = lenʸ} {post = post} p y→ q refl) (month→ {lenᵐ = lenᵐ} refl x₃ refl) = year→ p y→ (P.trans q x₃) (begin
      (suc (pre + lenʸ * 12) + post) + suc lenᵐ
    ≡⟨ ℕ.+-assoc (suc (pre + lenʸ * 12)) post (suc lenᵐ) ⟩
      suc (pre + lenʸ * 12 + (post + suc lenᵐ))
    ∎)
    where open ≡-Reasoning
  trans {x} {y} {z} (year→ {pre = pre₁} {lenʸ = lenʸ₁} {post = post₁} pre→₁ y₁→ post→₁ refl)
        (year→ {pre = pre₂} {lenʸ = lenʸ₂} {post = post₂} pre→₂ y₂→ post→₂ refl) =
        year→ pre→₁ (Y.trans y₁→ y₂→) post→₂ (begin
          ((suc pre₁ + lenʸ₁ * 12) + post₁) + ((suc pre₂ + lenʸ₂ * 12) + post₂)
        ≡⟨ solve 6 (λ pre₁ lenʸ₁ post₁ pre₂ lenʸ₂ post₂ →
                      ((con 1 :+ pre₁ :+ lenʸ₁ :* con 12) :+ post₁) :+ ((con 1 :+ pre₂ :+ lenʸ₂ :* con 12) :+ post₂) :=
                      (con 1 :+ pre₁ :+ lenʸ₁ :* con 12) :+ ((con 1 :+ (post₁ :+ pre₂)) :+ ((lenʸ₂ :* con 12) :+ post₂)))
                   refl
                   pre₁ lenʸ₁ post₁ pre₂ lenʸ₂ post₂ ⟩
          (suc pre₁ + lenʸ₁ * 12) + ((suc (post₁ + pre₂)) + ((lenʸ₂ * 12) + post₂))
        ≡⟨ cong (λ e → (suc pre₁ + lenʸ₁ * 12) + (suc e + ((lenʸ₂ * 12) + post₂))) (P.from-first-len (P.trans post→₁ pre→₂)) ⟩
          (suc pre₁ + lenʸ₁ * 12) + (12 + ((lenʸ₂ * 12) + post₂))
        ≡⟨ solve 4 (λ pre₁ lenʸ₁ lenʸ₂ post₂ →
                      (con 1 :+ pre₁ :+ lenʸ₁ :* con 12) :+ (con 12 :+ ((lenʸ₂ :* con 12) :+ post₂)) :=
                      con 1 :+ (pre₁ :+ (lenʸ₁ :+ (con 1 :+ lenʸ₂)) :* con 12 :+ post₂))
                 refl pre₁ lenʸ₁ lenʸ₂ post₂ ⟩
          suc (pre₁ + (lenʸ₁ + suc lenʸ₂) * 12 + post₂)
        ∎)
    where open ≡-Reasoning
          open +-*-Solver
