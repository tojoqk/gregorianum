module Gregorianum.Relation.Step (A : Set) (_⋖_ : A → A → Set) where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; <-cmp; s≤s; _≟_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Relation.Nullary.Negation using (¬_)
import Induction.WellFounded as WF

record IsStep : Set₁ where
  field
    IsSuc : A → Set
    isSuc? : (x : A) → Dec (IsSuc x)
    ¬isSuc-unique : ∀ {x y} → ¬ IsSuc x → ¬ IsSuc y → x ≡ y
    next : (x : A) → ∃[ y ] x ⋖ y
    prev : (y : A) → IsSuc y → ∃[ x ] x ⋖ y
    next-unique : ∀ {x y z} → x ⋖ y → x ⋖ z → y ≡ z
    prev-unique : ∀ {x y z} → x ⋖ z → y ⋖ z → x ≡ y
    ⋖-wellFounded : WF.WellFounded _⋖_

module Path (isStep : IsStep) where
  open IsStep isStep

  data _─[_]→_ (x : A) : ℕ → A → Set where
    ε : x ─[ zero ]→ x
    _▸_ : ∀ {y z n} → x ─[ n ]→ y → y ⋖ z → x ─[ suc n ]→ z

  open import Gregorianum.Relation.Path A _─[_]→_

  _◂_ : ∀ {x y z n}
        → x ⋖ y
        → y ─[ n ]→ z
        → x ─[ suc n ]→ z
  y ◂ ε = ε ▸ y
  y ◂ (x⋖x' ▸ x') = (y ◂ x⋖x') ▸ x'

  ⟨_,_⟩<<_ : ∀ {x y z w n}
       → x ⋖ y
       → z ⋖ w
       → y ─[ n ]→ w
       → x ─[ n ]→ z
  ⟨ x⋖y , z⋖w ⟩<< ε with prev-unique x⋖y z⋖w
  ...                  | refl = ε
  ⟨ x⋖y , z⋖w ⟩<< (y→z ▸ z'⋖w) with prev-unique z⋖w z'⋖w
  ...                               | refl = x⋖y ◂ y→z

  _>>⟨_,_⟩ : ∀ {x y z w n}
           → x ─[ n ]→ z
           → x ⋖ y
           → z ⋖ w
           → y ─[ n ]→ w
  ε >>⟨ x⋖y , z⋖w ⟩ with next-unique x⋖y z⋖w
  ...                  | refl = ε
  (x→z' ▸ z'⋖z) >>⟨ x⋖y , z⋖w ⟩ = (x→z' >>⟨ x⋖y , z'⋖z ⟩) ▸ z⋖w

  identity : ∀ {x y} → x ≡ y → x ─[ zero ]→ y
  identity refl = ε

  identity⁻¹ : ∀ {x y} → x ─[ zero ]→ y → x ≡ y
  identity⁻¹ ε = refl

  trans : ∀ {x y z m n}
        → x ─[ m ]→ y
        → y ─[ n ]→ z
        → x ─[ m + n ]→ z
  trans {x = x} {z = z} x→y ε = subst (x ─[_]→ z) (sym (+-identityʳ _)) x→y
  trans {x = x} {z = z} x→y (y→z' ▸ z'⋖z) = (subst (x ─[_]→ z) (sym (+-suc _ _)) (trans x→y y→z' ▸ z'⋖z))

  split : ∀ {x z}
        → ∀ m n
        → x ─[ m + n ]→ z
        → ∃[ y ] (x ─[ m ]→ y × y ─[ n ]→ z)
  split m zero x→z rewrite +-identityʳ m = _ , x→z , ε
  split m (suc n) x→z rewrite +-suc m n with x→z
  ... | _▸_ {z'} x→z' z'⋖z with split m n x→z'
  ... | y , x→y , y→z' = y , x→y , (y→z' ▸ z'⋖z)

  isPath : IsPath
  isPath = record { identity = identity ; identity⁻¹ = identity⁻¹ ; trans = trans ; split = split }

  _▸⁻¹_ : ∀ {x y z n}
          → x ─[ suc n ]→ z
          → y ⋖ z
          → x ─[ n ]→ y
  (y→z' ▸ z'⋖z) ▸⁻¹ y⋖z with prev-unique z'⋖z y⋖z
  ... | refl                 = y→z'

  _◂⁻¹_ : ∀ {x y z n}
          → x ⋖ y
          → x ─[ suc n ]→ z
          → y ─[ n ]→ z
  _◂⁻¹_ {n = zero} x⋖y (x→z' ▸ z'⋖z) with identity⁻¹ x→z'
  ... | refl = identity (next-unique x⋖y z'⋖z)
  _◂⁻¹_ {n = suc n} x⋖y (x→z' ▸ z'⋖z) = (x⋖y ◂⁻¹ x→z') ▸ z'⋖z

  uniqueˡ : ∀ {x y z n}
          → x ─[ n ]→ z
          → y ─[ n ]→ z
          → x ≡ y
  uniqueˡ x→z ε = identity⁻¹ x→z
  uniqueˡ x→z (y→z' ▸ z'⋖z) with x→z ▸⁻¹ z'⋖z
  ... | x→z' = uniqueˡ x→z' y→z'

  uniqueʳ : ∀ {x y z n}
          → x ─[ n ]→ y
          → x ─[ n ]→ z
          → y ≡ z
  uniqueʳ x→y ε = sym (identity⁻¹ x→y)
  uniqueʳ (x→y' ▸ y'⋖y) (x→z' ▸ z'⋖z) with uniqueʳ x→y' x→z'
  ... | refl = next-unique y'⋖y z'⋖z

  private
    acyclic' : ∀ {x n} → x ─[ n ]→ x → WF.Acc _⋖_ x → n ≡ 0
    acyclic' ε _ = refl
    acyclic' (x→x' ▸ x'⋖x) (WF.acc rs) with acyclic' (x'⋖x ◂ x→x') (rs x'⋖x)
    ...                                     | ()

  acyclic : ∀ {x n} → x ─[ n ]→ x → n ≡ 0
  acyclic x→x = acyclic' x→x (⋖-wellFounded _)

  private
    ¬circle : ∀ {x n} → ¬ (x ─[ suc n ]→ x)
    ¬circle x with acyclic x
    ... | ()

  uniqueᶜ : ∀ {x y m n} → x ─[ m ]→ y →  x ─[ n ]→ y → m ≡ n
  uniqueᶜ {m = zero} {n = zero} ε ε = refl
  uniqueᶜ {m = zero} {n = suc n} ε x→y with acyclic x→y
  ... | ()
  uniqueᶜ {m = suc m} {n = zero} x→y ε with acyclic x→y
  ... | ()
  uniqueᶜ {m = suc m} {n = suc n} (x→y'₁ ▸ y'⋖y₁) (x→y'₂ ▸ y'⋖y₂) with prev-unique y'⋖y₁ y'⋖y₂
  ... | refl with uniqueᶜ x→y'₁ x→y'₂
  ... | refl = refl

  private
    bridge' : ∀ x y → ¬ IsSuc x → WF.Acc _⋖_ y → ∃[ n ] x ─[ n ]→ y
    bridge' x y ¬isSuc _ with isSuc? y
    bridge' x y ¬isSuc (WF.acc rs) | yes isSuc' with prev y isSuc'
    ... | y' , y'⋖y with bridge' x y' ¬isSuc (rs y'⋖y)
    ... | n , x→y = suc n , (x→y ▸ y'⋖y)
    bridge' x y ¬isSuc _ | no ¬isSuc' with ¬isSuc-unique ¬isSuc ¬isSuc'
    ... | refl = 0 , ε

    bridge : ∀ x y → ¬ IsSuc x → ∃[ n ] x ─[ n ]→ y
    bridge x y ¬isSuc = bridge' x y ¬isSuc (⋖-wellFounded y)

    total' : ∀ x y → WF.Acc _⋖_ y → Tri x y
    total' x y _ with isSuc? x | isSuc? y
    total' x y _ | no ¬isSuc₁ | no ¬isSuc₂ with ¬isSuc-unique ¬isSuc₁ ¬isSuc₂
    ... | eq = tri≡ eq
    total' x y _ | yes isSuc₁ | no ¬isSuc₂ with prev x isSuc₁
    ... | x' , x'⋖x with bridge y x' ¬isSuc₂
    ... | n , y→x' = tri← n (y→x' ▸ x'⋖x)
    total' x y _ | no ¬isSuc₁ | yes isSuc₂ with prev y isSuc₂
    ... | y' , y'⋖y with bridge x y' ¬isSuc₁
    ... | n , x→y' = tri→ n (x→y' ▸ y'⋖y)
    total' x y (WF.acc rs) | yes isSuc₁ | yes isSuc₂ with prev x isSuc₁ | prev y isSuc₂
    ... | x' , x'⋖x | y' , y'⋖y with total' x' y' (rs y'⋖y)
    ... | tri≡ refl = tri≡ (next-unique x'⋖x y'⋖y)
    ... | tri→ n x'→y' = tri→ n (x'→y' >>⟨ x'⋖x , y'⋖y ⟩)
    ... | tri← n y'→x' = tri← n (y'→x' >>⟨ y'⋖y , x'⋖x ⟩)

  total : ∀ x y → Tri x y
  total x y = total' x y (⋖-wellFounded y)

  isLinear : IsLinear
  isLinear = record
              { isPath = isPath
              ; uniqueˡ = uniqueˡ
              ; uniqueᶜ = uniqueᶜ
              ; uniqueʳ = uniqueʳ
              ; acyclic = acyclic
              ; total = total
              }
