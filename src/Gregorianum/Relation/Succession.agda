module Gregorianum.Relation.Succession (A : Set) (_⋖_ : A → A → Set) where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; <-cmp; s≤s; _≟_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; cong; subst; module ≡-Reasoning)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Relation.Nullary.Negation using (¬_)
import Induction.WellFounded as WF

record IsSuccession : Set₁ where
  field
    IsSuc : A → Set
    isSuc? : (x : A) → Dec (IsSuc x)
    ¬isSuc-unique : ∀ {x y} → ¬ IsSuc x → ¬ IsSuc y → x ≡ y
    next : (x : A) → ∃[ y ] x ⋖ y
    prev : (y : A) → IsSuc y → ∃[ x ] x ⋖ y
    next-unique : ∀ {x y z} → x ⋖ y → x ⋖ z → y ≡ z
    prev-unique : ∀ {x y z} → x ⋖ z → y ⋖ z → x ≡ y
    ⋖-wellFounded : WF.WellFounded _⋖_
    ∃prev⇒IsSuc : ∀ {x y} → x ⋖ y → IsSuc y
    ⋖-irrelevant : ∀ {d₁ d₂} → (p₁ p₂ : d₁ ⋖ d₂) → p₁ ≡ p₂

module Path (isSuccession : IsSuccession) where
  open IsSuccession isSuccession

  data _─[_]→_ (x : A) : ℕ → A → Set where
    ε : x ─[ zero ]→ x
    _▸_ : ∀ {y z n} → x ─[ n ]→ y → y ⋖ z → x ─[ suc n ]→ z

  open import Gregorianum.Relation.Path A _─[_]→_ using (IsPath)

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

  open import Gregorianum.Relation.Path A _─[_]→_ using (IsLinear)
  open import Gregorianum.Relation.Path A _─[_]→_ using (Tri; tri≡; tri←; tri→) public

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

  forward : ∀ x n → ∃[ y ] x ─[ n ]→ y
  forward x zero = x , ε
  forward x (suc n) = let (y' , x→y') = forward x n in
                      let (y , x⋖y)  = next y' in y , (x→y' ▸ x⋖y)

  backward? : ∀ y n → Dec (∃[ x ] x ─[ n ]→ y)
  backward? y zero = yes (y , ε)
  backward? y (suc n) with isSuc? y
  backward? y (suc n) | yes isSuc with prev y isSuc
  ... | y' , y'⋖y with backward? y' n
  ... | yes (x , x→y) = yes (x , (x→y ▸ y'⋖y))
  ... | no ¬p = no λ {(x , x→y) → ¬p (x , (x→y ▸⁻¹ y'⋖y))}
  backward? y (suc n) | no ¬isSuc = no λ { (_ , (_ ▸ y'⋖y)) → ¬isSuc (∃prev⇒IsSuc y'⋖y)}

  irrelevant : ∀ {x y n} → (p₁ p₂ : x ─[ n ]→ y) → p₁ ≡ p₂
  irrelevant ε ε = refl
  irrelevant (p₁ ▸ x) (p₂ ▸ x₁) with uniqueʳ p₁ p₂
  ... | refl with irrelevant p₁ p₂ | ⋖-irrelevant x x₁
  ... | refl | refl = refl

import Gregorianum.Relation.Timeline A as T

record IsIsoToTimeline (isSuccession : IsSuccession) (isTimeline : T.IsTimeline) : Set where
  open IsSuccession isSuccession
  open T.IsTimeline isTimeline using (_HasOrdinal_)
  field
    suc-ordinal⇒IsSuc : ∀ {d n} → d HasOrdinal (suc n) → IsSuc d
    prev-ordinal : ∀ {d₁ d₂ n} → d₁ ⋖ d₂ → d₂ HasOrdinal (suc n) → d₁ HasOrdinal n
    next-ordinal : ∀ {d₁ d₂ n} → d₁ ⋖ d₂ → d₁ HasOrdinal n → d₂ HasOrdinal (suc n)

module IsoToTimeline (isSuccession : IsSuccession) (isTimeline : T.IsTimeline) (isIsoToTimeline : IsIsoToTimeline isSuccession isTimeline) where
  open IsSuccession isSuccession
  open Path isSuccession
  module TP = T.Path isTimeline
  open IsIsoToTimeline isIsoToTimeline

  fromTimeline : ∀ {x y n} → x TP.─[ n ]→ y → x ─[ n ]→ y
  fromTimeline {n = zero} x→y with TP.identity⁻¹ x→y
  ... | refl = ε
  fromTimeline {y = y} {n = suc n} TP.⟨ start , end ⟩ with prev y (suc-ordinal⇒IsSuc end)
  ... | y' , y'⋖y with prev-ordinal y'⋖y end
  ... | ho with fromTimeline TP.⟨ start , ho ⟩
  ... | x→y' = x→y' ▸ y'⋖y

  toTimeline : ∀ {x y n} → x ─[ n ]→ y → x TP.─[ n ]→ y
  toTimeline ε = TP.identity refl
  toTimeline (x→y' ▸ y'⋖y) with toTimeline x→y'
  ... | TP.⟨ start , end' ⟩ = TP.⟨ start , next-ordinal y'⋖y end' ⟩

  fromTimeline∘toTimeline : ∀ {x y n} → (p : x ─[ n ]→ y) → fromTimeline (toTimeline p) ≡ p
  fromTimeline∘toTimeline p = irrelevant (fromTimeline (toTimeline p)) p

  toTimeline∘fromTimeline : ∀ {x y n} → (p : x TP.─[ n ]→ y) → toTimeline (fromTimeline p) ≡ p
  toTimeline∘fromTimeline p = TP.irrelevant (toTimeline (fromTimeline p)) p

  compare : ∀ x y → Tri x y
  compare x y with TP.compare x y
  ... | TP.tri≡ x₁ = tri≡ x₁
  ... | TP.tri→ n x→y = tri→ n (fromTimeline x→y)
  ... | TP.tri← n y→x = tri← n (fromTimeline y→x)

  _─[_]→?_ : ∀ x n y → Dec (x ─[ n ]→ y)
  x ─[ n ]→? y with x TP.─[ n ]→? y
  ... | yes x→y = yes (fromTimeline x→y)
  ... | no ¬p = no λ {x→y → ¬p (toTimeline x→y)}
