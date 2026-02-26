open import Data.Nat using (ℕ)
import Gregorianum.Relation.Path as Path
import Gregorianum.Relation.DualLinear as DL

module Gregorianum.Relation.DualLinearOrder (A : Set)
                                            (_≤[_]→_ : A → ℕ → A → Set)
                                            (≤-isLinear : Path.IsLinear A _≤[_]→_)
                                            (_≥[_]→_ : A → ℕ → A → Set)
                                            (≥-isLinear : Path.IsLinear A _≥[_]→_)
                                            (isDualLinear : DL.IsDualLinear A _≤[_]→_ ≤-isLinear _≥[_]→_ ≥-isLinear)
                                            where

open import Data.Nat using (zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Gregorianum.Relation.DualLinear A _≤[_]→_ ≤-isLinear _≥[_]→_ ≥-isLinear
  renaming (Tri to PathTri)

open IsDualLinear isDualLinear renaming (compare to path-compare)

open import Gregorianum.Relation.LinearOrder A _≤[_]→_ ≤-isLinear
  renaming ( Tri to ≤-Tri
           ; compare to ≤-compare
           )
  public
open import Gregorianum.Relation.LinearOrder A _≥[_]→_ ≥-isLinear
  renaming ( _≤_ to _≥_
           ; ≤⟨_⟩ to ≥⟨_⟩
           ; ≤⟨_⟩[_] to ≥⟨_⟩[_]
           ; ≤-refl to ≥-refl
           ; ≤-antisym to ≥-antisym
           ; ≤-trans to ≥-trans
           ; _<_ to _>_
           ; <⟨_⟩ to >⟨_⟩
           ; <⟨_⟩[1+_] to >⟨_⟩[1+_]
           ; <-irrefl to >-irrefl
           ; <-asym to >-asym
           ; <-trans to >-trans
           ; <⇒≤ to >⇒≥
           ; ≤⇒< to ≥⇒>
           ; Tri to ≥-Tri
           ; tri< to tri>
           ; tri> to tri<
           ; compare to ≥-compare
           ) public

≤⇒≥ : ∀ {x y} → x ≤ y → y ≥ x
≤⇒≥ ≤⟨ path ⟩ = ≥⟨ ≤→⇒≥← path ⟩

≥⇒≤ : ∀ {x y} → x ≥ y → y ≤ x
≥⇒≤ ≥⟨ path ⟩ = ≤⟨ ≥→⇒≤← path ⟩

<⇒> : ∀ {x y} → x < y → y > x
<⇒> <⟨ path ⟩ = >⟨ ≤→⇒≥← path ⟩

>⇒< : ∀ {x y} → x > y → y < x
>⇒< >⟨ path ⟩ = <⟨ ≥→⇒≤← path ⟩

data Tri (x y : A) : Set where
  tri≡ : x ≡ y → Tri x y
  tri< : x < y → Tri x y
  tri> : x > y → Tri x y

compare : ∀ x y → Tri x y
compare x y with path-compare x y
... | tri≡ refl = tri≡ refl
... | tri≤→ x→y = tri< <⟨ x→y ⟩
... | tri≥→ x→y = tri> >⟨ x→y ⟩
