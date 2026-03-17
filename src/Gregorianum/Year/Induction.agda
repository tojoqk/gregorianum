module Gregorianum.Year.Induction where

open import Gregorianum.Year.Base
open import Gregorianum.Year.Weight
open import Gregorianum.Year.Weight.Properties

open import Induction.WellFounded as WF
open import Gregorianum.Data.Cursor
open import Gregorianum.Data.Cursor.Position hiding (_<_)
open import Data.Nat as ℕ using (ℕ; zero; suc; _<_; z≤n; s≤s)
open import Data.Nat.Properties as ℕ using (suc-injective; ≤-refl)
import Data.Nat.Induction as ℕ
open import Relation.Binary.Construct.On as On
open import Data.Product using (proj₁; _,_; ∃-syntax; _×_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Induction using (RecStruct; RecursorBuilder)
open import Data.Unit.Polymorphic.Base using (⊤)
open import Level using (Level)

private
  _weight<_ : Year → Year → Set
  _weight<_ y₁ y₂ = proj₁ (toWeight y₁) < proj₁ (toWeight y₂)

  weight<-WellFounded : WF.WellFounded _weight<_
  weight<-WellFounded y = accessible (proj₁ ∘ toWeight) (ℕ.<-wellFounded-fast (proj₁ (toWeight y)))

  ⋖⇒suc : ∀ {y₁ y₂} → y₁ ⋖ y₂ → ∃[ n ] (y₁ HasWeight n) × (y₂ HasWeight (suc n))
  ⋖⇒suc {y₁} {y₂} p with nextYear-weight p weight
  ...                  | epₙ = _ , weight , epₙ

  ⋖⇒weight< : ∀ {y₁ y₂} → y₁ ⋖ y₂ → y₁ weight< y₂
  ⋖⇒weight< {y₁} {y₂} p with ⋖⇒suc p | toWeight y₁ | toWeight y₂
  ... | n , ep₁ , ep₂ | n₁ , weight | n₂ , weight with weight-unique ep₁ weight | weight-unique ep₂ weight
  ... | eq₁ | eq₂ rewrite sym eq₂ | sym eq₁ = s≤s ≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded y = Subrelation.accessible ⋖⇒weight< (weight<-WellFounded y)

module _ {ℓ : Level} where
  open WF.All ⋖-wellFounded ℓ public
    renaming ( wfRecBuilder to ⋖-recBuilder
             ; wfRec        to ⋖-rec
             )
    hiding (wfRec-builder)
