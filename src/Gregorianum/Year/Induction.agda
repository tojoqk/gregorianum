module Gregorianum.Year.Induction where

open import Gregorianum.Year.Base
open import Gregorianum.Year.Epoch
open import Gregorianum.Year.Epoch.Properties

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
  _epoch<_ : Year → Year → Set
  _epoch<_ y₁ y₂ = proj₁ (toEpoch y₁) < proj₁ (toEpoch y₂)

  epoch<-WellFounded : WF.WellFounded _epoch<_
  epoch<-WellFounded y = accessible (proj₁ ∘ toEpoch) (ℕ.<-wellFounded-fast (proj₁ (toEpoch y)))

  ⋖⇒suc : ∀ {y₁ y₂} → y₁ ⋖ y₂ → ∃[ n ] (y₁ HasEpoch n) × (y₂ HasEpoch (suc n))
  ⋖⇒suc {y₁} {y₂} p with nextYear-epoch p epoch
  ...                  | epₙ = _ , epoch , epₙ

  ⋖⇒epoch< : ∀ {y₁ y₂} → y₁ ⋖ y₂ → y₁ epoch< y₂
  ⋖⇒epoch< {y₁} {y₂} p with ⋖⇒suc p | toEpoch y₁ | toEpoch y₂
  ... | n , ep₁ , ep₂ | n₁ , epoch | n₂ , epoch with epoch-unique ep₁ epoch | epoch-unique ep₂ epoch
  ... | eq₁ | eq₂ rewrite sym eq₂ | sym eq₁ = s≤s ≤-refl

⋖-wellFounded : WellFounded _⋖_
⋖-wellFounded y = Subrelation.accessible ⋖⇒epoch< (epoch<-WellFounded y)

module _ {ℓ : Level} where
  open WF.All ⋖-wellFounded ℓ public
    renaming ( wfRecBuilder to ⋖-recBuilder
             ; wfRec        to ⋖-rec
             )
    hiding (wfRec-builder)
