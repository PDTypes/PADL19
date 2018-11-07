module Mangle where


open import Prelude.Decidable renaming (Dec to PDec)
open import Relation.Nullary using (Dec;yes;no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Prelude.Empty
pdec-to-dec : {A : Set} → PDec A → Dec A
pdec-to-dec (yes x) = yes x
pdec-to-dec (no x) = no (λ x₁ → ⊥-elim (x x₁))

open import Prelude.Equality using (Eq; _==_)

mangle : {A : Set}  ⦃ _ : Eq A ⦄  → Decidable (_≡_ {A = A} )
mangle {A} x y = pdec-to-dec (x == y)

