open import Data.List
open import Level

module _ {a} {p} {A : Set a} {P : A → Set p} where

  open import Data.List.Any {a} {A}
  open import Data.List.Any.Properties
  open import Data.Sum

  ++⁻[] : ∀ {P} {N : List A} -> Any {a} P (N ++ []) -> Any {a} P N
  ++⁻[] {P} {N} x with (++⁻ N x) 
  ++⁻[] {_} {_} x | inj₁ x₁ = x₁
  ++⁻[] {_} {_} x | inj₂ ()


  open import Relation.Binary.PropositionalEquality
  open import Relation.Binary

  any-cong : ∀ {P} {M N : List A} → Any {Level.zero} P M → M ≡ N  → Any {Level.zero} P N
  any-cong (here px) refl = here px
  any-cong (there x) refl = there x

  
