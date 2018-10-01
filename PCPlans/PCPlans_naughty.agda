module PCPlans_naughty where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level

--------------------------------------------------------
-- A simple example that demonstrates violation of the
-- implicit consistency assumpion
--

-- We don't need any constants
data C : Set where

-- Predicates
data R : Set where
  handEmpty : R

-- There is only one, naughty, action, which violates the implicit
-- consistency assumption 
data Action : Set where 
  naughty : Action

-- The following two properties are required by the main Agda file:

-- Decidablity of constants (objects) -- 
_≡o?_ : Decidable (_≡_ {A = C})
() ≡o? ()

-- Decidability of predicates
_≡?_ : Decidable (_≡_ {A = R})
handEmpty ≡? handEmpty = yes refl


-- Instatiation of decidability of predicates to the IsDecEquivalence type
isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = R})
isDecidable = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = _≡?_  }


-- Instantiation of module PCPlans
-- PCPlans is parameterised by the Action Set, Predicate Set
-- as well as a proof showing that the Predicate Set is decidable
open import PCPlans {Action} {R} {isDecidable}
open import Data.Product
  
--------------------------------------------------------

-- The naughty action does not have any preconditions and
-- introduces an atomic predicate and its negation as 
-- postconditions
Γ₁ : Γ
Γ₁ naughty  = ( [] ,  ((- , handEmpty) ∷  (+ , handEmpty) ∷ []))

open import Data.Empty

-- Despite the obvious inconsistency,
-- the following plan has a derivation that type checks:
plan2 : Plan
plan2 = doAct naughty (halt)

Q : Form
Q =  atom (handEmpty) ∧  ¬ handEmpty 

Derivation2 : Γ₁ ⊢ plan2 ∶ [] ↝ (Q ↓[ + ] [])
Derivation2 = seq ([]<: []) refl (halt (atom<: (here refl)
  (atom<: (there (here refl))
    ([]<: ((- , handEmpty) ∷ (+ , handEmpty) ∷ [])))))

-- But, at the same time, action naughty
-- invalidates consistency of entire development
-- (given the implicit consistency assumption):
prop-inconsistent : ⊥
prop-inconsistent =
  implicit-consistency-assumption + handEmpty (proj₂ (Γ₁ naughty))
    (there (here refl))
    (here refl)
