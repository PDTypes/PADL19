module PCPlans_logistics where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Data.List
open import Data.List.Any


open import Tactic.Deriving.Eq

--------------------------------------------------------

-- Constants
data C : Set where
  truck1 truck2
    city1 city2
    airplane1
    airport1 airport2
    package1 package2
    office1 office2 : C

-- EqC : Eq C
unquoteDecl EqC = deriveEq EqC (quote C)


-- Predicates
data R : Set where
  package : C → R
  truck : C → R
  airplane : C → R
  airport : C → R
  city : C → R
  vehicle : C → R
  location : C → R
  isAt : C → C → R
  inCity : C → C → R
  inVehicle : C → C → R


-- EqR : Eq R
unquoteDecl EqR = deriveEq EqR (quote R)

open import Mangle using (mangle)

-- Instatiation of decidability of predicates to the IsDecEquivalence type
isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = R})
isDecidable = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }

-- Actions
data Action : Set where
  load_p1_t1_o1 : Action
  load_p1_pl1_a1 : Action
  load_p1_t2_a2 : Action
  unload_p1_t1_a1 : Action
  unload_p1_pl1_a2 : Action
  unload_p1_t2_o2 : Action
  drive_t1_c1_a1_o1 : Action
  drive_t1_c1_o1_a1 : Action
  drive_t2_c2_o2_a2 : Action
  drive_t2_c2_a2_o2 : Action
  fly_pl1_a1_a2 : Action
  fly_pl1_a2_a1 : Action

-- Instantiation of module PCPlans
-- PCPlans is parameterised by the Action Set, Predicate Set
-- as well as a proof showing that the Predicate Set is decidable
open import PCPlans {Action} {R} {isDecidable}
open import Data.Product

--------------------------------------------------------

-- Example plan for logistics
plan₁ : Plan
plan₁ = doAct drive_t2_c2_a2_o2
        (doAct drive_t1_c1_a1_o1
        (doAct fly_pl1_a1_a2
        (doAct load_p1_t1_o1
        (doAct drive_t1_c1_o1_a1
        (doAct unload_p1_t1_a1
        (doAct fly_pl1_a2_a1
        (doAct load_p1_pl1_a1
        (doAct fly_pl1_a1_a2
        (doAct unload_p1_pl1_a2
        (doAct drive_t2_c2_o2_a2
        (doAct load_p1_t2_a2
        (doAct drive_t2_c2_a2_o2
        (doAct unload_p1_t2_o2
        halt)))))))))))))

--------------------------------------------------------


-- Definition of context showing preconditions and
-- postconditions of actions
Γ₁ : Γ
Γ₁ load_p1_t1_o1 = (atom (isAt truck1 office1) ∧ atom (isAt package1 office1)) ↓₊ ,
                         (( atom (inVehicle package1 truck1) ∧ ¬ (isAt package1 office1) ) ↓₊)
Γ₁ load_p1_pl1_a1 = (atom (isAt airplane1 airport1) ∧ atom (isAt package1 airport1)) ↓₊ ,
                         (( atom (inVehicle package1 airplane1) ∧ ¬ (isAt package1 airport1) ) ↓₊)
Γ₁ load_p1_t2_a2 = (atom (isAt truck2 airport2) ∧ atom (isAt package1 airport2)) ↓₊ ,
                         (( atom (inVehicle package1 truck2) ∧ ¬ (isAt package1 airport2) ) ↓₊)
Γ₁ unload_p1_t1_a1 = (atom (isAt truck1 airport1) ∧ atom (inVehicle package1 truck1)) ↓₊ ,
                         (((atom (isAt package1 airport1) ∧ ¬ (inVehicle package1 truck1)) ↓₊))
Γ₁ unload_p1_pl1_a2 = (atom (isAt airplane1 airport2) ∧ atom (inVehicle package1 airplane1)) ↓₊ ,
                         (((atom (isAt package1 airport2) ∧ ¬ (inVehicle package1 airplane1)) ↓₊))
Γ₁ unload_p1_t2_o2 = (atom (isAt truck2 office2) ∧ atom (inVehicle package1 truck2)) ↓₊ ,
                         (((atom (isAt package1 office2) ∧ ¬ (inVehicle package1 truck2)) ↓₊))
Γ₁ drive_t1_c1_a1_o1 = (atom (inCity airport1 city1) ∧ atom (inCity office1 city1) ∧ atom (isAt truck1 airport1)) ↓₊ ,
                         (((atom (isAt truck1 office1) ∧ ¬ (isAt truck1 airport1)) ↓₊))
Γ₁ drive_t1_c1_o1_a1 =  (atom (inCity office1 city1) ∧ atom (inCity airport1 city1) ∧ atom (isAt truck1 office1)) ↓₊ ,
                         (((atom (isAt truck1 airport1) ∧ ¬ (isAt truck1 office1)) ↓₊))
Γ₁ drive_t2_c2_o2_a2 = (atom (inCity office2 city2) ∧ atom (inCity airport2 city2) ∧ atom (isAt truck2 office2)) ↓₊ ,
                         (((atom (isAt truck2 airport2) ∧ ¬ (isAt truck2 office2)) ↓₊))
Γ₁ drive_t2_c2_a2_o2 = (atom (inCity airport2 city2) ∧ atom (inCity office2 city2) ∧ atom (isAt truck2 airport2)) ↓₊ ,
                         ((atom (isAt truck2 office2) ∧ ¬ (isAt truck2 airport2)) ↓₊)
Γ₁ fly_pl1_a1_a2 =     (atom (isAt airplane1 airport1)) ↓₊ ,
                         (((atom (isAt airplane1 airport2) ∧ ¬ (isAt airplane1 airport1)) ↓₊))
Γ₁ fly_pl1_a2_a1 =    (atom (isAt airplane1 airport2)) ↓₊ ,
                         (((atom (isAt airplane1 airport1) ∧ ¬ (isAt airplane1 airport2)) ↓₊))

--------------------------------------------------------

-- Initial State
P₀ : Form
P₀ = atom (inCity airport1 city1) ∧ atom (inCity airport2 city2) ∧ atom (inCity office1 city1) ∧ atom (inCity office2 city2)
      ∧ atom (isAt package1 office1) ∧ atom (isAt truck1 airport1) ∧ atom (isAt truck2 airport2) ∧ atom (isAt airplane1 airport1)

-- Goal State
Q₀ : Form
Q₀ = atom (isAt package1 office2)

-- Derivation of plan₁ on P₀ and Q₀
Derivation : Γ₁ ⊢ plan₁ ∶ (P₀ ↓₊) ↝ (Q₀ ↓₊)
Derivation = seq
           (atom<: (there (here refl)) --isAt truck2 airport2
           (atom<: (there ((there (there (there (here refl)))))) --incity o2 c2
           (atom<: (there (there (there (there (there (there (here refl))))))) --incity a2 c2
             ([]<:
                    ((+ , isAt airplane1 airport1) ∷
                     (+ , isAt truck2 airport2) ∷
                     (+ , isAt truck1 airport1) ∷
                     (+ , isAt package1 office1) ∷
                     (+ , inCity office2 city2) ∷
                     (+ , inCity office1 city1) ∷
                     (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ []))))) refl
           
           (seq
             (atom<: (there ((there (there (here refl)))))
             (atom<: (there ((there (there (there (there (there (here refl))))))))
             (atom<: ((there (there (there (there (there (there (there (there (here refl))))))))))
             ([]<:
                   ((- , isAt truck2 airport2) ∷
                    (+ , isAt truck2 office2) ∷
                    (+ , isAt airplane1 airport1) ∷
                    (+ , isAt truck1 airport1) ∷
                    (+ , isAt package1 office1) ∷
                    (+ , inCity office2 city2) ∷
                    (+ , inCity office1 city1) ∷
                    (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ []))))) refl
            (seq
              (atom<: (there (there ((there (there (here refl))))))
              ([]<:
                    ((- , isAt truck1 airport1) ∷
                     (+ , isAt truck1 office1) ∷
                     (- , isAt truck2 airport2) ∷
                     (+ , isAt truck2 office2) ∷
                     (+ , isAt airplane1 airport1) ∷
                     (+ , isAt package1 office1) ∷
                     (+ , inCity office2 city2) ∷
                     (+ , inCity office1 city1) ∷
                     (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ []))) refl
            (seq
              (atom<: ((there (there (there (there (there (there (here refl))))))))
              (atom<: ((there (there (there (here refl)))))
              ([]<:
                    ((- , isAt airplane1 airport1) ∷
                     (+ , isAt airplane1 airport2) ∷
                     (- , isAt truck1 airport1) ∷
                     (+ , isAt truck1 office1) ∷
                     (- , isAt truck2 airport2) ∷
                     (+ , isAt truck2 office2) ∷
                     (+ , isAt package1 office1) ∷
                     (+ , inCity office2 city2) ∷
                     (+ , inCity office1 city1) ∷
                     (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ [])))) refl
            (seq
              (atom<: ((there (there (there (there (there (here refl)))))))
              (atom<: ((there (there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))
              (atom<: (((there (there (there (there (there (there (there (there (there (here refl))))))))))))
              ([]<:
                    ((- , isAt package1 office1) ∷
                     (+ , inVehicle package1 truck1) ∷
                     (- , isAt airplane1 airport1) ∷
                     (+ , isAt airplane1 airport2) ∷
                     (- , isAt truck1 airport1) ∷
                     (+ , isAt truck1 office1) ∷
                     (- , isAt truck2 airport2) ∷
                     (+ , isAt truck2 office2) ∷
                     (+ , inCity office2 city2) ∷
                     (+ , inCity office1 city1) ∷
                     (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ []))))) refl
           (seq
             (atom<: (there (there (there (here refl) )))
             (atom<: (there (here refl))
             ([]<:
                   ((- , isAt truck1 office1) ∷
                    (+ , isAt truck1 airport1) ∷
                    (- , isAt package1 office1) ∷
                    (+ , inVehicle package1 truck1) ∷
                    (- , isAt airplane1 airport1) ∷
                    (+ , isAt airplane1 airport2) ∷
                    (- , isAt truck2 airport2) ∷
                    (+ , isAt truck2 office2) ∷
                    (+ , inCity office2 city2) ∷
                    (+ , inCity office1 city1) ∷
                    (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ [])))) refl
           (seq
             (atom<: ((there (there (there (there (there  (there (here refl))))))))
             ([]<:
                   ((- , inVehicle package1 truck1) ∷
                    (+ , isAt package1 airport1) ∷
                    (- , isAt truck1 office1) ∷
                    (+ , isAt truck1 airport1) ∷
                    (- , isAt package1 office1) ∷
                    (- , isAt airplane1 airport1) ∷
                    (+ , isAt airplane1 airport2) ∷
                    (- , isAt truck2 airport2) ∷
                    (+ , isAt truck2 office2) ∷
                    (+ , inCity office2 city2) ∷
                    (+ , inCity office1 city1) ∷
                    (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ []))) refl
          (seq
            (atom<: (there (there (there (here refl))))
            (atom<: (there (here refl))
            ([]<:
                  ((- , isAt airplane1 airport2) ∷
                   (+ , isAt airplane1 airport1) ∷
                   (- , inVehicle package1 truck1) ∷
                   (+ , isAt package1 airport1) ∷
                   (- , isAt truck1 office1) ∷
                   (+ , isAt truck1 airport1) ∷
                   (- , isAt package1 office1) ∷
                   (- , isAt truck2 airport2) ∷
                   (+ , isAt truck2 office2) ∷
                   (+ , inCity office2 city2) ∷
                   (+ , inCity office1 city1) ∷
                   (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ [])))) refl
          (seq
            (atom<: (there (there (there (here refl))))
            ([]<:
               ((- , isAt package1 airport1) ∷
                (+ , inVehicle package1 airplane1) ∷
                (- , isAt airplane1 airport2) ∷
                (+ , isAt airplane1 airport1) ∷
                (- , inVehicle package1 truck1) ∷
                (- , isAt truck1 office1) ∷
                (+ , isAt truck1 airport1) ∷
                (- , isAt package1 office1) ∷
                (- , isAt truck2 airport2) ∷
                (+ , isAt truck2 office2) ∷
                (+ , inCity office2 city2) ∷
                (+ , inCity office1 city1) ∷
                (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ []))) refl
          (seq
            (atom<: (there (there (there (here refl))))
            (atom<: (there (here refl))
            ([]<:
                  ((- , isAt airplane1 airport1) ∷
                   (+ , isAt airplane1 airport2) ∷
                   (- , isAt package1 airport1) ∷
                   (+ , inVehicle package1 airplane1) ∷
                   (- , inVehicle package1 truck1) ∷
                   (- , isAt truck1 office1) ∷
                   (+ , isAt truck1 airport1) ∷
                   (- , isAt package1 office1) ∷
                   (- , isAt truck2 airport2) ∷
                   (+ , isAt truck2 office2) ∷
                   (+ , inCity office2 city2) ∷
                   (+ , inCity office1 city1) ∷
                   (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ [])))) refl
          (seq
            (atom<: (((there (there (there (there (there (there (there (there (there (there (here refl)))))))))))))
            (atom<: (((there (there (there (there (there (there (there (there (there (there (there ((there (there (here refl)))))))))))))))))
            (atom<: (((there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))
            ([]<:
                  ((- , inVehicle package1 airplane1) ∷
                   (+ , isAt package1 airport2) ∷
                   (- , isAt airplane1 airport1) ∷
                   (+ , isAt airplane1 airport2) ∷
                   (- , isAt package1 airport1) ∷
                   (- , inVehicle package1 truck1) ∷
                   (- , isAt truck1 office1) ∷
                   (+ , isAt truck1 airport1) ∷
                   (- , isAt package1 office1) ∷
                   (- , isAt truck2 airport2) ∷
                   (+ , isAt truck2 office2) ∷
                   (+ , inCity office2 city2) ∷
                   (+ , inCity office1 city1) ∷
                   (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ []))))) refl
          (seq
            (atom<: (there (there (there (here refl))))
            (atom<: (there (here refl))
            ([]<:
                  ((- , isAt truck2 office2) ∷
                   (+ , isAt truck2 airport2) ∷
                   (- , inVehicle package1 airplane1) ∷
                   (+ , isAt package1 airport2) ∷
                   (- , isAt airplane1 airport1) ∷
                   (+ , isAt airplane1 airport2) ∷
                   (- , isAt package1 airport1) ∷
                   (- , inVehicle package1 truck1) ∷
                   (- , isAt truck1 office1) ∷
                   (+ , isAt truck1 airport1) ∷
                   (- , isAt package1 office1) ∷
                   (+ , inCity office2 city2) ∷
                   (+ , inCity office1 city1) ∷
                   (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ [])))) refl
          (seq
            (atom<: (there (there (there (here refl))))
            (atom<: ((((there (there (there (there (there (there (there (there (there (there (there (there (here refl))))))))))))))))
            (atom<: ((((there (there (there (there (there (there (there (there (there (there (there (there (there (there (here refl) )))))))))))))))))
            ([]<:
                  ((- , isAt package1 airport2) ∷
                   (+ , inVehicle package1 truck2) ∷
                   (- , isAt truck2 office2) ∷
                   (+ , isAt truck2 airport2) ∷
                   (- , inVehicle package1 airplane1) ∷
                   (- , isAt airplane1 airport1) ∷
                   (+ , isAt airplane1 airport2) ∷
                   (- , isAt package1 airport1) ∷
                   (- , inVehicle package1 truck1) ∷
                   (- , isAt truck1 office1) ∷
                   (+ , isAt truck1 airport1) ∷
                   (- , isAt package1 office1) ∷
                   (+ , inCity office2 city2) ∷
                   (+ , inCity office1 city1) ∷
                   (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ []))))) refl
         (seq
           (atom<: (there (there (there (here refl))))
           (atom<: (there (here refl))
           ([]<:
                 ((- , isAt truck2 airport2) ∷
                  (+ , isAt truck2 office2) ∷
                  (- , isAt package1 airport2) ∷
                  (+ , inVehicle package1 truck2) ∷
                  (- , inVehicle package1 airplane1) ∷
                  (- , isAt airplane1 airport1) ∷
                  (+ , isAt airplane1 airport2) ∷
                  (- , isAt package1 airport1) ∷
                  (- , inVehicle package1 truck1) ∷
                  (- , isAt truck1 office1) ∷
                  (+ , isAt truck1 airport1) ∷
                  (- , isAt package1 office1) ∷
                  (+ , inCity office2 city2) ∷
                  (+ , inCity office1 city1) ∷
                  (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ [])))) refl
         (halt
          (atom<: (there (here refl))
          ([]<:            
           ((- , inVehicle package1 truck2) ∷
           (+ , isAt package1 office2) ∷
           (- , isAt truck2 airport2) ∷
           (+ , isAt truck2 office2) ∷
           (- , isAt package1 airport2) ∷
           (- , inVehicle package1 airplane1) ∷
           (- , isAt airplane1 airport1) ∷
           (+ , isAt airplane1 airport2) ∷
           (- , isAt package1 airport1) ∷
           (- , inVehicle package1 truck1) ∷
           (- , isAt truck1 office1) ∷
           (+ , isAt truck1 airport1) ∷
           (- , isAt package1 office1) ∷
           (+ , inCity office2 city2) ∷
           (+ , inCity office1 city1) ∷
           (+ , inCity airport2 city2) ∷ (+ , inCity airport1 city1) ∷ [])))))))))))))))))

--------------------------------------------------------

{- Illustration for the Soundness Theorem:  The workings of a canonical handler. To test, evaluate the below
functions world-eval and formula-eval
  -}


wP₁ : World
wP₁ =  (inCity airport1 city1) ∷ (inCity airport2 city2) ∷ (inCity office1 city1) ∷ (inCity office2 city2)
      ∷  (isAt package1 office1) ∷ (isAt truck1 airport1) ∷  (isAt truck2 airport2) ∷ (isAt airplane1 airport1) ∷ []

world-eval : World 
world-eval = ⟦ plan₁ ⟧ (canonical-σ Γ₁) wP₁

formula-eval : World
formula-eval = ⟦ plan₁ ⟧ (canonical-σ Γ₁) (σα (P₀ ↓[ + ] []) [])
