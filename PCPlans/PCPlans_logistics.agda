module PCPlans_logistics where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Data.List
open import Data.List.Any


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
 
  
data Obj : Set where
  truck1 truck2
    city1 city2
    airplane1
    airport1 airport2
    package1 package2
    office1 office2 : Obj

_≡o?_ : Decidable (_≡_ {A = Obj})
truck1 ≡o? truck1 = yes refl
truck1 ≡o? truck2 = no (λ ())
truck1 ≡o? city1 = no (λ ())
truck1 ≡o? city2 = no (λ ())
truck1 ≡o? airplane1 = no (λ ())
truck1 ≡o? airport1 = no (λ ())
truck1 ≡o? airport2 = no (λ ())
truck1 ≡o? package1 = no (λ ())
truck1 ≡o? package2 = no (λ ())
truck1 ≡o? office1 = no (λ ())
truck1 ≡o? office2 = no (λ ())
truck2 ≡o? truck1 = no (λ ())
truck2 ≡o? truck2 = yes refl
truck2 ≡o? city1 = no (λ ())
truck2 ≡o? city2 = no (λ ())
truck2 ≡o? airplane1 = no (λ ())
truck2 ≡o? airport1 = no (λ ())
truck2 ≡o? airport2 = no (λ ())
truck2 ≡o? package1 = no (λ ())
truck2 ≡o? package2 = no (λ ())
truck2 ≡o? office1 = no (λ ())
truck2 ≡o? office2 = no (λ ())
city1 ≡o? truck1 = no (λ ())
city1 ≡o? truck2 = no (λ ())
city1 ≡o? city1 = yes refl
city1 ≡o? city2 = no (λ ())
city1 ≡o? airplane1 = no (λ ())
city1 ≡o? airport1 = no (λ ())
city1 ≡o? airport2 = no (λ ())
city1 ≡o? package1 = no (λ ())
city1 ≡o? package2 = no (λ ())
city1 ≡o? office1 = no (λ ())
city1 ≡o? office2 = no (λ ())
city2 ≡o? truck1 = no (λ ())
city2 ≡o? truck2 = no (λ ())
city2 ≡o? city1 = no (λ ())
city2 ≡o? city2 = yes refl
city2 ≡o? airplane1 = no (λ ())
city2 ≡o? airport1 = no (λ ())
city2 ≡o? airport2 = no (λ ())
city2 ≡o? package1 = no (λ ())
city2 ≡o? package2 = no (λ ())
city2 ≡o? office1 = no (λ ())
city2 ≡o? office2 = no (λ ())
airplane1 ≡o? truck1 = no (λ ())
airplane1 ≡o? truck2 = no (λ ())
airplane1 ≡o? city1 = no (λ ())
airplane1 ≡o? city2 = no (λ ())
airplane1 ≡o? airplane1 = yes refl
airplane1 ≡o? airport1 = no (λ ())
airplane1 ≡o? airport2 = no (λ ())
airplane1 ≡o? package1 = no (λ ())
airplane1 ≡o? package2 = no (λ ())
airplane1 ≡o? office1 = no (λ ())
airplane1 ≡o? office2 = no (λ ())
airport1 ≡o? truck1 = no (λ ())
airport1 ≡o? truck2 = no (λ ())
airport1 ≡o? city1 = no (λ ())
airport1 ≡o? city2 = no (λ ())
airport1 ≡o? airplane1 = no (λ ())
airport1 ≡o? airport1 = yes refl
airport1 ≡o? airport2 = no (λ ())
airport1 ≡o? package1 = no (λ ())
airport1 ≡o? package2 = no (λ ())
airport1 ≡o? office1 = no (λ ())
airport1 ≡o? office2 = no (λ ())
airport2 ≡o? truck1 = no (λ ())
airport2 ≡o? truck2 = no (λ ())
airport2 ≡o? city1 = no (λ ())
airport2 ≡o? city2 = no (λ ())
airport2 ≡o? airplane1 = no (λ ())
airport2 ≡o? airport1 = no (λ ())
airport2 ≡o? airport2 = yes refl
airport2 ≡o? package1 = no (λ ())
airport2 ≡o? package2 = no (λ ())
airport2 ≡o? office1 = no (λ ())
airport2 ≡o? office2 = no (λ ())
package1 ≡o? truck1 = no (λ ())
package1 ≡o? truck2 = no (λ ())
package1 ≡o? city1 = no (λ ())
package1 ≡o? city2 = no (λ ())
package1 ≡o? airplane1 = no (λ ())
package1 ≡o? airport1 = no (λ ())
package1 ≡o? airport2 = no (λ ())
package1 ≡o? package1 = yes refl
package1 ≡o? package2 = no (λ ())
package1 ≡o? office1 = no (λ ())
package1 ≡o? office2 = no (λ ())
package2 ≡o? truck1 = no (λ ())
package2 ≡o? truck2 = no (λ ())
package2 ≡o? city1 = no (λ ())
package2 ≡o? city2 = no (λ ())
package2 ≡o? airplane1 = no (λ ())
package2 ≡o? airport1 = no (λ ())
package2 ≡o? airport2 = no (λ ())
package2 ≡o? package1 = no (λ ())
package2 ≡o? package2 = yes refl
package2 ≡o? office1 = no (λ ())
package2 ≡o? office2 = no (λ ())
office1 ≡o? truck1 = no (λ ())
office1 ≡o? truck2 = no (λ ())
office1 ≡o? city1 = no (λ ())
office1 ≡o? city2 = no (λ ())
office1 ≡o? airplane1 = no (λ ())
office1 ≡o? airport1 = no (λ ())
office1 ≡o? airport2 = no (λ ())
office1 ≡o? package1 = no (λ ())
office1 ≡o? package2 = no (λ ())
office1 ≡o? office1 = yes refl
office1 ≡o? office2 = no (λ ())
office2 ≡o? truck1 = no (λ ())
office2 ≡o? truck2 = no (λ ())
office2 ≡o? city1 = no (λ ())
office2 ≡o? city2 = no (λ ())
office2 ≡o? airplane1 = no (λ ())
office2 ≡o? airport1 = no (λ ())
office2 ≡o? airport2 = no (λ ())
office2 ≡o? package1 = no (λ ())
office2 ≡o? package2 = no (λ ())
office2 ≡o? office1 = no (λ ())
office2 ≡o? office2 = yes refl

data R : Set where
  package : Obj → R
  truck : Obj → R
  airplane : Obj → R
  airport : Obj → R
  city : Obj → R
  vehicle : Obj → R
  location : Obj → R
  isAt : Obj → Obj → R
  inCity : Obj → Obj → R
  inVehicle : Obj → Obj → R

{-
data Obj : Set where
  a b c : Obj

_≡o?_ : Decidable (_≡_ {A = Obj})
a ≡o? a = yes refl
a ≡o? b = no (λ ())
a ≡o? c = no (λ ())
b ≡o? a = no (λ ())
b ≡o? b = yes refl
b ≡o? c = no (λ ())
c ≡o? a = no (λ ())
c ≡o? b = no (λ ())
c ≡o? c = yes refl -}

_≡?_ : Decidable (_≡_ {A = R})
package x ≡? package x' with x ≡o? x'
(package x ≡? package x') | yes refl = yes refl
(package x ≡? package x') | no ¬p =  no λ {refl → ¬p refl}
package x ≡? truck x₁ = no (λ ())
package x ≡? airplane x₁ = no (λ ())
package x ≡? airport x₁ = no (λ ())
package x ≡? city x₁ = no (λ ())
package x ≡? vehicle x₁ = no (λ ())
package x ≡? location x₁ = no (λ ())
package x ≡? isAt x₁ x₂ = no (λ ())
package x ≡? inCity x₁ x₂ = no (λ ())
package x ≡? inVehicle x₁ x₂ = no (λ ())
truck x ≡? package x₁ = no (λ ())
truck x ≡? truck x' with x ≡o? x'
(truck x ≡? truck x') | yes refl = yes refl
(truck x ≡? truck x') | no ¬p = no (\ {refl -> ¬p refl})
truck x ≡? airplane x₁ = no (λ ())
truck x ≡? airport x₁ = no (λ ())
truck x ≡? city x₁ = no (λ ())
truck x ≡? vehicle x₁ = no (λ ())
truck x ≡? location x₁ = no (λ ())
truck x ≡? isAt x₁ x₂ = no (λ ())
truck x ≡? inCity x₁ x₂ = no (λ ())
truck x ≡? inVehicle x₁ x₂ = no (λ ())
airplane x ≡? package x₁ = no (λ ())
airplane x ≡? truck x₁ = no (λ ())
airplane x ≡? airplane x' with x ≡o? x'
(airplane x ≡? airplane x') | yes refl = yes refl
(airplane x ≡? airplane x') | no ¬p = no (\ {refl -> ¬p refl})
airplane x ≡? airport x₁ = no (λ ())
airplane x ≡? city x₁ = no (λ ())
airplane x ≡? vehicle x₁ = no (λ ())
airplane x ≡? location x₁ = no (λ ())
airplane x ≡? isAt x₁ x₂ = no (λ ())
airplane x ≡? inCity x₁ x₂ = no (λ ())
airplane x ≡? inVehicle x₁ x₂ = no (λ ())
airport x ≡? package x₁ = no (λ ())
airport x ≡? truck x₁ = no (λ ())
airport x ≡? airplane x₁ = no (λ ())
airport x ≡? airport x' with x ≡o? x'
(airport x ≡? airport .x) | yes refl = yes refl
(airport x ≡? airport x') | no ¬p = no (\ {refl -> ¬p refl})
airport x ≡? city x₁ = no (λ ())
airport x ≡? vehicle x₁ = no (λ ())
airport x ≡? location x₁ = no (λ ())
airport x ≡? isAt x₁ x₂ = no (λ ())
airport x ≡? inCity x₁ x₂ = no (λ ())
airport x ≡? inVehicle x₁ x₂ = no (λ ())
city x ≡? package x₁ = no (λ ())
city x ≡? truck x₁ = no (λ ())
city x ≡? airplane x₁ = no (λ ())
city x ≡? airport x₁ = no (λ ())
city x ≡? city x' with x ≡o? x'
(city x ≡? city .x) | yes refl = yes refl
(city x ≡? city x') | no ¬p = no (\ {refl -> ¬p refl})
city x ≡? vehicle x₁ = no (λ ())
city x ≡? location x₁ = no (λ ())
city x ≡? isAt x₁ x₂ = no (λ ())
city x ≡? inCity x₁ x₂ = no (λ ())
city x ≡? inVehicle x₁ x₂ = no (λ ())
vehicle x ≡? package x₁ = no (λ ())
vehicle x ≡? truck x₁ = no (λ ())
vehicle x ≡? airplane x₁ = no (λ ())
vehicle x ≡? airport x₁ = no (λ ())
vehicle x ≡? city x₁ = no (λ ())
vehicle x ≡? vehicle x' with x ≡o? x'
(vehicle x ≡? vehicle .x) | yes refl = yes refl
(vehicle x ≡? vehicle x') | no ¬p = no (\ {refl -> ¬p refl})
vehicle x ≡? location x₁ = no (λ ())
vehicle x ≡? isAt x₁ x₂ = no (λ ())
vehicle x ≡? inCity x₁ x₂ = no (λ ())
vehicle x ≡? inVehicle x₁ x₂ = no (λ ())
location x ≡? package x₁ = no (λ ())
location x ≡? truck x₁ = no (λ ())
location x ≡? airplane x₁ = no (λ ())
location x ≡? airport x₁ = no (λ ())
location x ≡? city x₁ = no (λ ())
location x ≡? vehicle x₁ = no (λ ())
location x ≡? location x' with x ≡o? x'
(location x ≡? location .x) | yes refl = yes refl
(location x ≡? location x') | no ¬p = no (\ {refl -> ¬p refl})
location x ≡? isAt x₁ x₂ = no (λ ())
location x ≡? inCity x₁ x₂ = no (λ ())
location x ≡? inVehicle x₁ x₂ = no (λ ())
isAt x x₁ ≡? package x₂ = no (λ ())
isAt x x₁ ≡? truck x₂ = no (λ ())
isAt x x₁ ≡? airplane x₂ = no (λ ())
isAt x x₁ ≡? airport x₂ = no (λ ())
isAt x x₁ ≡? city x₂ = no (λ ())
isAt x x₁ ≡? vehicle x₂ = no (λ ())
isAt x x₁ ≡? location x₂ = no (λ ())
isAt x x1 ≡? isAt x' x1' with x ≡o? x' | x1 ≡o? x1'
(isAt x x1 ≡? isAt .x .x1) | yes refl | yes refl = yes refl
(isAt x x1 ≡? isAt x' x1') | yes p | no ¬p = no (\ {refl -> ¬p refl})
(isAt x x1 ≡? isAt x' x1') | no ¬p | yes p = no (\ {refl -> ¬p refl})
(isAt x x1 ≡? isAt x' x1') | no ¬p | no ¬p₁ = no (\ {refl -> ¬p refl})
isAt x x₁ ≡? inCity x₂ x₃ = no (λ ())
isAt x x₁ ≡? inVehicle x₂ x₃ = no (λ ())
inCity x x₁ ≡? package x₂ = no (λ ())
inCity x x₁ ≡? truck x₂ = no (λ ())
inCity x x₁ ≡? airplane x₂ = no (λ ())
inCity x x₁ ≡? airport x₂ = no (λ ())
inCity x x₁ ≡? city x₂ = no (λ ())
inCity x x₁ ≡? vehicle x₂ = no (λ ())
inCity x x₁ ≡? location x₂ = no (λ ())
inCity x x₁ ≡? isAt x₂ x₃ = no (λ ())
inCity x x1 ≡? inCity x' x1'  with x ≡o? x' | x1 ≡o? x1'
(inCity x x1 ≡? inCity .x .x1) | yes refl | yes refl = yes refl
(inCity x x1 ≡? inCity x' x1') | yes p | no ¬p = no (\ {refl -> ¬p refl})
(inCity x x1 ≡? inCity x' x1') | no ¬p | yes p = no (\ {refl -> ¬p refl})
(inCity x x1 ≡? inCity x' x1') | no ¬p | no ¬p₁ = no (\ {refl -> ¬p refl})
inCity x x₁ ≡? inVehicle x₂ x₃ = no (λ ())
inVehicle x x₁ ≡? package x₂ = no (λ ())
inVehicle x x₁ ≡? truck x₂ = no (λ ())
inVehicle x x₁ ≡? airplane x₂ = no (λ ())
inVehicle x x₁ ≡? airport x₂ = no (λ ())
inVehicle x x₁ ≡? city x₂ = no (λ ())
inVehicle x x₁ ≡? vehicle x₂ = no (λ ())
inVehicle x x₁ ≡? location x₂ = no (λ ())
inVehicle x x₁ ≡? isAt x₂ x₃ = no (λ ())
inVehicle x x₁ ≡? inCity x₂ x₃ = no (λ ())
inVehicle x x1 ≡? inVehicle x' x1'  with x ≡o? x' | x1 ≡o? x1'
(inVehicle x x1 ≡? inVehicle .x .x1) | yes refl | yes refl = yes refl
(inVehicle x x1 ≡? inVehicle x' x1') | yes p | no ¬p = no (\ {refl -> ¬p refl})
(inVehicle x x1 ≡? inVehicle x' x1') | no ¬p | yes p = no (\ {refl -> ¬p refl})
(inVehicle x x1 ≡? inVehicle x' x1') | no ¬p | no ¬p₁ = no (\ {refl -> ¬p refl})

isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = R})
isDecidable = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = _≡?_  }

open import PCPlans {Action} {R} {isDecidable}
open import Data.Product

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


P₀ : Form
P₀ = atom (inCity airport1 city1) ∧ atom (inCity airport2 city2) ∧ atom (inCity office1 city1) ∧ atom (inCity office2 city2)
      ∧ atom (isAt package1 office1) ∧ atom (isAt truck1 airport1) ∧ atom (isAt truck2 airport2) ∧ atom (isAt airplane1 airport1)

Q₀ : Form
Q₀ = atom (isAt package1 office2)

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

{- Illustration for the Soundness Theorem:  The workings of a canonical handler -}

wP₁ : World
wP₁ =  (inCity airport1 city1) ∷ (inCity airport2 city2) ∷ (inCity office1 city1) ∷ (inCity office2 city2)
      ∷  (isAt package1 office1) ∷ (isAt truck1 airport1) ∷  (isAt truck2 airport2) ∷ (isAt airplane1 airport1) ∷ []

foo : World
foo = ⟦ plan₁ ⟧ (canonical-σ Γ₁) wP₁

bar : World
bar = ⟦ plan₁ ⟧ (canonical-σ Γ₁) (σα (P₀ ↓[ + ] []) [])
