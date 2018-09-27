module PCPlans_blocksworld where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level

data Action : Set where
  pickup_from_table_b : Action
  pickup_from_table_a : Action
  putdown_on_stack_b_c : Action
  putdown_on_stack_a_b : Action

data C : Set where
  a b c : C
  
data R : Set where
  handEmpty : R
  onTable : C → R
  clear : C → R
  holding : C → R
  on : C → C → R

_≡o?_ : Decidable (_≡_ {A = C})
a ≡o? a = yes refl
a ≡o? b = no (λ ())
a ≡o? c = no (λ ())
b ≡o? a = no (λ ())
b ≡o? b = yes refl
b ≡o? c = no (λ ())
c ≡o? a = no (λ ())
c ≡o? b = no (λ ())
c ≡o? c = yes refl

_≡?_ : Decidable (_≡_ {A = R})
handEmpty ≡? handEmpty = yes refl
handEmpty ≡? onTable x = no (λ ())
handEmpty ≡? clear x = no (λ ())
handEmpty ≡? holding x = no (λ ())
handEmpty ≡? on x x₁ = no (λ ())
onTable x ≡? handEmpty = no (λ ())
onTable x ≡? onTable x' with x ≡o? x'
onTable x ≡? onTable .x | yes refl = yes refl
onTable x ≡? onTable x' | no x≢x' = no λ {refl → x≢x' refl}
onTable x ≡? clear x' = no (λ ())
onTable x ≡? holding x' = no (λ ())
onTable x ≡? on x' x'' = no (λ ())
clear x ≡? handEmpty = no (λ ())
clear x ≡? onTable x₁ = no (λ ())
clear x ≡? clear x' with x ≡o? x'
clear x ≡? clear .x | yes refl = yes refl
clear x ≡? clear x' | no x≢x' = no λ {refl → x≢x' refl}
clear x ≡? holding x₁ = no (λ ())
clear x ≡? on x₁ x₂ = no (λ ())
holding x ≡? handEmpty = no (λ ())
holding x ≡? onTable x₁ = no (λ ())
holding x ≡? clear x₁ = no (λ ())
holding x ≡? holding x' with x ≡o? x'
holding x ≡? holding .x | yes refl = yes refl
holding x ≡? holding x' | no x≢x' = no λ {refl → x≢x' refl}
holding x ≡? on x₁ x₂ = no (λ ())
on x x₁ ≡? handEmpty = no (λ ())
on x x₁ ≡? onTable x₂ = no (λ ())
on x x₁ ≡? clear x₂ = no (λ ())
on x x₁ ≡? holding x₂ = no (λ ())
on x x₁ ≡? on x' x₁' with x ≡o? x' | x₁ ≡o? x₁'
on x x₁ ≡? on .x .x₁ | yes refl | yes refl = yes refl
on x x₁ ≡? on .x x₁' | yes refl | no x₁≢x₁' = no λ {refl → x₁≢x₁' refl}
on x x₁ ≡? on x' .x₁ | no x≢x' | yes refl = no λ {refl → x≢x' refl}
on x x₁ ≡? on x' x₁' | no x≢x' | no x₁≢x₁' = no λ {refl → x₁≢x₁' refl}

isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = R})
isDecidable = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = _≡?_  }

open import PCPlans {Action} {R} {isDecidable}
open import Data.Product

Γ₁ : Γ
Γ₁ pickup_from_table_b  =
  (atom handEmpty ∧ atom (onTable b) ∧ atom (clear b)) ↓₊ ,
  ((¬ handEmpty ∧ ¬ (onTable b) ∧ atom (holding b)) ↓₊)
Γ₁ pickup_from_table_a  =
  (atom handEmpty ∧ atom (onTable a) ∧ atom (clear a)) ↓₊ ,
  ((¬ handEmpty ∧ ¬ (onTable a) ∧ atom (holding a)) ↓₊)
Γ₁ putdown_on_stack_b_c =
  (atom (holding b) ∧ atom (clear c)) ↓₊ ,
  (¬ (holding b) ∧ ¬ (clear c) ∧ atom (on b c) ∧ atom handEmpty) ↓₊
Γ₁ putdown_on_stack_a_b =
  (atom (holding a) ∧ atom (clear b)) ↓₊ ,
  (¬ (holding a) ∧ ¬ (clear b) ∧ atom (on a b) ∧ atom handEmpty) ↓₊ 


plan₁ : Plan
plan₁ = doAct pickup_from_table_b
        (doAct putdown_on_stack_b_c
        (doAct pickup_from_table_a
        (doAct putdown_on_stack_a_b
         halt)))

P₀ : Form
P₀ = atom (onTable a) ∧ atom (onTable b) ∧ atom (onTable c) ∧ atom (clear a) ∧ atom (clear b) ∧ atom (clear c) ∧ atom handEmpty



Q₀ : Form
Q₀ = atom (on a b) ∧ atom (on b c)


{- Γ₁⊢plan₁∶P₀↓₊↝Q₀↓₊ -}

Derivation : Γ₁ ⊢ plan₁ ∶ (P₀ ↓₊) ↝ (Q₀ ↓₊)
{- Γ₁⊢plan₁∶P₀↓₊↝Q₀↓₊ = -}
Derivation = 
  seq (atom<: (there (there (here refl)))
      (atom<: (there (there (there (there (there (here refl))))))
      (atom<: (here refl)
      ([]<: ((+ , handEmpty) ∷
             (+ , clear c) ∷
             (+ , clear b) ∷
             (+ , clear a) ∷
             (+ , onTable c) ∷ (+ , onTable b) ∷ (+ , onTable a) ∷ [])))))
      refl
  (seq (atom<: (there (there (there (here refl))))
       (atom<: (here refl)
       ([]<: ((+ , holding b) ∷
              (- , onTable b) ∷
              (- , handEmpty) ∷
              (+ , clear c) ∷
              (+ , clear b) ∷
              (+ , clear a) ∷ (+ , onTable c) ∷ (+ , onTable a) ∷ []))))
       refl
  (seq (atom<: (there (there (there (there (there (there (here refl)))))))
       (atom<: (there (there (there (there (there (there (there (there (here refl)))))))))
       (atom<: (here refl)
       ([]<: ((+ , handEmpty) ∷
              (+ , on b c) ∷
              (- , clear c) ∷
              (- , holding b) ∷
              (- , onTable b) ∷
              (+ , clear b) ∷
              (+ , clear a) ∷ (+ , onTable c) ∷ (+ , onTable a) ∷ [])))))
       refl
  (seq (atom<: (there (there (there (there (there (there (there (here refl))))))))
       (atom<: (here refl)
       ([]<: ((+ , holding a) ∷
              (- , onTable a) ∷
              (- , handEmpty) ∷
              (+ , on b c) ∷
              (- , clear c) ∷
              (- , holding b) ∷
              (- , onTable b) ∷
              (+ , clear b) ∷ (+ , clear a) ∷ (+ , onTable c) ∷ []))))
       refl
  (halt (atom<: (there (there (there (there (there (here refl))))))
        (atom<: (there (here refl))
        ([]<: ((+ , handEmpty) ∷
               (+ , on a b) ∷
               (- , clear b) ∷
               (- , holding a) ∷
               (- , onTable a) ∷
               (+ , on b c) ∷
               (- , clear c) ∷
               (- , holding b) ∷
               (- , onTable b) ∷ (+ , clear a) ∷ (+ , onTable c) ∷ [])))))))) 


{- Illustration for the Soundness Theorem:  The workings of a canonical handler. To test, evaluate the below
functions world-eval and formula-eval
  -}

wP₁ : World
wP₁ = (onTable a) ∷ (onTable b) ∷ (onTable c) ∷ (clear a) ∷ (clear b) ∷ (clear c) ∷ handEmpty ∷ []


world-eval : World
world-eval = ⟦ plan₁ ⟧ (canonical-σ Γ₁) wP₁

formula-eval : World
formula-eval = ⟦ plan₁ ⟧ (canonical-σ Γ₁) (σα (P₀ ↓[ + ] []) [])
