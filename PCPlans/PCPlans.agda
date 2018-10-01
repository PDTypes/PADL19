-- Proof Carrying Plans, (supporting Agda code)
-- by C.Schwaab, A.Hill, F.Farka and E.Komendantskaya
-- This file defines Planning languages as types, plans as prrof terms approach to PDDL 

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

--------------------------------------------------------
-- Section 3: Definition of formulae, possible world semantics, actions, plans

--
-- The following module declarartion allows to develop the file parametrised on an abstract set R of predicates
-- an an abstract set A of declared actions. The former must have decidable equivalence.

module PCPlans {Action : Set} {R : Set } {isDE : IsDecEquivalence {A = R} (_≡_) } where

-- Figure 2 and 3
-- Formulae: 
--
-- Form ::= A | ¬ A | Form ∧ Form
--
data Form : Set where
  _∧_ : Form → Form → Form
  ¬_ : R  → Form
  atom : R → Form
infixl 4 _∧_
infixl 5 ¬_


--------------------------------------------------------
-- Figure 4. Possible worlds 
--

open import Data.List

World : Set
World = List R

data Polarity : Set where
  + - : Polarity

neg : Polarity → Polarity
neg + = -
neg - = +

--------------------------------------------------------
-- Figure 6. Declarative (possible world) semantics
-- 

open import Data.List.Membership.Propositional
--open import Data.List.Any.Membership.Propositional 


-- Entailment Relation
infix 3 _⊨[_]_
data _⊨[_]_ : World → Polarity → Form → Set where
  flip : ∀{w t A} → w ⊨[ neg t ] (atom A) → w ⊨[ t ] ¬ A
  both : ∀{w t P Q} → w ⊨[ t ] P → w ⊨[ t ] Q → w ⊨[ t ] P ∧ Q
  somewhere : ∀{w a} → a ∈ w → w ⊨[ + ] atom a
  nowhere : ∀{w a} → a ∉ w → w ⊨[ - ] atom a

open import Data.Product

-- A list containing pairs of polarities and predicates
NPred : Set
NPred = List (Polarity × R)

-- Operational Semantics: normalisation function
infixr 3 _↓[_]_
_↓[_]_ : Form → Polarity → NPred → NPred
P ∧ Q ↓[ t ] N = Q ↓[ t ] P ↓[ t ] N
¬ x ↓[ t ] N = (neg t , x) ∷ N
atom x ↓[ t ] N = (t , x) ∷ N

--------------------------------------------------------


_∈⟨_⟩ : World → NPred → Set
w ∈⟨ N ⟩ = (∀ a → (+ , a) ∈ N → a ∈ w) × (∀ a → (- , a) ∈ N → a ∉ w)


open import Data.List.Any

--------------------------------------------------------
-- Code for the Soundness and Completeness proofs
--
-- We first prove some auxiliary lemmas:

weakening : ∀ t₁ t₂ P Q N a -> (t₁ , a) ∈ (P ↓[ t₂ ] N) -> (t₁ , a) ∈ (Q ↓[ t₂ ] P ↓[ t₂ ] N)
weakening t₁ t₂ P (Q ∧ Q₁) N a x = weakening t₁ t₂ Q Q₁ (P ↓[ t₂ ] N) a (weakening t₁ t₂ P Q N a x)
weakening t₁ t₂ P (¬ x₁) N a x = there x
weakening t₁ t₂ P (atom x₁) N a x = there x

--
-- ∈⟨⟩-weakening
--
∈⟨⟩-weakening : ∀ w t P Q N -> w ∈⟨ Q ↓[ t ] P ↓[ t ] N ⟩ -> (w ∈⟨ P ↓[ t ] N ⟩)
∈⟨⟩-weakening w t P Q N (pos , neg)
  = (λ a1 x → pos a1 (weakening + t P Q N a1 x))
  , (λ a1 x x2 → neg a1 (weakening - t P Q N a1 x) x2)

lemma-transport-r : ∀ t P M N →
  ((P ↓[ t ] M) ++ N) ≡ (P ↓[ t ] (M ++ N))
lemma-transport-r t (P ∧ Q) M N = trans
  (lemma-transport-r t Q (P ↓[ t ] M) N)
  (cong (λ x → Q ↓[ t ] x) (lemma-transport-r t P M N))
lemma-transport-r t (¬ A) M N = refl
lemma-transport-r t (atom x) M N = refl


-- older stdlib
{-
open import Algebra 
++-assoc :  (x x₁ x₂ : List ( Polarity × R)) →  (x ++ x₁) ++ x₂ ≡ x ++ x₁ ++ x₂
++-assoc = Monoid.assoc (monoid (Polarity × R))-}

--newer stdlib
open import Data.List.Properties


lemma-transport-l : ∀ t P M N →
  (M ++ (P ↓[ t ] N)) ≡ ((M ++ (P ↓[ t ] [])) ++ N)
lemma-transport-l t (P ∧ P₁) M N
  = sym (trans (++-assoc M (P₁ ↓[ t ] P ↓[ t ] []) N)
               (cong (λ x → M ++ x)
                     (trans (lemma-transport-r t P₁ (P ↓[ t ] []) N)
                            (cong (λ x → P₁ ↓[ t ] x) (lemma-transport-r t P [] N)))))
lemma-transport-l t (¬ x) M N = sym (++-assoc M (((neg t) , x) ∷ []) N)
lemma-transport-l t (atom x) M N = sym (++-assoc M ((t , x) ∷ []) N)

open import AnyLemma

∈-transport-l : ∀ a {t1} t P M N -> (t1 , a) ∈ ( M ++ (P ↓[ t ] N))
  -> (t1 , a) ∈ ((M ++ (P ↓[ t ] [])) ++ N)
∈-transport-l a₁ {t₁} t P M N x
  = any-cong {zero} {zero} {Polarity × R} {λ _ → R} x (lemma-transport-l t P M N)


∈-transport-r : ∀ a {t1} t P M N -> (t1 , a) ∈ ((M ++ (P ↓[ t ] [])) ++ N)
  -> (t1 , a) ∈ ( M ++ (P ↓[ t ] N))
∈-transport-r a₁ t P M N x
  = any-cong {zero} {zero} {Polarity × R} {λ _ → R}  x (sym (lemma-transport-l t P M N))

--
-- exchange for the underlying representation (was cAny)
--
∈-exchange : ∀ a {t} t1 t2 P Q N1 N2 -> (t , a) ∈ ( N1 ++ (P ↓[ t1 ] Q ↓[ t2 ] N2))
  -> (t , a) ∈ (N1 ++ (Q ↓[ t2 ] P ↓[ t1 ] N2))
∈-exchange a₁ t1 t2 P (Q ∧ R) N1 N2 x
  = ∈-transport-r a₁ t2 R N1 (Q ↓[ t2 ] P ↓[ t1 ] N2)
      (∈-exchange a₁ t1 t2 P Q (N1 ++ (R ↓[ t2 ] [])) N2
            (∈-transport-l a₁ t2 R N1 (P ↓[ t1 ] Q ↓[ t2 ] N2)
                             (∈-exchange a₁ t1 t2 P R N1 (Q ↓[ t2 ] N2) x)))
∈-exchange a₁ t1 t2 (P ∧ Q) (¬ A) N1 N2 x
  = ∈-exchange a₁ t1 t2 Q (¬ A) N1 (P ↓[ t1 ] N2)
    (∈-transport-r a₁ t1 Q N1 ((¬ A) ↓[ t2 ] P ↓[ t1 ] N2)
      (∈-exchange a₁ t1 t2 P (¬ A) (N1 ++ (Q ↓[ t1 ] [])) N2
        (∈-transport-l a₁ t1 Q N1 (P ↓[ t1 ] (¬ A) ↓[ t2 ] N2) x)))
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) [] N2 (here px) = there (here px)
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) (x₂ ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) (x₂ ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (¬ x₁) (¬ A) N1 N2 x)
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) [] N2 (here px) = there (here px)
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) (x₂ ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (atom x₁) (¬ A) (x₂ ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (atom x₁) (¬ A) N1 N2 x)
∈-exchange a₁ t1 t2 (P ∧ Q) (atom x₁) N1 N2 x
  = ∈-exchange a₁ t1 t2 Q (atom x₁) N1 (P ↓[ t1 ] N2)
    (∈-transport-r a₁ t1 Q N1 ((atom x₁) ↓[ t2 ] P ↓[ t1 ] N2)
      (∈-exchange a₁ t1 t2 P (atom x₁) (N1 ++ (Q ↓[ t1 ] [])) N2
        (∈-transport-l a₁ t1 Q N1 (P ↓[ t1 ] (atom x₁) ↓[ t2 ] N2) x)))
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) [] N2 (here px) = there (here px)
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) (x₂ ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (¬ A) (atom x₁) (x₂ ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (¬ A) (atom x₁) N1 N2 x)
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) [] N2 (here refl) = there (here refl)
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) [] N2 (there (here px)) = here px
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) [] N2 (there (there x)) = there (there x)
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) ((t3 , x₃) ∷ N1) N2 (here px) = here px
∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) ((t3 , x₃) ∷ N1) N2 (there x)
  = there (∈-exchange a₁ t1 t2 (atom x₂) (atom x₁) N1 N2 x)

--
-- ∈⟨⟩-exchange lemma 
--
-- a wrapper around ∈-exchange
--
∈⟨⟩-exchange : ∀ w t1 t2 P Q N1 N2 -> w ∈⟨ N1 ++ (P ↓[ t1 ] Q ↓[ t2 ] N2) ⟩
  -> w ∈⟨ N1 ++ (Q ↓[ t2 ] P ↓[ t1 ] N2) ⟩
∈⟨⟩-exchange w t1 t2 P (Q ∧ R) N1 N2 (fst , snd)
  = (λ { a₁ x₁ → fst a₁ (∈-exchange a₁ t2 t1 R P N1 (Q ↓[ t2 ] N2)
       (∈-transport-r a₁ t2 R N1 (P ↓[ t1 ] Q ↓[ t2 ] N2)
         (∈-exchange a₁ t2 t1  Q P  (N1 ++ (R ↓[ t2 ] [])) N2
           (∈-transport-l a₁ t2 R N1 (Q ↓[ t2 ] P ↓[ t1 ] N2) x₁))))})
  , (λ { a₁ x x₁ → snd a₁
       ( ∈-exchange a₁ t2 t1 R P N1 (Q ↓[ t2 ] N2)
         (∈-transport-r a₁ t2 R N1 (P ↓[ t1 ] Q ↓[ t2 ] N2)
           (∈-exchange a₁ t2 t1 Q P  (N1 ++ (R ↓[ t2 ] [])) N2
             (∈-transport-l a₁ t2 R N1 (Q ↓[ t2 ] P ↓[ t1 ] N2) x)))  )
      x₁})
∈⟨⟩-exchange w t1 t2 P (¬ A) N1 N2 (fst , snd)
  = (λ {a₁ x₁ → fst a₁ (∈-exchange a₁ (neg t2) t1 (atom A) P N1 N2 x₁)})
  , (λ {a₁ x x₁ → snd a₁ (∈-exchange a₁ (neg t2) t1 (atom A) P N1 N2 x) x₁})
∈⟨⟩-exchange w t1 t2 P (atom x₁) N1 N2 (fst , snd)
  = (λ {a₁ x → fst a₁ (∈-exchange a₁ t2 t1 (atom x₁) P N1 N2 x)})
  , (λ {a₁ x x₂ → snd a₁ (∈-exchange a₁ t2 t1 (atom x₁) P N1 N2 x) x₂})


--
-- soundness of operational semantics (Theorem 1)
--
↓-sound : ∀{w t P} → w ∈⟨ P ↓[ t ] [] ⟩ → w ⊨[ t ] P
↓-sound {w} {t} {P ∧ Q} x
  = both (↓-sound (∈⟨⟩-weakening w t P Q [] x))
         (↓-sound (∈⟨⟩-weakening w t Q P [] (∈⟨⟩-exchange w t t Q P [] [] x )))
↓-sound {w} {+} {¬ A} (proj1 , proj2) = flip (nowhere (proj2 A (here refl)))
↓-sound {w} { - } {¬ A} (proj1 , proj2) = flip (somewhere (proj1 A (here (refl))))
↓-sound {w} {+} {atom p} (proj1 , proj2) = somewhere (proj1 p (here refl))
↓-sound {w} { - } {atom p} (proj1 , proj2) = nowhere (proj2 p (here refl))


open import Data.Sum

strengthening : ∀ t₁ t₂ P Q N a -> (t₁ , a) ∈ (Q ↓[ t₂ ] P ↓[ t₂ ] N)
  -> ((t₁ , a) ∈ (Q ↓[ t₂ ] N)) ⊎  ((t₁ , a) ∈ (P ↓[ t₂ ] N))
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x
  with strengthening t₁ t₂ Q₁ Q₂ (P₁ ↓[  t₂ ] P ↓[ t₂ ] N) a x
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁
  with strengthening t₁ t₂ Q₂ P₁ (P ↓[ t₂ ] N) a (∈-exchange a t₂ t₂ Q₂ P₁ [] (P ↓[ t₂ ] N) x₁)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₁ x₂ = inj₂ x₂
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₂ y
  with strengthening t₁ t₂ P Q₂ N a y
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₂ y | inj₁ x₂
  = inj₁ (∈-exchange a t₂ t₂ Q₁ Q₂ [] N (weakening t₁ t₂ Q₂ Q₁ N a x₂))
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₁ x₁ | inj₂ y | inj₂ y₁
  = inj₂ (weakening t₁ t₂ P P₁ N a y₁)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y
  with strengthening t₁ t₂ Q₁ P₁ (P ↓[ t₂ ] N) a (∈-exchange a t₂ t₂ Q₁ P₁ [] (P ↓[ t₂ ] N) y)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₁ x₂ = inj₂ x₂
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₂ y₂
  with strengthening t₁ t₂ P Q₁ N a y₂
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₂ y₂ | inj₁ x₁ = inj₁ (weakening t₁ t₂ Q₁ Q₂ N a x₁)
strengthening t₁ t₂ (P ∧ P₁) (Q₁ ∧ Q₂) N a x | inj₂ y | inj₂ y₂ | inj₂ y₁ = inj₂ (weakening t₁ t₂ P P₁ N a y₁)
strengthening t₁ t₂ (¬ x₁) (Q₁ ∧ Q₂) N a x with ∈-exchange a t₂ t₂ (Q₁ ∧ Q₂) (¬ x₁) [] N x
strengthening t₁ t₂ (¬ x₁) (Q₁ ∧ Q₂) N a x | here px = inj₂ (here px)
strengthening t₁ t₂ (¬ x₁) (Q₁ ∧ Q₂) N a x | there res = inj₁ res
strengthening t₁ t₂ (atom x₁) (Q₁ ∧ Q₂) N a x with ∈-exchange a t₂ t₂ (Q₁ ∧ Q₂) (atom x₁) [] N x
strengthening t₁ t₂ (atom x₁) (Q₁ ∧ Q₂) N a x | here px = inj₂ (here px)
strengthening t₁ t₂ (atom x₁) (Q₁ ∧ Q₂) N a x | there res = inj₁ res
strengthening t₁ t₂ P (¬ x₁) N a (here px) = inj₁ (here px)
strengthening t₁ t₂ (P ∧ P₁) (¬ x₁) N a (there x) = inj₂ x
strengthening t₁ t₂ (¬ x₂) (¬ x₁) N a (there (here px)) = inj₂ (here px)
strengthening t₁ t₂ (¬ x₂) (¬ x₁) N a (there (there x)) = inj₁ (there x)
strengthening t₁ t₂ (atom x₂) (¬ x₁) N a (there (here px)) = inj₂ (here px)
strengthening t₁ t₂ (atom x₂) (¬ x₁) N a (there (there x)) = inj₁ (there x)
strengthening t₁ t₂ P (atom x₁) N a (here px) = inj₁ (here px)
strengthening t₁ t₂ P (atom x₁) N a (there x) = inj₂ x

helperPos :  ∀ w t P Q N a → (w ∈⟨ P ↓[ t ] N ⟩) -> (w ∈⟨ Q ↓[ t ] N ⟩)
           -> (+ , a) ∈ (Q ↓[ t ] P ↓[ t ] N)
           -> a ∈ w
helperPos w t P Q N a x x1 x2 with (strengthening + t P Q N) a x2
helperPos w t P Q N a x x1 x2 | inj₁ y = proj₁ x1 a y
helperPos w t P Q N a x x1  x2 | inj₂ y = proj₁ x a y

open import Data.Empty

helperNeg : ∀ w t P Q N a → (w ∈⟨ P ↓[ t ] N ⟩) -> (w ∈⟨ Q ↓[ t ] N ⟩)
            -> (- , a) ∈ (Q ↓[ t ] P ↓[ t ] N)
            -> a ∉ w
helperNeg w t P Q N a x x1 x2 x3 with (strengthening - t P Q N) a x2
helperNeg w t P Q N a x x1 x2 x3 | inj₁ y = proj₂ x1 a y x3
helperNeg w t P Q N a x x1 x2 x3 | inj₂ y = proj₂ x a y x3


∈⟨⟩-strengthening : ∀ w t P Q N -> (w ∈⟨ P ↓[ t ] N ⟩) -> (w ∈⟨ Q ↓[ t ] N ⟩)
  -> w ∈⟨ Q ↓[ t ] P ↓[ t ] N ⟩
∈⟨⟩-strengthening w t P Q N p n
  = (λ { a x → helperPos w t P Q N a p n x })
    , (λ {a x x2 → helperNeg w t P Q N a p n x x2})


--
-- Completeness of operational semantics (Theorem 1)
--
↓-complete : ∀{w t P} → w ⊨[ t ] P → w ∈⟨ P ↓[ t ] [] ⟩
↓-complete {w} {t} {P ∧ Q} (both x y)
  = ∈⟨⟩-strengthening w t P Q [] (↓-complete x) (↓-complete y)
↓-complete {w} {+} {¬ x₁} (flip (nowhere x))
  = (λ { a (here ())
       ; a (there ())})
  , (λ { a (here refl) x₃ → x x₃
       ; a (there ()) x₃})
↓-complete {w} { - } {¬ x₁} (flip (somewhere x))
  = (λ { a (here refl) → x
       ; a (there ())})
  , (λ { a (here ()) x₃
       ; a (there ()) x₃})
↓-complete {w} { .+ } {atom x₁} (somewhere x)
  = (λ { a (here refl) → x
       ; a (there ()) })
  , (λ { a (here ()) x₃
       ; a (there ()) x₃ })
↓-complete {w} { .- } {atom x₁} (nowhere x)
  = (λ { a (here ())
       ; a (there ())})
  , (λ { a (here refl) x₃ → x x₃
       ; a (there ()) x₃})

---------------------------------------------------------------
-- Figure 7: Plans
--

data Plan : Set where
  doAct : Action → Plan → Plan
  halt : Plan

---------------------------------------------------------------
-- Figure 8
-- 

-- Context
Γ : Set
Γ = Action → NPred × NPred

---------------------------------------------------------------
-- Section 4: Plans as Proof terms
-- Figure 9
--

-- Subtyping
infix 3 _<:_
data _<:_ : NPred → NPred → Set where
  []<:_ : ∀ N → [] <: N
  atom<: : ∀{t x N M} → (t , x) ∈ M → N <: M → (t , x) ∷ N <: M

---------------------------------------------------------------

open import Relation.Nullary
open IsDecEquivalence isDE

del : R → NPred → NPred
del x [] = []
del x ((t' , x') ∷ M) with x ≟ x'
del x ((t' , x') ∷ M) | yes p =  del x M
del x ((t' , x') ∷ M) | no ¬p = (t' , x') ∷ del x M 

del-spec : ∀ t x N → (t , x) ∉ del x N
del-spec t x [] ()
del-spec t x ((t' , y) ∷ N) tx∈N' with x ≟ y
del-spec t x ((t' , y) ∷ N) tx∈N' | yes p = del-spec t x N tx∈N'
del-spec .t' .y ((t' , y) ∷ N) (here refl) | no ¬p = ¬p _≡_.refl
del-spec t x ((t' , y) ∷ N) (there tx∈N') | no ¬p =  del-spec t x N tx∈N'


del-∈ : ∀{M y x} → x ∈ del y M → x ∈ M
del-∈ {[]}             ()
del-∈ {(t , z) ∷ M}{y} x∈ with y ≟ z
del-∈ {(t , z) ∷ M} {y} x∈ | yes p = there (del-∈ x∈)
del-∈ {(t , z) ∷ M} {y} (here refl) | no ¬p = here _≡_.refl
del-∈ {(t , z) ∷ M} {y} (there x∈) | no ¬p = there (del-∈ x∈) 


-- Override operator
_⊔N_ : NPred → NPred → NPred
M ⊔N [] = M
M ⊔N ((t , x) ∷ N) = (t , x) ∷ del x M ⊔N N


⊔-right-bias : ∀{N x M} → x ∈ N → x ∈ M ⊔N N
⊔-right-bias {[]}    ()
⊔-right-bias {y ∷ N} (here refl) = here _≡_.refl 
⊔-right-bias {y ∷ N}{x}{M} (there x∈N) = there (⊔-right-bias x∈N) 

⊔-union : ∀{N t x M} → (t , x) ∈ M ⊔N N → (t , x) ∈ M × (neg t , x) ∉ N ⊎ (t , x) ∈ N
⊔-union {[]} x∈M = inj₁ (x∈M , λ ())
⊔-union {x ∷ N} (here refl)   = inj₂ (here _≡_.refl)
⊔-union {x ∷ N}{t}{y}{M} (there x∈M⊔N) = h (⊔-union {N}{t}{y} x∈M⊔N)
  where h : (t , y) ∈ del (proj₂ x) M × (neg t , y) ∉ N ⊎ (t , y) ∈ N → (t , y) ∈ M × (neg t , y) ∉ x ∷ N ⊎ (t , y) ∈ x ∷ N
        h (inj₁ (ty∈ , -ty∉N)) = inj₁ (del-∈ ty∈ , h') where
          h' : (neg t , y) ∉ x ∷ N
          h' (here refl) = del-spec t y M ty∈
          h' (there -ty∈N) = -ty∉N -ty∈N
        h (inj₂ pf) = inj₂ (there pf)

---------------------------------------------------------------
-- Figure 10: well-typing relation
--
data _⊢_∶_↝_ : Γ → Plan → NPred → NPred → Set where
  halt : ∀{Γ M' M} → M' <: M → Γ ⊢ halt ∶ M ↝ M'
  seq : ∀{α M₁' M₁ M₂ M₃ Γ f}
      → M₁' <: M₁
      → Γ α ≡ (M₁' , M₂)
      → Γ ⊢ f ∶ M₁ ⊔N M₂ ↝ M₃
      → Γ ⊢ doAct α f ∶ M₁ ↝ M₃
---------------------------------------------------------------
-- Figure 12
--

-- Action Handler
ActionHandler : Set
ActionHandler = Action → World → World

-- Evalutation function
⟦_⟧ : Plan → ActionHandler → World → World
⟦ doAct α f ⟧ σ w = ⟦ f ⟧ σ (σ α w)
⟦ halt ⟧ σ w = w


-- Well formed handler
WfHandler : Γ → ActionHandler → Set
WfHandler Γ σ =
  ∀{α M M' N} → Γ α ≡ (M' , N) → M' <: M → ∀{w} → w ∈⟨ M ⟩ → σ α w ∈⟨ M ⊔N N ⟩

remove : R → World → World
remove x [] = []
remove x (y ∷ w) with x ≟ y
remove x (y ∷ w) | yes p = remove x w
remove x (y ∷ w) | no ¬p = y ∷ remove x w

remove-other : ∀{w x} → x ∈ w → ∀{y} → x ≢ y → x ∈ remove y w
remove-other {[]}    x∈w x≢y = x∈w
remove-other {z ∷ w} x∈w {y} x≢z with y ≟ z
remove-other {z ∷ w} (here _≡_.refl) {y} x≢z | yes p = ⊥-elim (x≢z (IsEquivalence.sym (IsDecEquivalence.isEquivalence isDE) p))
remove-other {z ∷ w} (there x∈w) {y} x≢z | yes p = remove-other x∈w x≢z
remove-other {z ∷ w} (here px) {y} x≢z | no ¬p = here px
remove-other {z ∷ w} (there x∈w) {y} x≢z | no ¬p = there (remove-other x∈w x≢z)

remove-spec : (x : R) (w : World) → x ∉ remove x w
remove-spec x [] = λ ()
remove-spec x (y ∷ w) with  x ≟ y
remove-spec x (y ∷ w) | yes p = remove-spec x w
remove-spec x (y ∷ w) | no ¬p = contr
  where
    contr : x ∉ y ∷ remove x w
    contr (here x≡y) = ¬p x≡y
    contr (there x∈) = remove-spec x w x∈

-- World constructor from state
σα : NPred → World → World
σα [] w = w
σα ((+ , x) ∷ N) w = x ∷ σα N w
σα ((- , x) ∷ N) w = remove x (σα N w)

-- Canonical Handler
canonical-σ : Γ → ActionHandler
canonical-σ Γ α = σα (proj₂ (Γ α))

---------------------------------------------------------------

∉-tail : {A : Set} {xs : List A} {x y : A} → x ∉ y ∷ xs → x ∉ xs
∉-tail x∉y∷ys x∈ys = x∉y∷ys (there x∈ys)

remove-resp-∈ : ∀{N x y} → x ∈ remove y N → x ∈ N
remove-resp-∈ {[]}    x∈ = x∈
remove-resp-∈ {z ∷ N}{x}{y} x∈ with y ≟ z
remove-resp-∈ {z ∷ N}{x}{y} x∈ | yes refl = there (remove-resp-∈ {N} x∈)
remove-resp-∈ {z ∷ N} {x} {y} (here refl) | no y≢x = here _≡_.refl
remove-resp-∈ {z ∷ N} {x} {y} (there x∈)  | no y≢x = there (remove-resp-∈ x∈)

remove-resp-∉ : ∀{N x} → x ∉ N → ∀{y} → x ∉ remove y N
remove-resp-∉ {[]}    x∉N x∈N' = x∉N x∈N'
remove-resp-∉ {x ∷ N} x∉N {y} x∈N' with y ≟ x
remove-resp-∉ {x ∷ N} x∉N {.x} x∈N' | yes refl = remove-resp-∉ (∉-tail x∉N) x∈N'
remove-resp-∉ {x ∷ N} x∉N {y} (here refl)  | no x≢y = x∉N (here _≡_.refl)
remove-resp-∉ {x ∷ N} x∉N {y} (there x∈N') | no x≢y = remove-resp-∉ (∉-tail x∉N) x∈N'

sym≢ : {A : Set} → {x y : A} → x ≢ y → y ≢ x
sym≢ x≢y refl = x≢y _≡_.refl

postulate
  implicit-consistency-assumption : (t : Polarity) (x : R) → ∀ N → (t , x) ∈ N → (neg t , x) ∉ N

σα-insert : ∀{N x} → (+ , x) ∈ N → ∀ w → x ∈ σα N w
σα-insert {.(_ ∷ _)} (here refl) w = here _≡_.refl
σα-insert {(- , y) ∷ N}{x} (there +x∈N) w with y ≟ x
σα-insert {(- , y) ∷ N}{.y} (there +y∈N) w | yes refl = ⊥-elim (implicit-consistency-assumption - y ((- , y) ∷ N) (here _≡_.refl) (there +y∈N))
σα-insert {(- , y) ∷ N}{x} (there +x∈N)  w | no y≢x = remove-other (σα-insert +x∈N w) (sym≢ y≢x)
σα-insert {(+ , y) ∷ N}{x} (there +x∈N) w with y ≟ x
σα-insert {(+ , y) ∷ N}{.y} (there +x∈N) w | yes refl = here _≡_.refl
σα-insert {(+ , y) ∷ N}{x} (there +x∈N)  w | no y≢x = there (σα-insert +x∈N w)

σα-keep : ∀{x w} → x ∈ w → ∀{N} → (- , x) ∉ N → x ∈ σα N w
σα-keep     x∈w {[]}          -x∉N  = x∈w
σα-keep {x} x∈w {(+ , y) ∷ N} -ty∉N = there (σα-keep x∈w (∉-tail -ty∉N))
σα-keep {x} x∈w {(- , y) ∷ N} -ty∉N with x ≟ y
σα-keep {x} x∈w {(- , .x) ∷ N} -ty∉N | yes refl = ⊥-elim (-ty∉N (here _≡_.refl))
σα-keep {x} x∈w {(- , y) ∷ N} -ty∉N  | no x≢y = remove-other (σα-keep x∈w (∉-tail -ty∉N)) x≢y

σα-delete : ∀{x N} → (- , x) ∈ N → ∀ w → x ∉ σα N w
σα-delete {x}{[]}    () w
σα-delete {x}{y ∷ N} (here refl) w = remove-spec x (σα N w)
σα-delete {x} {(+ , y) ∷ N} (there -x∈N) w with y ≟ x
σα-delete {x} {(+ , y) ∷ N} (there -x∈N) w | yes refl = ⊥-elim (implicit-consistency-assumption + y ((+ , y) ∷ N) (here _≡_.refl) (there -x∈N))
σα-delete {x} {(+ , y) ∷ N} (there -x∈N) w | no y≢x = contr where
  contr : x ∉ y ∷ σα N w
  contr (here x≡y) = y≢x (Relation.Binary.PropositionalEquality.sym x≡y)
  contr (there x∈) = σα-delete -x∈N w x∈
σα-delete {x} {(- , y) ∷ N} (there -x∈N) w = remove-resp-∉ (σα-delete -x∈N w) {y}

σα-source : ∀{N x w} → x ∈ σα N w → (+ , x) ∈ N ⊎ x ∈ w
σα-source {[]}          {x} x∈ = inj₂ x∈
σα-source {(+ , y) ∷ N} {x} x∈ with x ≟ y
σα-source {(+ , .x) ∷ N} {x}{w} x∈ | yes refl = inj₁ (here  _≡_.refl)
σα-source {(+ , y) ∷ N}  {x}{w} (here refl) | no y≢y = ⊥-elim (y≢y _≡_.refl)
σα-source {(+ , y) ∷ N}  {x}{w} (there x∈)  | no x≢y = h (σα-source x∈) where
  h : (+ , x) ∈ N ⊎ x ∈ w → (+ , x) ∈ (+ , y) ∷ N ⊎ x ∈ w
  h (inj₁ +x∈N) = inj₁ (there +x∈N)
  h (inj₂ x∈w) = inj₂ x∈w
σα-source {(- ,  y) ∷ N} {x} x∈ with x ≟ y
σα-source {(- , .x) ∷ N} {x}{w} x∈ | yes refl = ⊥-elim (remove-spec x (σα N w) x∈)
σα-source {(- ,  y) ∷ N} {x}{w} x∈ | no x≢y = h (σα-source (remove-resp-∈ x∈)) where
  h : (+ , x) ∈ N ⊎ x ∈ w → (+ , x) ∈ (- , y) ∷ N ⊎ x ∈ w
  h (inj₁ +x∈N) = inj₁ (there +x∈N)
  h (inj₂ x∈w)  = inj₂ x∈w

σα-keep-∉ : ∀{x w} → x ∉ w → ∀{N} → (+ , x) ∉ N → x ∉ σα N w
σα-keep-∉        x∉w {[]}          +x∉N x∈w = x∉w x∈w
σα-keep-∉ {x}{w} x∉w {(+ , y) ∷ N} +x∉N (here refl) = +x∉N (here _≡_.refl)
σα-keep-∉ {x}{w} x∉w {(+ , y) ∷ N} +x∉N (there x∈) = σα-keep-∉ x∉w (∉-tail +x∉N) x∈
σα-keep-∉ {x}{w} x∉w {(- , y) ∷ N} +x∉N x∈ with x ≟ y
σα-keep-∉ {x}{w} x∉w {(- , .x) ∷ N} +x∉N x∈ | yes refl = remove-spec x (σα N w) x∈
σα-keep-∉ {x}{w} x∉w {(- , y) ∷ N}  +x∉N x∈ | no x≢y = h (σα-source (remove-resp-∈ x∈)) where
  h : (+ , x) ∈ N ⊎ x ∈ w → ⊥
  h (inj₁ +x∈N) = +x∉N (there +x∈N)
  h (inj₂ x∈w)  = x∉w x∈w


-- Proposition 1: The canonical handler is well-formed

wf-canonical-σ : ∀ Γ → WfHandler Γ (canonical-σ Γ)
wf-canonical-σ Γ {α} {M} {.(proj₁ (Γ α))} {.(proj₂ (Γ α))} refl M'<:M {w} w∈⟨M⟩ =
  (λ a +a∈M → lt a (⊔-union +a∈M)) ,
  λ a -a∈M a∈w → rt a (⊔-union -a∈M) a∈w
  where lt : ∀ x → (+x∈M⊎N : (+ , x) ∈ M × (- , x) ∉ proj₂ (Γ α) ⊎ (+ , x) ∈ proj₂ (Γ α)) → x ∈ canonical-σ Γ α w
        lt x (inj₁ (+x∈M , -x∉N)) = σα-keep (proj₁ w∈⟨M⟩ x +x∈M) -x∉N
        lt x (inj₂ +x∈N) = σα-insert +x∈N w
        rt : ∀ x → (+x∈M⊎N : (- , x) ∈ M × (+ , x) ∉ proj₂ (Γ α) ⊎ (- , x) ∈ proj₂ (Γ α)) → x ∉ canonical-σ Γ α w
        rt x (inj₁ (-x∈M , +x∉N)) = σα-keep-∉ (proj₂ w∈⟨M⟩ x -x∈M) +x∉N
        rt x (inj₂ -x∈N) = σα-delete -x∈N w


<:-resp-∈ : ∀{N M} → N <: M → ∀{w} → w ∈⟨ M ⟩ → w ∈⟨ N ⟩
<:-resp-∈ ([]<: N) w∈⟨M⟩ = (λ _ ()) , λ _ ()
<:-resp-∈ (atom<: {t}{x}{N}{M} tx∈M N<:M) {w} w∈⟨M⟩ = lt , rt where
  ih : w ∈⟨ N ⟩
  ih = <:-resp-∈ N<:M w∈⟨M⟩
  lt : ∀ a' → (+ , a') ∈ (t , x) ∷ N → a' ∈ w
  lt a' (here px) = proj₁ w∈⟨M⟩ a' (subst (λ tx → tx ∈ M) (Relation.Binary.PropositionalEquality.sym px) tx∈M)
  lt a' (there +a'∈N) = proj₁ ih a' +a'∈N
  rt : ∀ a' → (- , a') ∈ (t , x) ∷ N → a' ∉ w
  rt a' (here px) a'∈w =
    proj₂ w∈⟨M⟩ a' (subst (λ tx → tx ∈ M) (Relation.Binary.PropositionalEquality.sym px) tx∈M) a'∈w
  rt a' (there -a'∈N) a'∈w = proj₂ ih a' -a'∈N a'∈w

---------------------------------------------------------------
-- Theorem 2: Soundness of evaluation of normalised formula
--

sound : ∀{w σ M Γ f N}
      → WfHandler Γ σ
      → Γ ⊢ f ∶ M ↝ N
      → w ∈⟨ M ⟩
      → ⟦ f ⟧ σ w ∈⟨ N ⟩
sound wfσ (halt N<:M) w∈⟨M⟩ = <:-resp-∈ N<:M w∈⟨M⟩
sound {w}{σ}{M} wfσ (seq {α}{M₁'}{M₁}{M₂} M₁'<:M Γα≡M₁',M₂ Γ⊢f∶M⊔M₂↝N) w∈⟨M⟩ =
  sound wfσ Γ⊢f∶M⊔M₂↝N σαw∈⟨M⊔NM₂⟩
  where σαw∈⟨M⊔NM₂⟩ : σ α w ∈⟨ M ⊔N M₂ ⟩ 
        σαw∈⟨M⊔NM₂⟩ = wfσ {M = M} Γα≡M₁',M₂ M₁'<:M w∈⟨M⟩

---------------------------------------------------------------
-- Theorem 3: Soundness of evaluation
--
_↓₊ : Form → NPred
P ↓₊ = P ↓[ + ] []

sound' : ∀{Γ f P Q σ}
       → WfHandler Γ σ
       → Γ ⊢ f ∶ (P ↓₊) ↝ (Q ↓₊)
       → ∀{w} → w ⊨[ + ] P
       → ⟦ f ⟧ σ w ⊨[ + ] Q
sound' {Γ}{f}{P}{Q}{σ} wfσ Γ⊢f∶P↓₊↝Q↓₊ {w} w⊨₊P = ↓-sound h
  where h : ⟦ f ⟧ σ w ∈⟨ Q ↓₊ ⟩
        h = sound wfσ Γ⊢f∶P↓₊↝Q↓₊ (↓-complete w⊨₊P)


---------------------------------------------------------------
