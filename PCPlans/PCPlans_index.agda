-- Proof Carrying Plans, (supporting Agda code)
-- by C.Schwaab, A.Hill, F.Farka and E.Komendantskaya
-- This file defines Planning languages as types, plans as proof terms approach to PDDL 

--------------------------------------------------------
--
module PCPlans_index where

--
-- The following module contains generic declarations and results in the paper

open import PCPlans


--------------------------------------------------------
-- module PCPlans_blockworlds

--
-- The following module contains encoding of planning domain and problem
-- in PDDL_examples/blocksworld_domain.pddl and PDDL_examples/blocksworls_problem.pddl

open import PCPlans_blocksworld

--------------------------------------------------------
-- module PCPlans_logistics

--
-- The following module contains encoding of planning domain and problem
-- in PDDL_examples/logistics_domain.pddl and PDDL_examples/blocksworls_problem.pddl

open import PCPlans_logistics

--------------------------------------------------------
-- The following module contains encoding of a simple example
-- that demonstrates violation of the implicit consistency assumpion
--

open import PCPlans_naughty
