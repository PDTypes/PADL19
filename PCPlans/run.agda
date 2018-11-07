module run where

open import PCPlans_blocksworld
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Reflection
open import Data.List
open import Data.String


postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}



open import Tactic.Deriving.Eq

showC : C -> String
showC a = "a "
showC b = "b "
showC c = "c "

showR : R -> String
showR handEmpty = "handEmpty "
showR (onTable x) = "onTable " Data.String.++ showC x
showR (clear x) = "clear " Data.String.++ showC x
showR (holding x) = "holding " Data.String.++ showC x
showR (on x x1) = "on " Data.String.++ showC x Data.String.++ showC x1 

showEval : List R -> String
showEval [] = ""
showEval (x ∷ xs) = showR x Data.String.++ (showEval xs)

main : IO ⊤
main = putStrLn (showEval world-eval)
