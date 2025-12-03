module Run where

open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.List
open import Data.List.All

open import Typing
open import Syntax
open import Global
open import Channel
open import Values
open import Session
open import Schedule

open import Examples
open import Aexamples

gas : ℕ → Gas
gas zero = Empty
gas (suc n) = More (gas n)


runex1 : Outcome
runex1 = start (gas 8) ex1

runex2 : Outcome
runex2 = start (gas 14) ex2

runex3 : Outcome
runex3 = start (gas 6) ex3

runex4 : Outcome
runex4 = start (gas 11) ex4

runex5 : Outcome
runex5 = start (gas 3) ex5

runex6 : Outcome
runex6 = start (gas 7) ex6

runaex1 : Outcome
runaex1 = start (gas 40) aex1

runasyncex1 : Outcome
runasyncex1 = start (gas 40) asyncex1

runasyncex2 : Outcome
runasyncex2 = start (gas 80) asyncex2
