
open import Data.Unit renaming (⊤ to unit) 
open import Data.Sum 
open import Data.Product hiding (zipWith)
open import Data.Maybe hiding (zipWith)
open import Data.List  
open import Data.Nat  
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding ([_])

open import PBG
open import CFG

module Main where

  data grout : Set where 
    〈〉 : sort -> grout
    〈〈 : sort -> grout
    〉〉 : sort -> grout
    〉〈 : sort -> grout

  data terminal : Set where 
    TT : cfterminal -> terminal
    TG : grout -> terminal

  data symbol : Set where 
    ST : terminal -> symbol
    SN : nonteriminal -> symbol
  
  -- "grout grammar"
  GG : Set₁
  GG = nonteriminal -> (List cfsymbol) -> Set



    