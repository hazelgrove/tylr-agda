
open import Data.Unit renaming (⊤ to unit) 
open import Data.Sum hiding (map)
open import Data.Product hiding (zipWith; map)
open import Data.Maybe hiding (zipWith; map)
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
  GG = nonteriminal -> (List symbol) -> Set

  symbol-of-cfsymbol : cfsymbol -> symbol 
  symbol-of-cfsymbol (CFT τ) = ST (TT τ)
  symbol-of-cfsymbol (CFN σ) = SN σ

  data GG-of-CFG {H : CFG} : GG where 
    GCSub : ∀{σ χs} -> (H σ χs) -> (GG-of-CFG σ (map symbol-of-cfsymbol χs))



    