
open import Data.Unit renaming (⊤ to unit) 
open import Data.Sum 
open import Data.Product hiding (zipWith)
open import Data.Maybe hiding (zipWith)
open import Data.List  
open import Data.Nat  
open import Relation.Nullary 
open import Relation.Binary.PropositionalEquality hiding ([_])

open import PBG

module CFG where

  data cfterminal : Set where 
    #L : cfterminal
    #R : cfterminal
    Tile : tile -> cfterminal

  data nonteriminal : Set where 
    ROOT : nonteriminal
    _⌈_⌉_ : prec -> sort -> prec -> nonteriminal

  data cfsymbol : Set where 
    CFT : cfterminal -> cfsymbol
    CFN : nonteriminal -> cfsymbol
  
  CFG : Set₁
  CFG = nonteriminal -> (List cfsymbol) -> Set
  
  _〚_〛_[_] : prec -> pbsymbol -> prec -> sort -> cfsymbol   
  p 〚 Tile t 〛 q [ s ] = CFT (Tile t)
  p 〚 Sort s0 〛 q [ s ] with s0 ≡? s
  p 〚 Sort s0 〛 q [ s ] | yes eq = CFN (p ⌈ s ⌉ q)
  p 〚 Sort s0 〛 q [ s ] | no neq = CFN (⊥ ⌈ s0 ⌉ ⊥)

  bound-bounds-inner : ℕ -> (p : prec) -> (List prec) 
  bound-bounds-inner zero p = []
  bound-bounds-inner (suc zero) p = [ p ]
  bound-bounds-inner (2+ n) p = ⊥ ∷ bound-bounds-inner (suc n) p

  bound-bounds : ℕ -> (p : prec) -> (q : prec) -> (List prec) 
  bound-bounds zero p q = []
  bound-bounds (suc n) p q = q ∷ bound-bounds-inner n p

  list-forall : (List Set) -> Set 
  list-forall = foldr (_×_) unit

  tripZip : {A B C D : Set} -> (List A) -> (List B) -> (List C) -> (A -> B -> C -> D) -> (List D)
  tripZip (x ∷ xs) (y ∷ ys) (z ∷ zs) f = f x y z ∷ tripZip xs ys zs f
  tripZip _ _ _ _ = []

  data CFG-of-PBG {G : PBG} : CFG where 
    CPRoot : CFG-of-PBG ROOT ((CFT #L) ∷ ((CFN (⊥ ⌈ s# ⌉ ⊥)) ∷ [ CFT #R ]))
    CPSort : ∀{pL s pR q xs PL PR} ->
      (G s q) ⟹ xs ->
      ((head xs ≡ (just (Sort s))) ->  pL ≺[ s ] q) ->
      ((last xs ≡ (just (Sort s))) ->  q ≻[ s ] pR) ->
      list-forall (zipWith (λ qLi pLi → qLi ⪯[ s ] pLi) (bound-bounds (length xs) pL q) PL) ->
      list-forall (zipWith (λ pRi qRi → pRi ⪰[ s ] qRi) PR (reverse (bound-bounds (length xs) pR q))) ->
      CFG-of-PBG (pL ⌈ s ⌉ pR) (tripZip PL xs PR (λ pLi xi pRi → pLi 〚 xi 〛 pRi [ s ]))

  