
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum


postulate 
  char : Set 

data str : Set where 
  εs : str
  _∷_ : char -> str -> str

_·s_ : str -> str -> str
εs ·s Y = Y
(x ∷ X) ·s Y = x ∷ (X ·s Y)
 
data exp : Set where 
  ε : exp 
  _+_ : exp -> exp -> exp
  _·_ : exp -> exp -> exp
  _* : exp -> exp


data _⇒_ : exp -> str -> Set where 
  Empty : ε ⇒ εs
  PlusL : ∀{g1 g2 X} -> 
    g1 ⇒ X -> 
    (g1 + g2) ⇒ X
  PlusR : ∀{g1 g2 X} -> 
    g2 ⇒ X -> 
    (g1 + g2) ⇒ X
  Times : ∀{g1 g2 X Y} -> 
    g1 ⇒ X ->
    g2 ⇒ Y -> 
    (g1 · g2) ⇒ (X ·s Y)
  StarEmpty : ∀{g} -> 
    (g *) ⇒ εs
  StarAppend : ∀{g X Y} -> 
    g ⇒ X ->
    (g *) ⇒ Y -> 
    (g *) ⇒ (X ·s Y)
 
unique : exp -> Set 
unique = {!   !}

∷-inj : ∀{a b A B} -> (a ∷ A) ≡ (b ∷ B) -> (a ≡ b × A ≡ B)
∷-inj refl = refl , refl


split-append : ∀ {X Y A B x} -> 
  (X ·s Y) ≡ (A ·s (x ∷ B)) -> 
  (∃[ B-pre ] (X ≡ A ·s (x ∷ B-pre)) × (B ≡ (B-pre ·s Y))) ⊎
  (∃[ A-post ] (A ≡ X ·s A-post) × (Y ≡ A-post ·s (x ∷ B)))
split-append {εs} {A = A} eq = inj₂ (A , refl , eq)
split-append {x ∷ X} {A = εs} refl = inj₁ (X , refl , refl)
split-append {x ∷ X} {A = y ∷ A} eq with ∷-inj eq 
split-append {x ∷ X} {A = y ∷ A} eq | refl , eq' with split-append {X = X} eq'
split-append {x ∷ X} {A = y ∷ A} eq | refl , eq' | inj₁ (B-pre , refl , eq2) = inj₁ (B-pre , refl , eq2)
split-append {x ∷ X} {A = y ∷ A} eq | refl , eq' | inj₂ (A-post , refl , eq2) = inj₂ (A-post , refl , eq2)

thm : ∀{g A B C D AxB CxD x} -> 
  g ⇒ AxB -> 
  g ⇒ CxD -> 
  AxB ≡ (A ·s (x ∷ B)) -> 
  CxD ≡ (C ·s (x ∷ D)) -> 
  g ⇒ (A ·s (x ∷ D))
thm {ε} {εs} Empty d2 () eq2
thm {ε} {_ ∷ A} Empty d2 () eq2
thm {g + g₁} (PlusL d1) (PlusL d2) refl refl = PlusL (thm d1 d2 refl refl)
thm {g + g₁} (PlusR d1) (PlusR d2) refl refl = PlusR (thm d1 d2 refl refl)
thm {g + g₁} (PlusL d1) (PlusR d2) eq1 eq2 = {!   !} -- impossible with uniques
thm {g + g₁} (PlusR d1) (PlusL d2) eq1 eq2 = {!   !} -- impossible with uniques
thm {g · g₁} {A} {_} {C} (Times {X = X} d1 d2) (Times {X = X'} d3 d4) eq1 eq2 with split-append {X} eq1 | split-append {X'} eq2 
... | inj₁ (B-pre , refl , eq3) | inj₁ (B-pre' , refl , refl) = coerce (Times (thm d1 d3 refl refl) d4)
  where 
    coerce : ∀{x Y} -> 
      (g · g₁) ⇒ ((A ·s (x ∷ B-pre')) ·s Y) -> 
      (g · g₁) ⇒ (A ·s (x ∷ (B-pre' ·s Y)))
    coerce = {!   !} -- duh

... | inj₂ (A-post , refl , refl) | inj₂ (A-post' , refl , refl) = coerce (Times d1 (thm d2 d4 refl refl))
  where 
    coerce : ∀{x D} -> 
      (g · g₁) ⇒ (X ·s (A-post ·s (x ∷ D))) -> 
      (g · g₁) ⇒ ((X ·s A-post) ·s (x ∷ D))
    coerce = {!   !} -- duh

... | inj₁ x | inj₂ y = {!   !} -- impossible with uniques
... | inj₂ y | inj₁ x = {!   !} -- impossible with uniques

thm {g *} {εs} StarEmpty d2 () eq2
thm {g *} {x ∷ A} StarEmpty d2 () eq2
thm {g *} {εs} {C = εs} d1 StarEmpty eq1 ()
thm {g *} {εs} {C = x ∷ C} d1 StarEmpty eq1 ()
thm {g *} {x ∷ A} {C = εs} d1 StarEmpty eq1 ()
thm {g *} {x ∷ A} {C = _ ∷ C} d1 StarEmpty eq1 ()
thm {g *} (StarAppend {X = X} d1 d2) (StarAppend {X = X'} d3 d4) eq1 eq2 with split-append {X} eq1 | split-append {X'} eq2
... | inj₁ (B-pre , refl , refl) | inj₁ (B-pre' , refl , refl) = coerce (StarAppend (thm d1 d3 refl refl) d4) 
  where 
    coerce : ∀{x A Y} -> 
      (g *) ⇒ ((A ·s (x ∷ B-pre')) ·s Y) -> 
      (g *) ⇒ (A ·s (x ∷ (B-pre' ·s Y)))
    coerce = {!   !} -- duh
... | inj₂ (A-post , refl , refl) | inj₂ (A-post' , refl , refl) = coerce (StarAppend d1 (thm d2 d4 refl refl))
  where 
    coerce : ∀{x X D} -> 
      (g *) ⇒ (X ·s (A-post ·s (x ∷ D))) -> 
      (g *) ⇒ ((X ·s A-post) ·s (x ∷ D))
    coerce = {!   !} -- duh

... | inj₁ (B-pre , refl , refl) | inj₂ (A-post' , refl , refl) =  thm (StarAppend d1 d2) d4 equation refl
  where 
    equation : ∀{A x Y} -> ((A ·s (x ∷ B-pre)) ·s Y) ≡ (A ·s (x ∷ (B-pre ·s Y)))
    equation = {!   !} -- duh

... | inj₂ (A-post' , refl , refl) | inj₁ (B-pre , refl , refl) with thm d2 (StarAppend d3 d4) refl equation
  where 
    equation : ∀{C x Y} -> ((C ·s (x ∷ B-pre)) ·s Y) ≡ (C ·s (x ∷ (B-pre ·s Y)))
    equation = {!   !} -- duh
... | d5 = coerce (StarAppend d1 d5)
  where 
    coerce : ∀{Y x} -> 
      (g *) ⇒ (X ·s (A-post' ·s (x ∷ (B-pre ·s Y)))) -> 
      (g *) ⇒ ((X ·s A-post') ·s (x ∷ (B-pre ·s Y)))
    coerce = {!   !} -- duh