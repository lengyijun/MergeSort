open import Data.List
open import Data.Nat
  hiding (compare)
open import Data.Product
open import Function
open import Induction.Nat
open import Induction.WellFounded

split : {A : Set } -> List A → List A × List A
split [] = [] , []
split (x ∷ xs) with split xs
... | l , r = x ∷ r , l

Rel : Set -> Set₂
Rel x = x -> x -> Set₁

module WF{A : Set}( _<_ : Rel A) where
  data Acc(x : A ) : Set where
    acc : ( ? ) -> Acc x

