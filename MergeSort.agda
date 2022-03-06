
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module MergeSort
  {ℓ a} {A : Set a}
  {_<_ : Rel A ℓ}
  (strictTotalOrder : IsStrictTotalOrder _≡_ _<_) where

open IsStrictTotalOrder strictTotalOrder
open import Data.List
open import Data.Nat
  hiding (compare)
open import Data.Product
open import Function
open import Data.Nat.Induction
open import Induction.WellFounded

mymerge : (xs ys : List A) → List A
mymerge [] ys = ys
mymerge xs [] = xs
mymerge (x ∷ xs) (y ∷ ys) with compare x y
... | tri< _ _ _ = x ∷ mymerge xs (y ∷ ys)
... | tri≈ _ _ _ = x ∷ mymerge xs (y ∷ ys)
... | tri> _ _ _ = y ∷ mymerge (x ∷ xs) ys
