
{-# OPTIONS --type-in-type --guardedness #-}


module Three where

open import Category.Applicative  using (RawApplicative)
open import Data.Char             using (Char)
open import Data.String as String using (String; fromList)
open import Data.Nat              using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties   -- you can use it all!
open import Data.Bool             using (Bool; true; false; if_then_else_)
open import Data.List   as L      using (List; []; _∷_; map)
open import Data.List.Properties  using (map-id; map-compose)
open import Data.Vec   as V
  using (Vec; []; _∷_; _++_; replicate; map; splitAt)
open import Data.Product          using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_; map)
open import Data.Sum   as Sum     using (_⊎_; inj₁; inj₂; map)
open import Data.Unit             using (⊤; tt)
open import Data.Empty            using (⊥; ⊥-elim)
open import Function   as F       using (_∘′_; id)
open import IO.Primitive          using (IO)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; cong-app; sym; trans; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary      using (¬_; Dec; yes; no)


data _≤_ : ℕ  -> ℕ -> Set where
  ≤-reflex : {n : ℕ } -> n ≤ n
  s≤s : {n m : ℕ } -> ( n ≤ m ) -> (  n  ≤  suc m )

zero≤n : ( n : ℕ )  -> zero ≤ n
zero≤n zero = ≤-reflex
zero≤n (suc n) = s≤s (zero≤n n)

transitive : { n m o : ℕ } -> n ≤ m -> m ≤ o -> n ≤ o
transitive {n} {.n} {o} ≤-reflex x₁ = x₁
transitive {n} {.(suc _)} {.(suc _)} (s≤s x) ≤-reflex = s≤s x
transitive {n} {.(suc _)} {.(suc _)} (s≤s x) (s≤s x₁) = s≤s (transitive x (transitive (s≤s ≤-reflex) x₁))

sucsuc : (n m : ℕ ) -> n ≤ m -> (suc n ) ≤ (suc m )
sucsuc n .n ≤-reflex = ≤-reflex
sucsuc n .(suc m) (s≤s {m = m} x) = transitive (sucsuc _ _ x) (s≤s ≤-reflex)

em : ( m n : ℕ ) -> ( m ≤ n ) ⊎ ( n ≤ m )
em zero n = inj₁ (zero≤n n)
em (suc m) zero = inj₂ (zero≤n (suc m))
em (suc m) (suc n) with em m n
em (suc m) (suc n) | inj₁ x = inj₁ (sucsuc _ _ x)
em (suc m) (suc n) | inj₂ y = inj₂ (sucsuc _ _ y)

≤reflrefl : {m n : ℕ} -> m ≤ n -> n ≤ m -> m ≡ n
≤reflrefl {m} {.m} ≤-reflex x₁ = refl
≤reflrefl {.(suc _)} {.(suc _)} (s≤s x) ≤-reflex = refl
≤reflrefl {.(suc m)} {.(suc _)} (s≤s x) (s≤s {m = m} x₁) with transitive (s≤s ≤-reflex) x₁ |  transitive (s≤s ≤-reflex) x
≤reflrefl {.(suc m)} {.(suc _)} (s≤s x) (s≤s {m = m} x₁) | a | b = cong suc (≤reflrefl b a)
  
data isorder : List ℕ -> Set where
  nil : isorder []
  one : {x : ℕ } -> isorder ( x ∷ [] )
  two : (x y : ℕ ) -> (L : List ℕ ) -> x ≤ y -> isorder ( y ∷ L ) -> isorder ( x ∷ y ∷ L )

orderlemma : (x : ℕ) -> (l : List ℕ ) -> isorder ( x ∷ l ) -> isorder l
orderlemma x .[] one = nil
orderlemma x .(y ∷ L) (two .x y L x₁ x₂) = x₂

{- https://stackoverflow.com/questions/17910737/termination-check-on-list-merge/17912550#17912550 -}
merge : List ℕ -> List ℕ -> List ℕ
merge [] x₁ = x₁
merge (x ∷ x₂) [] = x ∷ x₂ 
merge (x ∷ xs) (y ∷ ys) with em x y | merge xs (y ∷ ys ) | merge  (x ∷ xs )  ys
merge (x ∷ xs) (y ∷ ys) | inj₁ x₁ | b | c = b
merge (x ∷ xs) (y ∷ ys) | inj₂ y₁ | b | c = c

merge[] : ( x : List ℕ ) -> x ≡ merge x []
merge[] [] = refl
merge[] (x ∷ x₁) = refl

mergeswap : ( x y  : List ℕ ) ->  merge y x  ≡ merge x y 
mergeswap [] y = sym (merge[] y)
mergeswap (x ∷ x₁) [] = merge[] (x ∷ x₁)
mergeswap (x ∷ x₁) (x₂ ∷ y) with em x x₂ | em x₂ x 
mergeswap (x ∷ x₁) (x₂ ∷ y) | inj₁ x₃ | inj₁ x₄ with ≤reflrefl x₃ x₄
mergeswap (x ∷ x₁) (.x ∷ y) | inj₁ x₃ | inj₁ x₄ | refl = {!!}
mergeswap (x ∷ x₁) (x₂ ∷ y) | inj₁ x₃ | inj₂ y₁ = {!!}
mergeswap (x ∷ x₁) (x₂ ∷ y) | inj₂ y₁ | inj₁ x₃ = {!!}
mergeswap (x ∷ x₁) (x₂ ∷ y) | inj₂ y₁ | inj₂ y₂ with ≤reflrefl y₁ y₂
mergeswap (x ∷ x₁) (.x ∷ y) | inj₂ y₁ | inj₂ y₂ | refl = {!!}

correctness : ( xs ys : List ℕ ) -> isorder xs -> isorder ys -> isorder ( merge xs ys )
correctness = {!!}
