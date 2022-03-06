module G where

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
open import Data.Nat
open import Relation.Binary

open DecTotalOrder decTotalOrder
  using (trans)

data Acc (n : ℕ) : Set where
  acc : (∀ m → m Data.Nat.< n → Acc m) → Acc n


WF : Set
WF = ∀ n → Acc n

<-wf : WF
<-wf n = acc (go n)
  where
  go : ∀ n m → m Data.Nat.< n → Acc m
  go zero    m       ()
  go (suc n) zero    _         = acc λ _ ()
  go (suc n) (suc m) (s≤s m<n) = acc λ o o<sm → go n o (trans o<sm m<n)

