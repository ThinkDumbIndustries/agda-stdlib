------------------------------------------------------------------------
-- The Agda standard library
--
-- Sum combinators for setoid equality preserving functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Function.Setoid where

open import Data.Product.Base as Prod using (_,_)
open import Data.Sum.Base as Sum
open import Data.Sum.Relation.Binary.Pointwise as Pointwise
open import Relation.Binary
open import Function
open import Level

private
  variable
    a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Level
    a ℓ : Level
    A B C D : Setoid a ℓ

------------------------------------------------------------------------
-- Combinators for equality preserving functions

inj₁ₛ : Func A (A ⊎ₛ B)
inj₁ₛ = record { to = inj₁ ; cong = inj₁ }

inj₂ₛ : Func B (A ⊎ₛ B)
inj₂ₛ = record { to = inj₂ ; cong = inj₂ }

[_,_]ₛ : Func A C → Func B C → Func (A ⊎ₛ B) C
[ f , g ]ₛ = record
  { to   = [ to f , to g ]
  ; cong = λ where
    (inj₁ x∼₁y) → cong f x∼₁y
    (inj₂ x∼₂y) → cong g x∼₂y
  } where open Func

swapₛ : Func (A ⊎ₛ B) (B ⊎ₛ A)
swapₛ = [ inj₂ₛ , inj₁ₛ ]ₛ

------------------------------------------------------------------------
-- Function bundles

_⊎-⟶_ : Func A B → Func C D → Func (A ⊎ₛ C) (B ⊎ₛ D)
A→B ⊎-⟶ C→D = record
  { to    = Sum.map (to A→B) (to C→D)
  ; cong  = Pointwise.map (cong A→B) (cong C→D)
  } where open Func

_⊎-equivalence_ : Equivalence A B → Equivalence C D →
                  Equivalence (A ⊎ₛ C) (B ⊎ₛ D)
A⇔B ⊎-equivalence C⇔D = record
  { to        = Sum.map (to A⇔B) (to C⇔D)
  ; from      = Sum.map (from A⇔B) (from C⇔D)
  ; to-cong   = Pointwise.map (to-cong A⇔B) (to-cong C⇔D)
  ; from-cong = Pointwise.map (from-cong A⇔B) (from-cong C⇔D)
  } where open Equivalence

_⊎-injection_ : Injection A B → Injection C D →
                Injection (A ⊎ₛ C) (B ⊎ₛ D)
_⊎-injection_ {A = A} {B = B} {C = C} {D = D} A↣B C↣D = record
  { to        = Sum.map (to A↣B) (to C↣D)
  ; cong      = Pointwise.map (cong A↣B) (cong C↣D)
  ; injective = inj
  }
  where
  open Injection
  open Setoid (A ⊎ₛ C) using () renaming (_≈_ to _≈AC_)
  open Setoid (B ⊎ₛ D) using () renaming (_≈_ to _≈BD_)

  fg = Sum.map (to A↣B) (to C↣D)
  
  inj : Injective _≈AC_ _≈BD_ fg
  inj {inj₁ x} {inj₁ y} (inj₁ x∼₁y) = inj₁ (injective A↣B x∼₁y)
  inj {inj₂ x} {inj₂ y} (inj₂ x∼₂y) = inj₂ (injective C↣D x∼₂y)

_⊎-surjection_ : Surjection A B → Surjection C D →
                 Surjection (A ⊎ₛ C) (B ⊎ₛ D)
A↠B ⊎-surjection C↠D = record
  { to              = Sum.map (to A↠B) (to C↠D)
  ; cong            = Pointwise.map (cong A↠B) (cong C↠D)
  ; surjective      = [ Prod.map inj₁ inj₁ ∘ surjective A↠B ,
                        Prod.map inj₂ inj₂ ∘ surjective C↠D ]
  } where open Surjection

_⊎-left-inverse_ : LeftInverse A B → LeftInverse C D →
                   LeftInverse (A ⊎ₛ C) (B ⊎ₛ D)
A↩B ⊎-left-inverse C↩D = record
  { to              = Sum.map (to A↩B) (to C↩D)
  ; from            = Sum.map (from A↩B) (from C↩D)
  ; to-cong         = Pointwise.map (to-cong A↩B) (to-cong C↩D)
  ; from-cong       = Pointwise.map (from-cong A↩B) (from-cong C↩D)
  ; inverseˡ        = [ inj₁ ∘ inverseˡ A↩B , inj₂ ∘ inverseˡ C↩D ]
  } where open LeftInverse

_⊎-right-inverse_ : RightInverse A B → RightInverse C D →
                    RightInverse (A ⊎ₛ C) (B ⊎ₛ D)
A↪B ⊎-right-inverse C↪D = record
  { to              = Sum.map (to A↪B) (to C↪D)
  ; from            = Sum.map (from A↪B) (from C↪D)
  ; to-cong         = Pointwise.map (to-cong A↪B) (to-cong C↪D)
  ; from-cong       = Pointwise.map (from-cong A↪B) (from-cong C↪D)
  ; inverseʳ        = [ inj₁ ∘ inverseʳ A↪B , inj₂ ∘ inverseʳ C↪D ]
  } where open RightInverse
  
_⊎-inverse_ : Inverse A B → Inverse C D →
              Inverse (A ⊎ₛ C) (B ⊎ₛ D)
A↔B ⊎-inverse C↔D = record
  { to        = Sum.map (to A↔B) (to C↔D)
  ; from      = Sum.map (from A↔B) (from C↔D)
  ; to-cong   = Pointwise.map (to-cong A↔B) (to-cong C↔D)
  ; from-cong = Pointwise.map (from-cong A↔B) (from-cong C↔D)
  ; inverse   = [ inj₁ ∘ inverseˡ A↔B , inj₂ ∘ inverseˡ C↔D ] ,
                [ inj₁ ∘ inverseʳ A↔B , inj₂ ∘ inverseʳ C↔D ]
  } where open Inverse
