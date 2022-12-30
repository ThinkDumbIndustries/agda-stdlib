------------------------------------------------------------------------
-- The Agda standard library
--
-- Sum combinators for propositional equality preserving functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Function.Propositional where

open import Data.Sum.Base
open import Data.Sum.Function.Setoid
open import Data.Sum.Relation.Binary.Pointwise using (Pointwise-≡↔≡)
open import Function.Construct.Composition as Compose
open import Function.Related
open import Function
open import Function.Properties.Inverse as Inv
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (setoid)

private
  variable
    a b c d : Level
    A B C D : Set a

------------------------------------------------------------------------
-- Combinators for various function types

_⊎-⇔_ : A ⇔ B → C ⇔ D → (A ⊎ C) ⇔ (B ⊎ D)
A⇔B ⊎-⇔ C⇔D =
  (Inverse⇒Equivalence (Inv.sym (Pointwise-≡↔≡ _ _)) ⟨∘⟩
  (A⇔B ⊎-equivalence C⇔D))                           ⟨∘⟩
  Inverse⇒Equivalence (Pointwise-≡↔≡ _ _)
  where open Compose using () renaming (equivalence to _⟨∘⟩_)

_⊎-↣_ : A ↣ B → C ↣ D → (A ⊎ C) ↣ (B ⊎ D)
_⊎-↣_ A↣B C↣D =
  (Inverse⇒Injection (Inv.sym (Pointwise-≡↔≡ _ _)) ⟨∘⟩
  (A↣B ⊎-injection C↣D)) ⟨∘⟩
  Inverse⇒Injection (Pointwise-≡↔≡ _ _)
  where open Compose using () renaming (injection to _⟨∘⟩_)

_⊎-↩_ : A ↩ B → C ↩ D → (A ⊎ C) ↩ (B ⊎ D)
_⊎-↩_ A↩B C↩D =
  (Inverse.leftInverse (Inv.sym (Pointwise-≡↔≡ _ _)) ⟨∘⟩
  (A↩B ⊎-left-inverse C↩D)) ⟨∘⟩
  Inverse.leftInverse (Pointwise-≡↔≡ _ _)
  where open Compose using () renaming (leftInverse to _⟨∘⟩_)

_⊎-↠_ : A ↠ B → C ↠ D → (A ⊎ C) ↠ (B ⊎ D)
A↠B ⊎-↠ C↠D =
  (Inverse⇒Surjection (Inv.sym (Pointwise-≡↔≡ _ _)) ⟨∘⟩
  (A↠B ⊎-surjection C↠D)) ⟨∘⟩
  Inverse⇒Surjection (Pointwise-≡↔≡ _ _)
  where open Compose using () renaming (surjection to _⟨∘⟩_)

_⊎-↔_ : A ↔ B → C ↔ D → (A ⊎ C) ↔ (B ⊎ D)
A↔B ⊎-↔ C↔D =
  (Inv.sym (Pointwise-≡↔≡ _ _) ⟨∘⟩
  (A↔B ⊎-inverse C↔D)) ⟨∘⟩
  Pointwise-≡↔≡ _ _
  where open Compose using () renaming (inverse to _⟨∘⟩_)

_⊎-cong_ : ∀ {k} → A ∼[ k ]′ B → C ∼[ k ]′ D → (A ⊎ C) ∼[ k ]′ (B ⊎ D)
_⊎-cong_ {k = implication}         = map
_⊎-cong_ {k = reverse-implication} = λ f g → lam (map (app-← f) (app-← g))
_⊎-cong_ {k = equivalence}         = _⊎-⇔_
_⊎-cong_ {k = injection}           = _⊎-↣_
_⊎-cong_ {k = reverse-injection}   = λ f g → lam (app-↢′ f ⊎-↣ app-↢′ g)
_⊎-cong_ {k = left-inverse}        = _⊎-↩_
_⊎-cong_ {k = surjection}          = _⊎-↠_
_⊎-cong_ {k = bijection}           = _⊎-↔_
