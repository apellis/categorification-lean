/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.BigOperators.Pi
import Categorification.TwoRep.PiLinear

/-!
# Finite biproducts in a product of additive categories

Finite biproducts are computed componentwise. This supplies the finite-biproduct
and zero-object instances for the cyclotomic weight spaces and their vacuum.
Unlike the small-diagram product-limit interface, the construction separates
the universes of the indexing set, the component categories and their morphisms.
-/

open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace Categorification.TwoRep
section Pi
variable {A : Type*} {C : A → Type*} [∀ a, Category (C a)] [∀ a, Preadditive (C a)]
  [∀ a, HasFiniteBiproducts (C a)]
variable {J : Type} [Fintype J] (F : J → ∀ a, C a)
def piBicone : Bicone F where
  pt a := ⨁ fun j => F j a
  π j a := biproduct.π (fun j => F j a) j
  ι j a := biproduct.ι (fun j => F j a) j
  ι_π j j' := by
    split_ifs with h
    · subst h
      funext a
      exact biproduct.ι_π_self (fun j => F j a) j
    · funext a
      exact biproduct.ι_π_ne (fun j => F j a) h

def piBiconeIsBilimit : (piBicone F).IsBilimit := by
  refine isBilimitOfTotal _ ?_
  funext a
  change (∑ j, (fun a => biproduct.π (fun j => F j a) j ≫
    biproduct.ι (fun j => F j a) j)) a = _
  rw [Finset.sum_apply]
  exact biproduct.total

instance : HasFiniteBiproducts (∀ a, C a) where
  out _ := ⟨fun F => HasBiproduct.mk ⟨piBicone F, piBiconeIsBilimit F⟩⟩
end Pi
end Categorification.TwoRep
