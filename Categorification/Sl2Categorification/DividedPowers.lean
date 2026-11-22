/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Sl2Categorification.WeakCategorification
import Categorification.Sl2Categorification.NilHeckeAction
import Categorification.KLR.NilHeckeFullSplitting
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Divided powers of `E` and their classes

Chuang–Rouquier, arXiv:math/0407205v2, §5.2.1: given a nilHecke action on `E`, the divided power
`E^{(n)} M` is the image of the idempotent `e_n = x^δ ∂_{w_0}` of `NH_n` acting on `E^n M`. Since
`1 ∈ NH_n` splits through `n!` copies of `e_n` (`NilHecke.exists_isSplitting_one_idemNH`),
`E^n M ≅ (E^{(n)} M)^{⊕ n!}`, so `[E^n M] = n! [E^{(n)} M]` in the Grothendieck group (the
class form of Chuang–Rouquier, Lemma 5.13 together with Theorem 5.6's decomposition).

## Main results

* `K0Data.cls_biproduct`: the class map is additive on finite biproducts.
* `K0Data.cls_eq_card_smul_of_isSplitting`: if `1 ∈ End Y` splits through copies of an
  endomorphism `e`, then `[Y]` is `card ι` times `[image e]`.
* `NilHeckeData.cls_Epow`: `[E^n M] = n! [E^{(n)} M]` (`NilHeckeData.divObj`).
-/

namespace Categorification.Sl2

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

attribute [local instance] Abelian.hasFiniteBiproducts

namespace K0Data

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V] (K : K0Data C ι V)

lemma cls_eq_zero_of_isZero {X : C} (hX : IsZero X) : K.cls X = 0 := by
  have h := K.cls_add_of_epi (𝟙 X)
  have h0 : K.cls (kernel (𝟙 X)) = 0 := by
    have := congrArg (· - K.cls X) h
    simpa using this.symm
  rw [K.cls_of_iso (hX.iso (isZero_kernel_of_mono (𝟙 X))), h0]

/-- The class map is additive on finite biproducts. -/
theorem cls_biproduct : ∀ (m : ℕ) {J : Type} [Fintype J] [DecidableEq J] (f : J → C),
    Fintype.card J = m → K.cls (⨁ f) = ∑ j, K.cls (f j)
  | 0, J, _, _, f, h => by
    have : IsEmpty J := Fintype.card_eq_zero_iff.mp h
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact K.cls_eq_zero_of_isZero
      ((IsZero.iff_id_eq_zero _).mpr (biproduct.hom_ext _ _ fun j => isEmptyElim j))
  | m + 1, J, _, _, f, h => by
    obtain ⟨i⟩ : Nonempty J := Fintype.card_pos_iff.mp (by omega)
    rw [K.cls_add_of_epi (biproduct.π f i), K.cls_of_iso (kernelBiproductπIso f i),
      cls_biproduct m _ (by rw [Fintype.card_subtype_compl, h, Fintype.card_unique]; rfl),
      Fintype.sum_eq_add_sum_subtype_ne _ i, add_comm]
    rfl

/-- If `1 ∈ End Y` splits through copies of `e` (`b_i a_j = δ_{ij} e`, `∑ a_j b_j = 1`), then
`Y ≅ (image e)^{⊕ ι}`, so `[Y] = card ι • [image e]`. -/
theorem cls_eq_card_smul_of_isSplitting {Y : C} {J : Type} [Fintype J] [DecidableEq J]
    {e : End Y} {a b : J → End Y} (h : Graded.IsSplitting 1 (fun _ => e) a b) :
    K.cls Y = Fintype.card J • K.cls (image e) := by
  have heb : ∀ j, e * b j = b j := fun j => by
    conv_rhs => rw [← mul_one (b j), ← h.sum_eq, Finset.mul_sum]
    simp_rw [← mul_assoc, h.mul_eq, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  have hfac : ∀ j, image.ι e ≫ factorThruImage e = 𝟙 _ := fun j => by
    have hba : b j * a j = e := by simpa using h.mul_eq j j
    have hee : e * e = e := by
      calc e * e = e * (b j * a j) := by rw [hba]
        _ = e := by rw [← mul_assoc, heb, hba]
    rw [← cancel_epi (factorThruImage e), ← cancel_mono (image.ι e)]
    simp only [Category.assoc, image.fac_assoc, image.fac, Category.comp_id]
    exact hee
  let B : Bicone (fun _ : J => image e) :=
    { pt := Y
      π := fun j => b j ≫ factorThruImage e
      ι := fun j => image.ι e ≫ a j
      ι_π := fun j j' => by
        split_ifs with hjj
        · subst hjj
          have hab : a j ≫ b j = e := by simpa using h.mul_eq j j
          rw [eqToHom_refl, Category.assoc, reassoc_of% hab,
            ← image.fac_assoc e (factorThruImage e), reassoc_of% (hfac j), hfac j]
        · have hab : a j ≫ b j' = 0 := by simpa [Ne.symm hjj] using h.mul_eq j' j
          rw [Category.assoc, reassoc_of% hab, zero_comp, comp_zero] }
  have total : ∑ j, B.π j ≫ B.ι j = 𝟙 B.pt := by
    have : ∀ j, B.π j ≫ B.ι j = a j * b j := fun j => by
      dsimp only [B]
      rw [Category.assoc, image.fac_assoc, ← Category.assoc]
      change (e * b j) ≫ a j = _
      rw [heb]
      rfl
    simp_rw [this]
    exact h.sum_eq
  rw [K.cls_of_iso (biproduct.uniqueUpToIso _ (isBilimitOfTotal B total)),
    K.cls_biproduct _ _ rfl, Finset.sum_const, Finset.card_univ]

end K0Data

namespace NilHeckeData

variable {E : C ⥤ C} [E.Additive] (D : NilHeckeData E)
variable (k : Type*) [CommRing k] [IsDomain k] [Linear k C]

/-- Evaluation of endomorphisms of a functor at an object, as a ring homomorphism. -/
@[simps]
def evalEnd (F : C ⥤ C) (M : C) : End F →+* End (F.obj M) where
  toFun a := a.app M
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := NatTrans.app_add _ _ _

/-- The divided power `E^{(n)} M`: the image of `e_n = x^δ ∂_{w_0} ∈ NH_n` acting on `E^n M`
(Chuang–Rouquier, §5.2.1). -/
noncomputable def divObj (n : ℕ) (M : C) : C :=
  image ((D.γ (k := k) n ⟨NilHecke.idemNH k n, NilHecke.idemNH_mem⟩).app M)

/-- **Chuang–Rouquier, Lemma 5.13** (class form): `[E^n M] = n! [E^{(n)} M]`. -/
theorem cls_Epow {ι V : Type*} [AddCommGroup V] [Module ℚ V] (K : K0Data C ι V) (n : ℕ)
    (M : C) : K.cls ((Epow E n).obj M) = n.factorial • K.cls (D.divObj k n M) := by
  obtain ⟨J, _, _, a, b, hc, hS⟩ := NilHecke.exists_isSplitting_one_idemNH k n
  have h := (hS.map (D.γ (k := k) n)).map (evalEnd (Epow E n) M)
  rw [map_one, map_one] at h
  rw [K.cls_eq_card_smul_of_isSplitting h, hc]
  rfl

end NilHeckeData

end Categorification.Sl2
