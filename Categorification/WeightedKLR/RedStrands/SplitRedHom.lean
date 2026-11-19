/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SplitRedBraid
import Categorification.KLR.BaseChange

/-!
# Splitting a red strand: the algebra map

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.3,
Proposition 4.21. The images of the idempotents, dots and crossings in the split corner
satisfy every defining relation of the Stendhal algebra of the merged weights
`λ'_c + λ'_{c+1}`, so they define an algebra map from that Stendhal algebra (all orders of
the red strands) into the corner of the Stendhal algebra of `λ'` cut out by the loadings in
which `λ'_c`, `λ'_{c+1}` are adjacent.
-/

noncomputable section

namespace Categorification.Stendhal.SplitRed

open KLR TypeA Equiv MvPolynomial

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} (c : Fin ℓ)
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ' : Fin (ℓ + 1) → I →₀ ℕ) {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "C" => SplitCorner c Q Λ' ν

noncomputable local instance : Algebra k C := KLR.cornerAlgebra _

variable (Q) in
/-- The images of the generators. -/
def genSplit : Gen μ → C
  | .idem s => gE c Λ' s
  | .dot a => polSplit c Λ' (X a)
  | .cross j => gΨ c Λ' j

variable (Q) in
/-- The free algebra on the generators maps to the corner. -/
def freeSplit : FreeAlgebra k (Gen μ) →ₐ[k] C :=
  FreeAlgebra.lift k (genSplit c Q Λ')

theorem freeSplit_rel ⦃u v : FreeAlgebra k (Gen μ)⦄
    (h : Stendhal.Rel k Q (mergeWeights c Λ') ν u v) :
    freeSplit c Q Λ' u = freeSplit c Q Λ' v := by
  have hfe : ∀ s, freeSplit c Q Λ' (fe k μ s) = gE c Λ' s :=
    fun s => FreeAlgebra.lift_ι_apply _ _
  have hfx : ∀ a, freeSplit c Q Λ' (fx k μ a) = polSplit c Λ' (X a) :=
    fun a => FreeAlgebra.lift_ι_apply _ _
  have hfψ : ∀ j, freeSplit c Q Λ' (fψ k μ j) = gΨ c Λ' j :=
    fun j => FreeAlgebra.lift_ι_apply _ _
  have hev {n : ℕ} (y : Fin n → FreeAlgebra k (Gen μ)) (p : MvPolynomial (Fin n) k) :
      freeSplit c Q Λ' (ncEval y p) = ncEval (fun a => freeSplit c Q Λ' (y a)) p := by
    have := map_ncEval (RingHom.id k) (freeSplit c Q Λ').toRingHom
      (fun r => (freeSplit c Q Λ').commutes r) y p
    rw [MvPolynomial.map_id] at this
    exact this
  cases h with
  | klr h =>
    cases h with
    | idem_mul s t =>
      rw [map_mul, hfe, hfe, gE_mul_gE]
      split_ifs <;> simp [hfe]
    | idem_sum => rw [map_sum, map_one]; simp only [hfe]; exact sum_gE c Λ'
    | dot_idem a s => rw [map_mul, map_mul, hfe, hfx, polSplit_mul_gE]
    | cross_idem j s => rw [map_mul, map_mul, hfe, hfe, hfψ, gΨ_mul_gE]
    | cross_zero j h =>
      rw [map_zero, hfψ]
      simp [gΨ, show ¬ j + 1 < m by omega]
    | dot_dot a b => rw [map_mul, map_mul, hfx, hfx, ← map_mul, ← map_mul, mul_comm]
    | cross_cross j l h => rw [map_mul, map_mul, hfψ, hfψ, gΨ_comm c Λ' j l h]
    | dot_cross a j h₁ h₂ => rw [map_mul, map_mul, hfx, hfψ, X_gΨ_comm c Λ' a j h₁ h₂]
    | dot_cross_left j h s =>
      rw [map_mul, map_sub, map_mul, map_mul, hfx, hfx, hfψ, hfe, dotCrossLeft c Λ' j h s]
      split_ifs <;> simp [hfe]
    | dot_cross_right j h s =>
      rw [map_mul, map_sub, map_mul, map_mul, hfx, hfx, hfψ, hfe, dotCrossRight c Λ' j h s]
      split_ifs <;> simp [hfe]
    | cross_sq j h s =>
      rw [map_mul, map_mul, hfψ, hfe, crossSq c Λ' j h s]
      split_ifs
      · simp
      · rw [map_mul, hfe, hev, ← ncEval_algHom_X]
        congr 2
        funext a; fin_cases a <;> simp [hfx]
    | braid j h s =>
      rw [map_mul, map_sub, map_mul, map_mul, map_mul, map_mul, hfψ, hfψ, hfe,
        braid c Λ' j h s]
      split_ifs
      · rw [map_mul, hfe, hev, ← ncEval_algHom_X]
        congr 2
        funext a; fin_cases a <;> simp [hfx]
      · simp
  | red_dot a s h =>
    rw [map_mul, hfx, hfe, map_zero]
    exact X_mul_gE_of_red c Λ' a s h
  | red_cross j h s h₁ h₂ =>
    rw [map_mul, hfψ, hfe, map_zero]
    exact redCross c Λ' j h s h₁ h₂

variable (Q ν) in
/-- Webster, arXiv:1309.3796v3, Proposition 4.21: splitting the red strand `λ_c` into adjacent
red strands `λ'_c`, `λ'_{c+1}` with `λ_c = λ'_c + λ'_{c+1}` is an algebra map from the Stendhal
algebra of `λ` to the corner of the Stendhal algebra of `λ'` cut out by the split loadings. -/
def splitHom : StendhalAlgebraAllOrders k Q (mergeWeights c Λ') ν →ₐ[k] C :=
  RingQuot.liftAlgHom k ⟨freeSplit c Q Λ', freeSplit_rel c Λ'⟩

theorem splitHom_mk (u : FreeAlgebra k (Gen μ)) :
    splitHom c Q Λ' ν (RingQuot.mkAlgHom k _ u) = freeSplit c Q Λ' u :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem splitHom_e (s : Seq μ) :
    splitHom c Q Λ' ν (StendhalAlgebraAllOrders.e s) = gE c Λ' s := by
  rw [StendhalAlgebraAllOrders.e, KLRAlgebra.e, StendhalAlgebraAllOrders.ofKLR_mk,
    splitHom_mk]
  exact FreeAlgebra.lift_ι_apply _ _

@[simp] theorem splitHom_x (a : Fin m) :
    splitHom c Q Λ' ν (StendhalAlgebraAllOrders.x a) = polSplit c Λ' (X a) := by
  rw [StendhalAlgebraAllOrders.x, KLRAlgebra.x, StendhalAlgebraAllOrders.ofKLR_mk,
    splitHom_mk]
  exact FreeAlgebra.lift_ι_apply _ _

@[simp] theorem splitHom_ψ (j : ℕ) :
    splitHom c Q Λ' ν (StendhalAlgebraAllOrders.ψ j) = gΨ c Λ' j := by
  rw [StendhalAlgebraAllOrders.ψ, KLRAlgebra.ψ, StendhalAlgebraAllOrders.ofKLR_mk,
    splitHom_mk]
  exact FreeAlgebra.lift_ι_apply _ _

end Categorification.Stendhal.SplitRed
