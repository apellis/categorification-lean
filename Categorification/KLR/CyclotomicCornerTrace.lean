/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicCommutatorBimodule

/-!
# The prescribed trace on the entire present-colour cyclotomic corner

For `β = {i} + γ`, construct an `RΛ(β)`-bimodule map on the actual corner
`e(β,i) RΛ(β+i) e(β,i)`, in every weight range. The definition uses the
actual signed crossing and dotted unit/counit maps in the cyclotomic
commutator, not an arbitrary vector-space splitting.

With KK weight `w`, for `w > 0` the trace is the last correction coordinate
of the positive inverse. For `w ≤ 0` it is dotted multiplication with `-w`
dots after the negative inverse applied to `(z,0)`. These are the cap
formulas of Brundan, arXiv:1501.00350v1, (1.15), (1.17), with Brundan weight
`-w`; the two signs in the second formula cancel. The inversions are the
ungraded bimodule maps of Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.2.

The domain, nonzero factorization, unit leading-coefficient, monicity and
Cartan-degree hypotheses are exactly those of the existing inversions.
The coefficient algebra is not assumed commutative or nontrivial.

The negative formula retains the connecting-kernel correction. In particular,
this is not the trace of a polynomial coordinate quotient identified with
the whole corner. The present-colour hypothesis makes beta nonzero but does
not cover absent colour. Relative nondegeneracy, a coevaluation, the two
opposite-adjunction triangles, grading and mixed-colour compatibility remain
separate obligations; none is assumed or asserted here.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.CornerTrace
open MulOpposite Polynomial
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
  (a : I → Polynomial k)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
local notation "R" => CycKLR k Q a β
local notation "M" => MiddleCyclotomic Q i γ a
local notation "L" => LowerCyclotomic Q i γ a
variable (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.RootDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))
local notation "pos" => cyclotomicCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg
local notation "neg" => cyclotomicNegativeCommutatorBimoduleEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg

/-- Last inverse component, defined on the entire actual corner. -/
def positive (hw : 0 < wt) : M →ₗ[R] R where
  toFun z := ((pos hw.le).symm z).2 ⟨(wt).toNat - 1, by omega⟩
  map_add' z t := by simp only [map_add, Prod.snd_add, Pi.add_apply]
  map_smul' r z := by simp only [map_smul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

local notation "trP" => positive Q i γ a hsym hQ ha RD Λ hΛ hdeg

/-- Right linearity is for the actual right multiplication action on the corner. -/
theorem positive_op_smul (hw : 0 < wt) (r : Rᵐᵒᵖ) (z : M) :
    trP hw (r • z) = r • trP hw z := by
  change ((pos hw.le).symm (r • z)).2 _ = _
  rw [cyclotomicCommutatorBimoduleEquiv_symm_op_smul]
  rfl

/-- The prescribed formula includes arbitrary lower tensors, not just polynomials. -/
theorem positive_on_commutator (hw : 0 < wt) (l : L) (v : Fin (wt).toNat → R) :
    trP hw (pos hw.le (l,v)) = v ⟨(wt).toNat - 1, by omega⟩ := by
  change ((pos hw.le).symm (pos hw.le (l,v))).2 _ = _
  rw [LinearEquiv.symm_apply_apply]

/-- All crossing terms have zero positive-weight trace. -/
theorem positive_crossing (hw : 0 < wt) (l : L) :
    trP hw (cyclotomicSigma Q i γ a l) = 0 := by
  have he : pos hw.le (l,0) = cyclotomicSigma Q i γ a l := by
    rw [cyclotomicCommutatorBimoduleEquiv_apply, cyclotomicCommutatorFinEquiv_apply]
    simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero, add_zero]
  rw [← he, positive_on_commutator]
  rfl

/-- The inverse component normalizes the last dot-unit and kills the other low dots. -/
theorem positive_dotUnit (hw : 0 < wt) (d : Fin (wt).toNat) (r : R) :
    trP hw (cyclotomicDotUnit Q i γ a (monomial d r)) =
      if d.val = (wt).toNat - 1 then r else 0 := by
  classical
  have he : pos hw.le (0, Pi.single d r) = cyclotomicDotUnit Q i γ a (monomial d r) := by
    rw [cyclotomicCommutatorBimoduleEquiv_apply, cyclotomicCommutatorFinEquiv_apply]
    rw [map_zero, zero_add, Finset.sum_eq_single d]
    · rw [Pi.single_eq_same]
    · intro e _ hed
      rw [Pi.single_eq_of_ne hed, map_zero, map_zero]
    · intro hd
      exact (hd (Finset.mem_univ d)).elim
  rw [← he, positive_on_commutator]
  simp only [Pi.single_apply]
  congr 1
  exact propext (by simp only [Fin.ext_iff]; omega)

/-- The positive trace is forced by its values on the actual source generators. -/
theorem positive_unique (hw : 0 < wt) (f : M →ₗ[R] R)
    (hf : ∀ l v, f (pos hw.le (l,v)) = v ⟨(wt).toNat - 1, by omega⟩) : f = trP hw := by
  ext z
  obtain ⟨⟨l,v⟩,rfl⟩ := (pos hw.le).surjective z
  rw [hf, positive_on_commutator]

/-- Ordinary dotted multiplication, with its proved coefficient linearity. -/
def dottedCounit (d : ℕ) : L →ₗ[R] R where
  toFun := cyclotomicDotCounit Q i γ a d
  map_add' := map_add _
  map_smul' r z := cyclotomicDotCounit_smul Q i γ a d r z

/-- The negative inverse with zero low dotted-counit coordinates. -/
def negativeLift (hw : wt ≤ 0) : M →ₗ[R] L :=
  (neg hw).symm.toLinearMap.comp (LinearMap.inl R M (Fin (-wt).toNat → R))

local notation "liftN" => negativeLift Q i γ a hsym hQ ha RD Λ hΛ hdeg

/-- Dotted multiplication after the prescribed inverse, including weight zero. -/
def nonpositive (hw : wt ≤ 0) : M →ₗ[R] R :=
  (dottedCounit Q i γ a (-wt).toNat).comp (liftN hw)

local notation "trN" => nonpositive Q i γ a hsym hQ ha RD Λ hΛ hdeg

theorem negativeLift_spec (hw : wt ≤ 0) (z : M) :
    cyclotomicSigma Q i γ a (liftN hw z) = z ∧
      ∀ d : Fin (-wt).toNat, cyclotomicDotCounit Q i γ a d (liftN hw z) = 0 := by
  have he := (neg hw).apply_symm_apply (z,0)
  exact ⟨congrArg Prod.fst he, fun d => congrArg (fun p => p.2 d) he⟩

theorem negativeLift_unique (hw : wt ≤ 0) (z : M) (l : L)
    (hs : cyclotomicSigma Q i γ a l = z)
    (hd : ∀ d : Fin (-wt).toNat, cyclotomicDotCounit Q i γ a d l = 0) :
    l = liftN hw z := by
  apply (neg hw).injective
  change neg hw l = neg hw ((neg hw).symm (z,0))
  rw [LinearEquiv.apply_symm_apply]
  exact Prod.ext hs (funext hd)

theorem nonpositive_op_smul (hw : wt ≤ 0) (r : Rᵐᵒᵖ) (z : M) :
    trN hw (r • z) = r • trN hw z := by
  change cyclotomicDotCounit Q i γ a (-wt).toNat ((neg hw).symm (r • z,0)) = _
  rw [show (r • z, (0 : Fin (-wt).toNat → R)) = r • (z,0) by
      change (r • z, 0) = (r • z, r • (0 : Fin (-wt).toNat → R))
      rw [smul_zero],
    cyclotomicNegativeCommutatorBimoduleEquiv_symm_op_smul, cyclotomicDotCounit_op_smul]
  rfl

/-- Evaluation on a normalized actual crossing lift. -/
theorem nonpositive_crossing_normalized (hw : wt ≤ 0) (l : L)
    (hd : ∀ d : Fin (-wt).toNat, cyclotomicDotCounit Q i γ a d l = 0) :
    trN hw (cyclotomicSigma Q i γ a l) = cyclotomicDotCounit Q i γ a (-wt).toNat l := by
  change cyclotomicDotCounit Q i γ a (-wt).toNat (liftN hw _) = _
  rw [← negativeLift_unique Q i γ a hsym hQ ha RD Λ hΛ hdeg hw _ l rfl hd]

/-- The correction is the actual connecting tensor, computed by the dotted kernel matrix. -/
theorem negativeLift_representative (hw : wt ≤ 0) (z : M) (l : L)
    (hs : cyclotomicSigma Q i γ a l = z) :
    liftN hw z = l + negativeConnecting Q i γ a hsym hQ ha RD Λ hΛ hdeg
      ((negativeCounitMatrixEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hw).symm
        (-(fun d : Fin (-wt).toNat => cyclotomicDotCounit Q i γ a d l))) := by
  change (cyclotomicNegativeCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hw).symm (z,0) = _
  rw [cyclotomicNegativeCommutator_inverse_representative Q i γ a hsym hQ ha RD Λ hΛ hdeg hw z 0 l hs,
    zero_sub]

/-- Formula on every crossing, retaining rather than discarding its lower-kernel term. -/
theorem nonpositive_crossing (hw : wt ≤ 0) (l : L) :
    trN hw (cyclotomicSigma Q i γ a l) =
      cyclotomicDotCounit Q i γ a (-wt).toNat l +
      cyclotomicDotCounit Q i γ a (-wt).toNat
        (negativeConnecting Q i γ a hsym hQ ha RD Λ hΛ hdeg
          ((negativeCounitMatrixEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hw).symm
            (-(fun d : Fin (-wt).toNat => cyclotomicDotCounit Q i γ a d l)))) := by
  change cyclotomicDotCounit Q i γ a (-wt).toNat (liftN hw _) = _
  rw [negativeLift_representative Q i γ a hsym hQ ha RD Λ hΛ hdeg hw _ l rfl, map_add]

/-- One prescribed bimodule trace on the entire actual present-colour corner. -/
def trace : M →ₗ[R] R :=
  if hw : 0 < wt then trP hw else trN (le_of_not_gt hw)

local notation "tr" => trace Q i γ a hsym hQ ha RD Λ hΛ hdeg

theorem trace_smul (r : R) (z : M) : tr (r • z) = r * tr z := map_smul tr r z

theorem trace_op_smul (r : R) (z : M) : tr (op r • z) = tr z * r := by
  unfold trace
  split
  · exact positive_op_smul Q i γ a hsym hQ ha RD Λ hΛ hdeg _ (op r) z
  · exact nonpositive_op_smul Q i γ a hsym hQ ha RD Λ hΛ hdeg _ (op r) z

/-- Both noncommutative coefficient orders are retained. -/
theorem trace_bimodule (r s : R) (z : M) :
    tr (r • (op s • z)) = r * tr z * s := by
  rw [trace_smul, trace_op_smul, mul_assoc]

end Categorification.KLR.KLRAlgebra.CornerTrace
