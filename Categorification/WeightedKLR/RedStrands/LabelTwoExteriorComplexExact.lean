/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleQuotientCoordinates
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorMiddleInjective
import Categorification.WeightedKLR.RedStrands.LabelTwoOutgoingRows
import Categorification.WeightedKLR.RedStrands.LabelTwoEndpointFlagDetection
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exactness of the label-two exterior crossing complex

Webster, arXiv:1309.3796v2, §8.2, printed page 80. The outgoing map is
injective at the middle loading. Its kernel at the terminal loading
is spanned by the two images of the incoming divided standard.
-/

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra Categorification.Webster.LabelTwo

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]
local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "rawν" => Multiset.replicate 2 ()
local notation "rawW" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "μ" => stendhalWeight 2 ν
local notation "H" => KLRAlgebra k (stendhalQ (parameter k) weights) μ
local notation "rawH" => KLRAlgebra k (stendhalQ (parameter k) rawW) (stendhalWeight 2 rawν)
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "T" => TensorProductAlgebra k (parameter k) rawW rawν
local notation "S" => Standard k
local notation "U" => LinearMap.range (diagramPlus k)
local notation "V" => StandardDotSumQuotient k
local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "E" => exteriorMiddleQuotientEquiv k
local notation "π" => tensorOfKLR (parameter k) weights ν
local notation "rawπ" => tensorOfKLR (parameter k) rawW rawν
local notation "d" => labelTwoMiddleExteriorDifferential (parameter k)
local notation "X" => (x (⟨1, by decide⟩ : Fin (Multiset.card μ)) : H)

private def leftCut : Seq μ := labelTwoExteriorLeftLoading

private def projector : A := labelTwoLeftExteriorProjector (parameter k)
local notation "P" => lIdeal (projector k)

private def qword : H := e leftCut - X * (ψ 1 : H) * e leftCut
private def mixed : H := (ψ 2 : H) * e leftCut
private def slide : H := (ψ 1 : H) * mixed k

private theorem projected_word_mul (a b : H) : π (a * b) = π a * π b := by
  simp only [tensorOfKLR,map_mul]

/-- The outgoing crossing written in the common middle quotient. -/
def normalizedOutgoing : V →ₗ[A] P where
  toFun v := d ((E).symm v)
  map_add' u v := (congrArg d ((E).symm.map_add u v)).trans ((d).map_add _ _)
  map_smul' a v := (congrArg d ((E).symm.map_smul a v)).trans ((d).map_smul (a : T) _)

private theorem normalizedOutgoing_gen :
    ((normalizedOutgoing k) ((U).mkQ g)).val = π (mixed k * qword k) := by
  have he := exteriorMiddleQuotientEquiv_mk_unit k
  have hi := (E).symm_apply_eq.mpr he.symm
  change (d ((E).symm ((U).mkQ g))).val = _
  rw [hi]
  have h := labelTwo_outgoing_applyRaw (parameter k) (1 : rawH)
  simp only [tensorOfKLR, map_one, one_smul, one_mul] at h
  exact h

private theorem normalizedOutgoing_acted (a : H) :
    ((normalizedOutgoing k) ((U).mkQ (π a • g))).val =
      π (a * mixed k * qword k) := by
  rw [(U).mkQ.map_smul, (normalizedOutgoing k).map_smul]
  change π a * ((normalizedOutgoing k) ((U).mkQ g)).val = _
  rw [normalizedOutgoing_gen]
  simp only [projected_word_mul, mul_assoc]

private theorem loading_fixes_gen : π (e loading) • g = g := by
  have he : π (e loading) = seqIdem (parameter k) weights loading loading_ordered := by
    apply congrArg (TensorProductAlgebra.mk (parameter k) weights ν)
    apply Subtype.ext
    exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem loading).trans (ite_eq_left loading_ordered)
  have h : seqIdem (parameter k) weights loading loading_ordered •
      (middleToFixed k (1 : Middle k)).val = (middleToFixed k (1 : Middle k)).val :=
    (middleToFixed k (1 : Middle k)).property
  rw [middleToFixed_one_val k] at h
  exact (congrArg (fun z : A => z • g) he).trans h

private theorem normalizedOutgoing_acted_cut (a : H) :
    ((normalizedOutgoing k) ((U).mkQ (π a • g))).val =
      π ((a * e loading) * mixed k * qword k) := by
  have h : π (a * e loading) • g = π a • g := by
    rw [projected_word_mul, mul_smul, loading_fixes_gen]
  exact (congrArg (fun v : S => ((normalizedOutgoing k) ((U).mkQ v)).val) h).symm.trans
    (normalizedOutgoing_acted k (a * e loading))

private def oldMid : Seq μ := labelTwoMiddleLoading
private theorem oldMid_eq_loading : oldMid = loading := exterior_middle_loading_alignment

private def terminalColumn : A := π (slide k * qword k)
private def terminalDotColumn : A := π (slide k * (X * qword k))
private def middleColumn : A := π (mixed k * qword k)
private def middleDotColumn : A := π (mixed k * (X * qword k))

private theorem terminalVector_one_zero :
    (terminalVector k 1 0).val = (U).mkQ (π (ψ 1 : H) • g) := by
  rw [terminalVector_val, middleToFixed_one_val, (middleToFixed k).map_zero]
  simp only [Submodule.coe_zero, smul_zero, add_zero, ψw_cons, ψw_nil, mul_one]

private theorem terminalVector_dot_zero :
    (terminalVector k y₁ 0).val = (U).mkQ (π ((ψ 1 : H) * X) • g) := by
  rw [terminalVector_val, middleToFixed_y₁_val, (middleToFixed k).map_zero]
  simp only [Submodule.coe_zero, smul_zero, add_zero, ψw_cons, ψw_nil, mul_one,
    leftMiddleDot, projected_word_mul, mul_smul]

private theorem terminalVector_zero_one :
    (terminalVector k 0 1).val = (U).mkQ (π ((ψ 2 : H) * (ψ 1 : H)) • g) := by
  rw [terminalVector_val, (middleToFixed k).map_zero, middleToFixed_one_val]
  simp only [Submodule.coe_zero, smul_zero, zero_add, ψw_cons, ψw_nil, mul_one]

private theorem terminalVector_zero_dot :
    (terminalVector k 0 y₁).val = (U).mkQ (π ((ψ 2 : H) * ((ψ 1 : H) * X)) • g) := by
  rw [terminalVector_val, (middleToFixed k).map_zero, middleToFixed_y₁_val]
  simp only [Submodule.coe_zero, smul_zero, zero_add, ψw_cons, ψw_nil, mul_one,
    leftMiddleDot, projected_word_mul, mul_smul]

local notation "out" => normalizedOutgoing k

private theorem normalizedOutgoing_terminal_one :
    (out (terminalVector k 1 0).val).val = terminalColumn k := by
  rw [terminalVector_one_zero]
  exact (normalizedOutgoing_acted k (ψ 1 : H))

private theorem normalizedOutgoing_terminal_dot :
    (out (terminalVector k y₁ 0).val).val = terminalDotColumn k := by
  rw [terminalVector_dot_zero, normalizedOutgoing_acted_cut, ← oldMid_eq_loading]
  have h : (((ψ 1 : H) * (X * e oldMid)) * mixed k * qword k) =
      slide k * (X * qword k) := (labelTwo_outgoing_terminal_affine_rows
        (stendhalQ (parameter k) weights)).2.2.1
  apply congrArg (π)
  simpa only [mul_assoc] using h

private theorem normalizedOutgoing_terminal_translate :
    (out (terminalVector k 0 1).val).val = 0 := by
  rw [terminalVector_zero_one, normalizedOutgoing_acted_cut, ← oldMid_eq_loading]
  have h : ((ψ 2 : H) * (((ψ 1 : H) * e oldMid) * mixed k * qword k)) = 0 :=
    (labelTwo_outgoing_terminal_affine_rows (stendhalQ (parameter k) weights)).2.1
  have hh : ((((ψ 2 : H) * (ψ 1 : H)) * e oldMid) * mixed k * qword k) = 0 := by
    simpa only [mul_assoc] using h
  rw [hh]
  simp only [tensorOfKLR, map_zero]

private theorem normalizedOutgoing_terminal_translate_dot :
    (out (terminalVector k 0 y₁).val).val = terminalColumn k := by
  rw [terminalVector_zero_dot, normalizedOutgoing_acted_cut, ← oldMid_eq_loading]
  have h : ((ψ 2 : H) * (((ψ 1 : H) * (X * e oldMid)) * mixed k * qword k)) =
      slide k * qword k := (labelTwo_outgoing_terminal_affine_rows
        (stendhalQ (parameter k) weights)).2.2.2
  apply congrArg (π)
  simpa only [mul_assoc] using h

private theorem normalizedOutgoing_middle_one :
    (out ((U).mkQ g)).val = middleColumn k := normalizedOutgoing_gen k

private theorem normalizedOutgoing_middle_dot :
    (out ((U).mkQ (leftMiddleDot k • g))).val = middleDotColumn k := by
  change (out ((U).mkQ (π X • g))).val = _
  rw [normalizedOutgoing_acted]
  have h : (X * mixed k * qword k : H) = mixed k * (X * qword k) := by
    unfold mixed
    rw [← mul_assoc X, x_mul_ψ _ _ (by decide) (by decide)]
    have hdot : (X * e leftCut : H) = e leftCut * X := x_mul_e _ _
    calc
      _ = (ψ 2 : H) * (X * e leftCut) * qword k := by simp only [mul_assoc]
      _ = _ := by rw [hdot]; simp only [mul_assoc]
  exact congrArg (π) h

private def outgoingValue : V →ₗ[k] A :=
  ((lIdeal (projector k)).subtype.restrictScalars k).comp ((out).restrictScalars k)

private theorem project_coefficient_row (a b : k) (p q : H) :
    π (a • p + b • q) = a • π p + b • π q := by
  simp only [tensorOfKLR, map_add, map_smul]

private theorem independent_middle_columns (a b : k)
    (h : a • middleColumn k + b • middleDotColumn k = 0) :
    a = 0 ∧ b = 0 := by
  have hr : π (a • (mixed k * qword k) + b • (mixed k * (X * qword k))) = 0 :=
    (project_coefficient_row k a b _ _).trans h
  exact LabelTwoEndpointFlag.outgoing_middle_coefficients_eq_zero (parameter k) hr

private theorem independent_terminal_columns (a b : k)
    (h : a • terminalColumn k + b • terminalDotColumn k = 0) :
    a = 0 ∧ b = 0 := by
  have hr : π (a • (slide k * qword k) + b • (slide k * (X * qword k))) = 0 :=
    (project_coefficient_row k a b _ _).trans h
  exact LabelTwoEndpointFlag.outgoing_terminal_coefficients_eq_zero (parameter k) hr

local notation "Eb" => seqIdem (parameter k) weights loading loading_ordered
local notation "Ea" => seqIdem (parameter k) weights terminalLoading terminalLoading_ordered
local notation "Vb" => fixSub k V Eb
local notation "Va" => fixSub k V Ea

private theorem map_two_coefficients
    {L N : Type*} [AddCommGroup L] [Module k L] [AddCommGroup N] [Module k N]
    (f : L →ₗ[k] N) (a b : k) (x y : L) :
    f (a • x + b • y) = a • f x + b • f y :=
  (f.map_add _ _).trans (congrArg₂ (· + ·) (f.map_smul a x) (f.map_smul b y))

set_option maxHeartbeats 550000 in
private theorem outgoing_injective_middle_cut (z : Vb) (hz : out z.val = 0) : z.val = 0 := by
  obtain ⟨a,b,hs⟩ := middle_cut_basis_span k z
  let f := outgoingValue k
  have h₀ : f ((U).mkQ g) = middleColumn k := normalizedOutgoing_middle_one k
  have h₁ : f ((U).mkQ (leftMiddleDot k • g)) = middleDotColumn k := normalizedOutgoing_middle_dot k
  have hz' : f z.val = 0 := by
    change (out z.val).val = 0
    exact congrArg Subtype.val hz
  have hrow := (map_two_coefficients k f a b ((U).mkQ g) ((U).mkQ (leftMiddleDot k • g))).trans
    (congrArg₂ (· + ·) (congrArg (a • ·) h₀) (congrArg (b • ·) h₁))
  have hr : a • middleColumn k + b • middleDotColumn k = 0 :=
    hrow.symm.trans ((congrArg f hs).symm.trans hz')
  obtain ⟨ha,hb⟩ := independent_middle_columns k a b hr
  simpa only [ha, hb, zero_smul, add_zero] using hs

local notation "Source" => labelTwoRightExteriorDividedStandard (parameter k)
local notation "e₁" => labelTwoExteriorMiddleDifferential (parameter k)
local notation "fullIncoming" => labelTwoExteriorToMiddle (parameter k)
local notation "RA" => labelTwoExteriorRightLoading
local notation "rawX₂" => (x (⟨2, by decide⟩ : Fin (Multiset.card (stendhalWeight 2 rawν))) : rawH)

private theorem orderedRA : IsRedOrdered RA := by
  unfold IsRedOrdered
  decide +kernel

local notation "gA" => leftStandardUnit (parameter k) rawW RA orderedRA

private def incomingUnit : Source :=
  (labelTwoRightExteriorProjection (parameter k)).rangeRestrict gA

private def incomingTranslate : Source :=
  rawπ (ψ 2 : rawH) • incomingUnit k

private theorem incomingUnit_val :
    (incomingUnit k).val = rawπ (rawX₂ * (ψ 2 : rawH) * e RA) • gA :=
  labelTwoRightExteriorProjection_generator (parameter k)

private def normalizedIncoming : Source →ₗ[k] V :=
  ((E).toLinearMap.restrictScalars k).comp ((e₁).restrictScalars k)

private theorem normalizedIncoming_unit :
    normalizedIncoming k (incomingUnit k) = (terminalVector k 1 y₂).val := by
  change E (fullIncoming (incomingUnit k).val) = _
  rw [incomingUnit_val]
  exact exteriorMiddleQuotientEquiv_projected_generator k

private theorem normalizedIncoming_translate :
    normalizedIncoming k (incomingTranslate k) = (terminalVector k 0 1).val := by
  change E (fullIncoming (rawπ (ψ 2 : rawH) • (incomingUnit k).val)) = _
  rw [incomingUnit_val]
  have hz : (0 : fixSub k S Eb) = middleToFixed k 0 := (middleToFixed k).map_zero.symm
  have hpair : ((0 : fixSub k S Eb), middleToFixed k (1 : Middle k)) =
      (middleToFixed k 0, middleToFixed k (1 : Middle k)) := Prod.ext hz rfl
  exact (exteriorMiddleQuotientEquiv_projected_translate k).trans
    (congrArg (fun w : fixSub k S Eb × fixSub k S Eb =>
      (U).mkQ ((terminalToTwoMiddle k).symm w).val) hpair)

private theorem incoming_terminal_vector_sub :
    (terminalVector k 1 y₂).val = (terminalVector k 1 0).val - (terminalVector k 0 y₁).val := by
  let c := terminalCutDotSumEquiv k
  have h₀ : c (terminalVector k 1 0) = (1,0) := by
    simpa only [map_one, map_zero] using terminalVector_coordinates k 1 0
  have h₁ : c (terminalVector k 0 y₁) = (0,DualNumber.eps) := by
    simpa only [map_zero, specialize_y₁] using terminalVector_coordinates k 0 y₁
  have h₂ : c (terminalVector k 1 y₂) = (1,-DualNumber.eps) := by
    simpa only [map_one, specialize_y₂] using terminalVector_coordinates k 1 y₂
  have h : terminalVector k 1 y₂ = terminalVector k 1 0 - terminalVector k 0 y₁ := c.injective (by
    calc
      _ = ((1,-DualNumber.eps) : DualNumber k × DualNumber k) := h₂
      _ = ((1,0) : DualNumber k × DualNumber k) - (0,DualNumber.eps) := by
        apply Prod.ext <;> simp
      _ = _ := (congrArg₂ (· - ·) h₀.symm h₁.symm).trans (c.map_sub _ _).symm)
  exact congrArg Subtype.val h

private def terminalUnitBasis : V := (terminalVector k 1 0).val
private def terminalDotBasis : V := (terminalVector k y₁ 0).val
private def terminalTranslateBasis : V := (terminalVector k 0 1).val
private def terminalTranslateDotBasis : V := (terminalVector k 0 y₁).val

local notation "r₀" => terminalUnitBasis k
local notation "r₁" => terminalDotBasis k
local notation "r₂" => terminalTranslateBasis k
local notation "r₃" => terminalTranslateDotBasis k

private theorem map_four_coefficients {L N : Type*}
    [AddCommGroup L] [Module k L] [AddCommGroup N] [Module k N]
    (f : L →ₗ[k] N) (a b c c' : k) (u v w z : L) :
    f (a • u + b • v + c • w + c' • z) =
      a • f u + b • f v + c • f w + c' • f z := by
  rw [f.map_add, f.map_add, map_two_coefficients,
    f.map_smul c w, f.map_smul c' z]

set_option maxHeartbeats 650000 in
private theorem outgoing_terminal_linear_combination (a₀ a₁ b₀ b₁ : k) :
    outgoingValue k (a₀ • r₀ + a₁ • r₁ + b₀ • r₂ + b₁ • r₃) =
      (a₀ + b₁) • terminalColumn k + a₁ • terminalDotColumn k := by
  let f := outgoingValue k
  have h₀ : f r₀ = terminalColumn k := normalizedOutgoing_terminal_one k
  have h₁ : f r₁ = terminalDotColumn k := normalizedOutgoing_terminal_dot k
  have h₂ : f r₂ = 0 := normalizedOutgoing_terminal_translate k
  have h₃ : f r₃ = terminalColumn k := normalizedOutgoing_terminal_translate_dot k
  calc
    _ = a₀ • f r₀ + a₁ • f r₁ + b₀ • f r₂ + b₁ • f r₃ :=
      map_four_coefficients k f a₀ a₁ b₀ b₁ r₀ r₁ r₂ r₃
    _ = a₀ • terminalColumn k + a₁ • terminalDotColumn k + b₁ • terminalColumn k := by
      rw [h₀, h₁, h₂, h₃, smul_zero, add_zero]
    _ = (a₀ • terminalColumn k + b₁ • terminalColumn k) + a₁ • terminalDotColumn k :=
      add_right_comm _ _ _
    _ = _ := congrArg (· + a₁ • terminalDotColumn k) (add_smul a₀ b₁ (terminalColumn k)).symm

private theorem incoming_terminal_linear_combination (a b : k) :
    normalizedIncoming k (a • incomingUnit k + b • incomingTranslate k) =
      a • r₀ + b • r₂ - a • r₃ := by
  let f := normalizedIncoming k
  calc
    _ = a • f (incomingUnit k) + b • f (incomingTranslate k) :=
      map_two_coefficients k f _ _ _ _
    _ = a • (r₀ - r₃) + b • r₂ :=
      congrArg₂ (· + ·)
        (congrArg (a • ·) ((normalizedIncoming_unit k).trans (incoming_terminal_vector_sub k)))
        (congrArg (b • ·) (normalizedIncoming_translate k))
    _ = a • r₀ - a • r₃ + b • r₂ :=
      congrArg (· + b • r₂) (smul_sub a r₀ r₃)
    _ = _ := sub_add_eq_add_sub _ _ _

private theorem reduce_terminal_coefficients {L : Type*}
    [AddCommGroup L] [Module k L] (a a' b b' : k) (u v w z : L)
    (ha : a' = 0) (hb : b' = -a) :
    a • u + a' • v + b • w + b' • z = a • u + b • w - a • z := by
  rw [ha, hb, zero_smul, add_zero, neg_smul, sub_eq_add_neg]

set_option maxHeartbeats 650000 in
private theorem outgoing_kernel_terminal_cut (z : Va) (hz : out z.val = 0) :
    ∃ x : Source, normalizedIncoming k x = z.val := by
  obtain ⟨a₀,a₁,b₀,b₁,h⟩ := terminal_cut_basis_span k z
  have hs : z.val = a₀ • r₀ + a₁ • r₁ + b₀ • r₂ + b₁ • r₃ := congrArg Subtype.val h
  have hz' : outgoingValue k z.val = 0 := by
    change (out z.val).val = 0
    exact congrArg Subtype.val hz
  have hrel : (a₀ + b₁) • terminalColumn k + a₁ • terminalDotColumn k = 0 :=
    (outgoing_terminal_linear_combination k a₀ a₁ b₀ b₁).symm.trans
      ((congrArg (outgoingValue k) hs).symm.trans hz')
  obtain ⟨hc,ha⟩ := independent_terminal_columns k _ _ hrel
  have hb : b₁ = -a₀ := eq_neg_iff_add_eq_zero.mpr ((add_comm b₁ a₀).trans hc)
  have hs' := hs.trans (reduce_terminal_coefficients k a₀ a₁ b₀ b₁ r₀ r₁ r₂ r₃ ha hb)
  exact ⟨a₀ • incomingUnit k + b₀ • incomingTranslate k,
    (incoming_terminal_linear_combination k a₀ b₀).trans hs'.symm⟩

/-- The two actual adjacent crossing maps at label two are exact at the
middle dot-sum quotient. -/
theorem labelTwoExteriorMiddle_exact :
    Function.Exact (e₁) (d) := by
  intro z
  constructor
  · intro hz
    let v := E z
    have hout : out v = 0 := by
      change d ((E).symm (E z)) = 0
      exact (congrArg d ((E).symm_apply_apply z)).trans hz
    let y : Vb := ⟨Eb • v, smul_mem_fixSub (seqIdem_mul_self (parameter k) weights loading loading_ordered) v⟩
    let w : Va := ⟨Ea • v, smul_mem_fixSub (seqIdem_mul_self (parameter k) weights terminalLoading terminalLoading_ordered) v⟩
    have hy : out y.val = 0 := by
      change out (Eb • v) = 0
      rw [(out).map_smul, hout, smul_zero]
    have hw : out w.val = 0 := by
      change out (Ea • v) = 0
      rw [(out).map_smul, hout, smul_zero]
    have hmid : Eb • v = 0 := outgoing_injective_middle_cut k y hy
    obtain ⟨u,hu⟩ := outgoing_kernel_terminal_cut k w hw
    refine ⟨u, (E).injective ?_⟩
    change normalizedIncoming k u = v
    rw [hu]
    change Ea • v = v
    simpa only [hmid, zero_add] using labelTwo_middleQuotient_split k v
  · rintro ⟨u,rfl⟩
    exact DFunLike.congr_fun (labelTwoExteriorMiddleDifferential_comp_zero (parameter k)) u

/-- The actual three-term label-two short complex is exact at its middle term. -/
theorem labelTwoExteriorStandardComplex_exact :
    (labelTwoExteriorStandardComplex (parameter k)).Exact :=
  (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    (labelTwoExteriorMiddle_exact k)

end
end Categorification.Stendhal.LabelTwo
