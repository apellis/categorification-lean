/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.Frobenius
import Categorification.KLR.CyclotomicAction.PresCL
import Categorification.TwoRep.CyclicTraceWord

/-!
# The Frobenius trace of a cyclotomic KLR algebra is symmetric

Webster, arXiv:1309.3796v3, Theorem 3.18 and Remark 3.19. The trace `cycTrace` of Theorem 3.18
closes a diagram on the right with the biadjunction of `E_i` and `F_i`. Webster observes that
it is not symmetric in general, because moving a crossing of strands labelled `i ≠ j` around
the closure multiplies it by `t_ji / t_ij`, and Remark 3.19 rescales the trace on each
`e(i) R^Λ e(i)` by a product of such ratios to make it symmetric. When `t_ij = t_ji` for all
`i ≠ j`, every rescaling factor is `1`, and the trace itself is symmetric:
`tr (x y) = tr (y x)` (`cycTrace_mul_comm`). This covers the scalars of Khovanov–Lauda III,
`t_ij = 1` (`cyclotomic_frobenius_symmetric_kl`).

Here `t_ij` is the coefficient of `u^{d_ij}` in `Q_ij(u, v)` (`KLR.extremalCoeff`), the scalar
of the Cautis–Lauda presentation acting on the cyclotomic quotients (`cyclotomicScalars`).

The proof: the dots and same-colour crossings are cyclic for the right adjunctions
`E_i ⊣ F_i` and Brundan's left adjunctions `F_i ⊣ E_i` (Brundan, arXiv:1501.00350v1,
Theorem 5.3), the distinct-colour crossings are cyclic up to `t_ij / t_ji`
(`TwoRep.RouqFamily.mixed_cross_doubleMate`), so every entry of the action of `R(ν)` on the
words `E_t` is cyclic (`TwoRep.RouqFamily.klrAct_isCyclic`), and the closing trace is
symmetric on cyclic 2-morphisms (`TwoRep.closeTrace_comp_comm`).

## Main results

* `cycTrace_mul_comm`: symmetry of the trace of Theorem 3.18 when `t_ij = t_ji`;
* `KLR.IsRouquierQ.cyclotomic_frobenius_symmetric`: in Webster's setting, `R^Λ(ν)` is a
  symmetric Frobenius algebra when `t_ij = t_ji`;
* `cyclotomic_frobenius_symmetric_kl`: the same for the scalars `t_ij = 1`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Bicategory TwoRep KLRAlgebra QuantumGroup

universe u v w u₁

noncomputable section

variable {I : Type u} [DecidableEq I] {k : Type v} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y} {Λ : X}
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
  (hsupp : ∀ i j, i ≠ j → ∀ p q : ℕ, -2 * C.dot i j < C.dot i i * p + C.dot j j * q →
    (Q i j).coeff (Finsupp.single 0 p + Finsupp.single 1 q) = 0)
  (hsym : ∀ i j, i ≠ j → extremalCoeff C Q i j = extremalCoeff C Q j i)

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg

set_option quotPrecheck false in
set_option hygiene false in
local notation "𝕍" => emptyBlockObj.{u, v, w} Q a RD Λ

local notation "μ₀" => blockWeight RD Λ 0

include hsupp hsym in
/-- **All crossings of the cyclotomic Rouquier family are cyclic** when `t_ij = t_ji` for
`i ≠ j`. -/
theorem cyclotomicFamily_crossCyclic : (S).CrossCyclic :=
  (S).crossCyclic_of_scalars (cyclotomicScalars hQ hlead RD hdeg)
    (cyclotomicFamily_brundanUpKLR hQ hlead ha RD Λ hΛ hdeg hsupp)
    (cyclotomicFamily_mixedInversion RD Λ hQ hlead ha hΛ hdeg) fun i j hij => by
      simp only [kkScalars, hij, Ne.symm hij, ↓reduceDIte, IsUnit.unit_spec]
      exact hsym i j hij

variable {ν : Multiset I}

/-- Closing a 2-morphism at the vacuum is evaluating its bicategorical closing trace. -/
theorem wordTrace_hom_app (t : Seq ν)
    (f : RouqData.wordCell (S).toRouqData μ₀ t ⟶ RouqData.wordCell (S).toRouqData μ₀ t) :
    wordTrace.{u, v, w} hQ hlead ha hΛ hdeg t (f.hom.app (familyObj hQ hlead ha hΛ hdeg (𝕍))) =
      (TwoRep.closeTrace (RouqFamily.wadj (S) μ₀ (wordL RD μ₀ t) _ (wValid_wordL μ₀ t))
        (RouqFamily.wadjL (S) μ₀ (wordL RD μ₀ t) _ (wValid_wordL μ₀ t)) f).hom.app
          (familyObj hQ hlead ha hΛ hdeg (𝕍)) := by
  simp only [wordTrace, AmbidextrousTrace.closeTraceIso, AmbidextrousTrace.closeTrace,
    TwoRep.closeTrace, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id]
  rfl

/-- The trace of the action at the vacuum is the evaluation of the bicategorical trace. -/
theorem trace_vacAct (r : KLRAlgebra k Q ν) :
    Diagram.MatEnd.trace (fun t : Seq ν => wordTrace.{u, v, w} hQ hlead ha hΛ hdeg t)
        (vacAct.{u, v, w} hQ hlead ha hΛ hdeg r) =
      ((S).wordTrace₂ μ₀
        (RouqFamily.klrAct (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg) μ₀ r)).hom.app
          (familyObj hQ hlead ha hΛ hdeg (𝕍)) := by
  change ∑ t, wordTrace.{u, v, w} hQ hlead ha hΛ hdeg t (vacAct.{u, v, w} hQ hlead ha hΛ hdeg r t t)
    = _
  unfold RouqFamily.wordTrace₂
  exact (Finset.sum_congr rfl fun t _ => wordTrace_hom_app hQ hlead ha hΛ hdeg t _).trans
    (LinearCat.LinFun.sum_hom_app _ _ _).symm

include hQ hlead ha hΛ hdeg hsupp hsym in
/-- **The trace of Theorem 3.18 is symmetric** when `t_ij = t_ji` for all `i ≠ j` (Webster,
arXiv:1309.3796v3, Remark 3.19, where all rescaling factors are then `1`). -/
theorem cycTrace_mul_comm (x y : CycKLR k Q a ν) :
    cycTrace hQ hlead ha hΛ hdeg ν (x * y) = cycTrace hQ hlead ha hΛ hdeg ν (y * x) := by
  rw [cycTrace_mul, cycTrace_mul]
  congr 1
  obtain ⟨rx, rfl⟩ := CycKLR.mk_surjective x
  obtain ⟨ry, rfl⟩ := CycKLR.mk_surjective y
  rw [cycAct_mk, cycAct_mk, ← vacAct_mul, ← vacAct_mul, trace_vacAct, trace_vacAct, map_mul,
    map_mul, RouqFamily.wordTrace₂_mul_comm _ _
      (RouqFamily.klrAct_mem_cycSubalgebra _ _ _
        (cyclotomicFamily_crossCyclic hQ hlead ha hΛ hdeg hsupp hsym) _)]

include hQ hlead ha hΛ hdeg hsupp hsym in
/-- **Webster, arXiv:1309.3796v3, Theorem 3.18 and Remark 3.19**, for `t_ij = t_ji`: over a
field the cyclotomic KLR algebra `R^Λ(ν)` is a symmetric Frobenius algebra. -/
theorem cyclotomic_trace_symmetric (ν : Multiset I) :
    ∃ tr : CycKLR k Q a ν →ₗ[k] k,
      ((∀ x, x ≠ 0 → ∃ y, tr (x * y) ≠ 0) ∧ ∀ y, y ≠ 0 → ∃ x, tr (x * y) ≠ 0) ∧
        ∀ x y, tr (x * y) = tr (y * x) :=
  ⟨cycTrace hQ hlead ha hΛ hdeg ν, cycTrace_nondegenerate hQ hlead ha hΛ hdeg ν,
    cycTrace_mul_comm hQ hlead ha hΛ hdeg hsupp hsym⟩

end

/-- **Webster, arXiv:1309.3796v3, Theorem 3.18 and Remark 3.19**, in Webster's setting: for
Rouquier's homogeneous parameters `Q` over a field whose two extremal coefficients agree
(`t_ij = t_ji`), and a cyclotomic quotient of weight `Λ`, the cyclotomic KLR algebra `R^Λ(ν)`
carries a `k`-linear trace that is nondegenerate on both sides and symmetric. -/
theorem _root_.Categorification.KLR.IsRouquierQ.cyclotomic_frobenius_symmetric
    {I : Type u} [DecidableEq I] {k : Type v} [Field k]
    {C : QuantumGroup.CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
    (hsym : ∀ i j, i ≠ j → extremalCoeff C Q i j = extremalCoeff C Q j i)
    {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : QuantumGroup.UDot.WeightDatum C X Y)
    (Λ : X) {a : I → Polynomial k} (ha : ∀ j, (a j).Monic)
    (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ) (ν : Multiset I) :
    ∃ tr : CycKLR k Q a ν →ₗ[k] k,
      ((∀ x, x ≠ 0 → ∃ y, tr (x * y) ≠ 0) ∧ ∀ y, y ≠ 0 → ∃ x, tr (x * y) ≠ 0) ∧
        ∀ x y, tr (x * y) = tr (y * x) :=
  cyclotomic_trace_symmetric hQ.klrSymm hQ.polyInY_leading ha hΛ
    (fun i j hji => hQ.polyInY_degree_pair RD i j hji)
    (fun i j h => coeff_eq_zero_of_lt_of_hom C (hQ.homogeneous i j h)) hsym ν

/-- The extremal coefficients of the Khovanov–Lauda polynomials `Q_ij = u^{d_ij} + v^{d_ji}`
are `1`. -/
theorem extremalCoeff_qCL_kl {I : Type u} [DecidableEq I] {k : Type v} [Field k]
    {C : QuantumGroup.CartanDatum I} (i j : I) (hij : i ≠ j) :
    extremalCoeff C (KL3.Diagram.CL.qCL (KL3.Diagram.CL.CLScalars.kl : KL3.Diagram.CL.CLScalars C k))
      i j = 1 := by
  unfold extremalCoeff KL3.Diagram.CL.qCL
  split_ifs with h
  · rw [(C.dij_eq_zero_iff hij).2 h, Finsupp.single_zero, MvPolynomial.coeff_C]
    simp
  · have h' : C.dij j i ≠ 0 := fun h0 => h (by rw [C.symm]; exact (C.dij_eq_zero_iff hij.symm).1 h0)
    simp [MvPolynomial.coeff_X_pow, Finsupp.single_eq_single_iff, h']

/-- **Webster, arXiv:1309.3796v3, Theorem 3.18 and Remark 3.19** for the Khovanov–Lauda
scalars `t_ij = 1`, `Q_ij = u^{d_ij} + v^{d_ji}`: the cyclotomic KLR algebra `R^Λ(ν)` is a
symmetric Frobenius algebra. -/
theorem cyclotomic_frobenius_symmetric_kl
    {I : Type u} [DecidableEq I] {k : Type v} [Field k] {C : QuantumGroup.CartanDatum I}
    (hQ : IsRouquierQ C
      (KL3.Diagram.CL.qCL (KL3.Diagram.CL.CLScalars.kl : KL3.Diagram.CL.CLScalars C k)))
    {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y] (RD : QuantumGroup.UDot.WeightDatum C X Y)
    (Λ : X) {a : I → Polynomial k} (ha : ∀ j, (a j).Monic)
    (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ) (ν : Multiset I) :
    ∃ tr : CycKLR k (KL3.Diagram.CL.qCL (KL3.Diagram.CL.CLScalars.kl : KL3.Diagram.CL.CLScalars C k))
        a ν →ₗ[k] k,
      ((∀ x, x ≠ 0 → ∃ y, tr (x * y) ≠ 0) ∧ ∀ y, y ≠ 0 → ∃ x, tr (x * y) ≠ 0) ∧
        ∀ x y, tr (x * y) = tr (y * x) :=
  hQ.cyclotomic_frobenius_symmetric (fun i j hij => by
    rw [extremalCoeff_qCL_kl i j hij, extremalCoeff_qCL_kl j i (Ne.symm hij)]) RD Λ ha hΛ ν

end Categorification.KLR.CyclotomicAction
