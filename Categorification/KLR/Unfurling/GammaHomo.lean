/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Gamma
import Categorification.KLR.Unfurling.SeriesAction
import Categorification.KLR.BasisTheorem

/-!
# Webster's Lemma `lem:gamma-homo`

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras* (arXiv:1603.06311v3), §3.3, Lemma label
`lem:gamma-homo`: the formulas with labels `com0new`–`com0newerer` define an injective
homomorphism `γ : R → 𝖱̂` from the KLR algebra of `I` to the graded completion of the KLR
algebra of the unfurled index set.

* `Unfurling.gamma`: the homomorphism `γ : R(ν) → ∏_{ν̃.map π = ν} 𝖱̂(ν̃)`, for an unfurling
  datum `D` over a field and any `Q` with a factorization `Q a b = P b a · P a b(v, u)`;
* `Unfurling.gamma_intertwine`: `γ(r)` acts on the completed polynomial representation of the
  unfurled algebra as `r` acts on `Pol_ν`, through the substitution `γ_P`;
* `Unfurling.gamma_injective`: `γ` is injective when `π` is surjective (all spectra nonempty)
  and `P a b ≠ 0` for `a ≠ b`.

The proof is Webster's: the images of the generators intertwine `γ_P` (`Unfurling.Intertwine`),
so the images of the two sides of a relation act equally on the image of `γ_P`; this image is
dense (`Unfurling.Density`), the action is continuous and faithful
(`Unfurling.CompletedPolyRep`), so `γ` respects the relations. Injectivity follows from the
injectivity of `γ_P` and of the polynomial representation (KL I Cor. 2.6).

Comparison with the source. Webster works over an algebraically closed field with the
polynomials `P_{ij}` of a Cartan datum and possibly infinite spectra; here `k` is any field, the
parameters are any `Q` admitting the polynomial-representation factorization, and `J` is any
index set with the data of `UnfurlingDatum` (built from finite spectra by
`UnfurlingDatum.ofSpectra` when the `P_{ij}` are weighted homogeneous). The completion is taken
for the grading `unfGrading`, which differs from the symmetric grading of `𝖱` by a bounded shift
on each idempotent and has the same completion.
-/

namespace Categorification.KLR.Unfurling

open MvPolynomial TypeA PolyRep KLRAlgebra GradingDatum


variable {I J : Type*} [DecidableEq I] [DecidableEq J] {k : Type*} [Field k]
  {P Q : I → I → MvPolynomial (Fin 2) k} (D : UnfurlingDatum k P J)
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  {ν : Multiset I}

omit [DecidableEq I] [DecidableEq J] in
theorem unfPQ : ∀ a b : J, a ≠ b →
    unfQ (k := k) D.arrows a b = unfP D.arrows b a * rename ![1, 0] (unfP D.arrows a b) :=
  fun a b _ => unfQ_eq D.arrows a b

omit [DecidableEq I] in
theorem unfPdeg : ∀ a b : J, a ≠ b →
    (unfP (k := k) D.arrows a b).IsWeightedHomogeneous
      ![(unfGrading (k := k) D.arrows).degX b, (unfGrading (k := k) D.arrows).degX a]
      ((unfGrading (k := k) D.arrows).degΨ a b) := by
  intro a b hab
  have := unfP_isWeightedHomogeneous (k := k) D.arrows a b
  simpa [unfGrading, hab] using this

/-- The action of `𝖱̂(ν̃)` on the completed polynomial representation. -/
noncomputable abbrev actU {ν' : Multiset J} (f : HahnSeries ℤ (UnfKLR D ν'))
    (v : HahnSeries ℤ (Pol k ν')) : HahnSeries ℤ (Pol k ν') :=
  act (unfPQ D) f v

/-- The decomposition of `Pol_ν̃` into homogeneous components. -/
noncomputable abbrev decU {ν' : Multiset J} : Pol k ν' →ₗ[k] HahnSeries ℤ (Pol k ν') :=
  decomp (unfGrading (k := k) D.arrows)

omit [DecidableEq I] in
theorem actU_toC {ν' : Multiset J} (a : UnfKLR D ν') (f : Pol k ν') :
    actU D (↑(toC D a)) (decU D f) = decU D (polyRep (unfPQ D) a f) := by
  rw [coe_toCompletion_eq_ser]
  exact act_ser_decomp (unfPQ D) _ (unfPdeg D) a f

omit [DecidableEq I] in
theorem actU_sum {ν' : Multiset J} {ι : Type*} (s : Finset ι) (f : ι → HahnSeries ℤ (UnfKLR D ν'))
    (v : HahnSeries ℤ (Pol k ν')) :
    actU D (∑ x ∈ s, f x) v = ∑ x ∈ s, actU D (f x) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [actU, zero_act]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, actU, add_act, ← actU]
    exact congrArg _ ih

variable {ν' : Multiset J} (hν : ν'.map D.π = ν)

theorem genImage_idem_intertwine (i : Seq ν) (p : Pol k ν) :
    actU D (↑(genImage D hν (.idem i))) (decU D (polySubst D.π D.pw hν p)) =
      decU D (polySubst D.π D.pw hν (opE i p)) := by
  rw [genImage, ← map_sum, actU_toC, map_sum]
  congr 1
  funext t
  rw [polySubst_opE, LinearMap.sum_apply, Finset.sum_apply]
  simp only [polyRep_e, opE_apply]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_filter, eq_comm]

theorem genImage_dot_intertwine (a : Fin (Multiset.card ν)) (p : Pol k ν) :
    actU D (↑(genImage D hν (.dot a))) (decU D (polySubst D.π D.pw hν p)) =
      decU D (polySubst D.π D.pw hν (opX a p)) := by
  rw [genImage, ← map_sum, actU_toC, map_sum]
  congr 1
  funext t
  rw [polySubst_opX, LinearMap.sum_apply, Finset.sum_apply]
  simp only [map_mul, polyRep_pol, polyRep_e, Module.End.mul_apply]
  rw [Finset.sum_eq_single t]
  · simp [opMul]
  · intro b _ hb
    simp [opMul, Ne.symm hb]
  · simp

omit [DecidableEq I] in
theorem constantCoeff_coe_eq {σ : Type*} (R : MvPolynomial σ k) :
    MvPowerSeries.constantCoeff (R : MvPowerSeries σ k) = MvPolynomial.constantCoeff R := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    MvPolynomial.constantCoeff_eq]

omit [DecidableEq I] in
/-- The inverse of a polynomial with unit constant term, applied on the summand `t`. -/
theorem actU_serU_invOfUnit (t : Seq ν') (R : MvPolynomial (Fin (Multiset.card ν')) k) (u : kˣ)
    (hu : MvPolynomial.constantCoeff R = u) {g y : Pol k ν'} (hy : R * y t = g t) :
    actU D (↑(serU D t ((R : MvPowerSeries _ k).invOfUnit u))) (decU D g) =
      decU D (Pi.single t (y t)) := by
  refine act_seriesAt_decomp (unfPQ D) (unf_degX_pos D) t _ ?_ ?_
  · rw [Pi.single_eq_same, ← hy, MvPolynomial.coe_mul, ← mul_assoc,
      MvPowerSeries.invOfUnit_mul _ u (by rw [constantCoeff_coe_eq, hu]), one_mul]
  · intro t' ht'
    exact Pi.single_eq_of_ne ht' _

/-- The image of a crossing, on the output summand `t`. -/
theorem crossImage_intertwine {j : ℕ} (h : j + 1 < Multiset.card ν) (t : Seq ν') (p : Pol k ν) :
    actU D (↑(crossImage D hν h t)) (decU D (polySubst D.π D.pw hν p)) =
      decU D (Pi.single t (polySubst D.π D.pw hν (opΨ P j p) t)) := by
  unfold crossImage
  simp only
  split_ifs with hc hab
  · rw [Subalgebra.coe_mul, actU, act_mul, ← actU, ← actU, actU_toC, polyRep_ψ]
    exact actU_serU_invOfUnit D t _ _ (by rw [constantCoeff_rename]; rfl)
      (pwDiff_mul_polySubst_opΨ_of_eq_label D hν h p t hab)
  · rw [Subalgebra.coe_mul, actU, act_mul, ← actU, ← actU, actU_toC, map_sub, polyRep_ψ,
      polyRep_e]
    refine actU_serU_invOfUnit D t _ _ ?_ ?_
    rotate_left
    · simp only [LinearMap.sub_apply, Pi.sub_apply, opE_apply, ite_true]
      exact pwSub_mul_polySubst_opΨ_of_ne_label D hν h p t hc hab
    rw [map_sub, pwAt, pwAt, constantCoeff_aeval_X, constantCoeff_aeval_X]
    rfl
  · rw [actU_toC]
    congr 1
    funext t'
    simp only [map_mul, polyRep_pol, polyRep_e, polyRep_ψ, Module.End.mul_apply]
    by_cases ht : t' = t
    · subst ht
      rw [Pi.single_eq_same, polySubst_opΨ_of_ne_colour D hν h p t' hc]
      simp [opMul, posL, posR]
    · rw [Pi.single_eq_of_ne ht]
      simp [opMul, ht]

theorem genImage_cross_intertwine (j : ℕ) (p : Pol k ν) :
    actU D (↑(genImage D hν (.cross j))) (decU D (polySubst D.π D.pw hν p)) =
      decU D (polySubst D.π D.pw hν (opΨ P j p)) := by
  rw [genImage]
  split_ifs with h
  · rw [AddSubmonoidClass.coe_finsetSum, actU_sum]
    simp only [crossImage_intertwine D hν h]
    rw [← map_sum, Finset.univ_sum_single]
  · simp only [opΨ, h, dite_false, LinearMap.zero_apply, map_zero, ZeroMemClass.coe_zero]
    exact zero_act _ _

/-- `γ` on the free algebra intertwines `γ_P` (Webster, proof of Lemma label `lem:gamma-homo`). -/
theorem freeGamma_intertwine (u : FreeAlgebra k (Gen ν)) (ν'' : Lift D ν) (p : Pol k ν) :
    actU D (↑(freeGamma D u ν'')) (decU D (polySubst D.π D.pw ν''.2 p)) =
      decU D (polySubst D.π D.pw ν''.2 (freeRep ν P u p)) := by
  induction u using FreeAlgebra.induction generalizing p with
  | grade0 r =>
    rw [AlgHom.commutes, Pi.algebraMap_apply, ← (toC D).commutes r, actU_toC, AlgHom.commutes,
      AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, map_smul,
      map_smul]
  | grade1 g =>
    rw [freeGamma, FreeAlgebra.lift_ι_apply]
    cases g with
    | idem i => rw [freeRep_fe]; exact genImage_idem_intertwine D ν''.2 i p
    | dot a => rw [freeRep_fx]; exact genImage_dot_intertwine D ν''.2 a p
    | cross j => rw [freeRep_fψ]; exact genImage_cross_intertwine D ν''.2 j p
  | mul a b ha hb =>
    rw [map_mul, Pi.mul_apply, Subalgebra.coe_mul, actU, act_mul, ← actU, ← actU, hb, ha,
      map_mul, Module.End.mul_apply]
  | add a b ha hb =>
    rw [map_add, Pi.add_apply, Subalgebra.coe_add, actU, add_act, ← actU, ← actU, ha, hb,
      map_add, LinearMap.add_apply, map_add, map_add]

omit [DecidableEq I] [DecidableEq J] in
theorem weight_two {σ : Type*} (c : σ →₀ ℕ) :
    Finsupp.weight (fun _ => (2 : ℤ)) c = 2 * (c.degree : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.degree_apply, Nat.cast_sum, Finset.mul_sum, Finsupp.sum]
  exact Finset.sum_congr rfl fun a _ => by simp [mul_comm]

omit [DecidableEq I] in
/-- The image of `γ_P` is dense in the graded-adic sense (Chinese remainder theorem). -/
theorem isGradedDense_range_polySubst :
    IsGradedDense (unfGrading (k := k) D.arrows) (Set.range (polySubst D.π D.pw hν)) := by
  intro Dd q
  obtain ⟨p, hp⟩ := exists_polySubst_coeff_sub_eq_zero D.π hν D.pw D.pw_coeff_one
    D.pw_coeff_zero_inj Dd.toNat q
  refine ⟨_, ⟨p, rfl⟩, fun e he => ?_⟩
  funext t
  ext c
  rw [homPart_apply, coeff_weightedHomogeneousComponent, Pi.zero_apply]
  split_ifs with hc
  · have hw : (wt (unfGrading (k := k) D.arrows) t) = fun _ => (2 : ℤ) := rfl
    rw [hw, weight_two] at hc
    have : c.degree < Dd.toNat := by omega
    have := hp t c this
    rw [coeff_sub] at this
    rw [Pi.sub_apply, coeff_sub]
    show _ = (0 : k)
    linear_combination -this
  · simp

omit [DecidableEq I] in
theorem decU_injective : Function.Injective (decU D (ν' := ν')) := by
  intro f g hfg
  have h : ∀ e, homPart (unfGrading (k := k) D.arrows) e f =
      homPart (unfGrading (k := k) D.arrows) e g := fun e => by
    have := congrArg (fun v => HahnSeries.coeff v e) hfg
    simpa using this
  let S := degrees (unfGrading (k := k) D.arrows) f ∪ degrees (unfGrading (k := k) D.arrows) g
  calc f = ∑ e ∈ S, homPart (unfGrading (k := k) D.arrows) e f :=
        (sum_homPart _ fun e he => homPart_eq_zero_of_notMem _ fun h' =>
          he (Finset.mem_union_left _ h')).symm
    _ = ∑ e ∈ S, homPart (unfGrading (k := k) D.arrows) e g := Finset.sum_congr rfl fun e _ => h e
    _ = g := sum_homPart _ fun e he => homPart_eq_zero_of_notMem _ fun h' =>
          he (Finset.mem_union_right _ h')

include hPQ in
/-- `γ` respects the defining relations of `R(ν)`. -/
theorem freeGamma_rel ⦃x y : FreeAlgebra k (Gen ν)⦄ (h : Rel k Q ν x y) :
    freeGamma D x = freeGamma D y := by
  funext ν''
  apply Subtype.ext
  refine eq_of_act_decomp_eq (unfPQ D) _ (fun a b _ => unfP_ne_zero _ a b)
    (isGradedDense_range_polySubst D ν''.2) ?_
  rintro _ ⟨p, rfl⟩
  rw [← actU, ← actU, freeGamma_intertwine, freeGamma_intertwine, freeRep_rel hPQ h]

/-- **Webster, arXiv:1603.06311v3, §3.3, Lemma label `lem:gamma-homo`** (the homomorphism):
the formulas `com0new`–`com0newerer` define an algebra homomorphism
`γ : R(ν) → ∏_{ν̃.map π = ν} 𝖱̂(ν̃)`. -/
noncomputable def gamma : KLRAlgebra k Q ν →ₐ[k] ∀ ν'' : Lift D ν, UnfCompl D ν''.1 :=
  RingQuot.liftAlgHom k ⟨freeGamma D, freeGamma_rel D hPQ⟩

theorem gamma_mk (u : FreeAlgebra k (Gen ν)) : gamma D hPQ (mk k Q ν u) = freeGamma D u :=
  RingQuot.liftAlgHom_mkAlgHom_apply k (freeGamma D) _ u

/-- `γ` intertwines the substitution `γ_P` of polynomial representations. -/
theorem gamma_intertwine (r : KLRAlgebra k Q ν) (ν'' : Lift D ν) (p : Pol k ν) :
    actU D (↑(gamma D hPQ r ν'')) (decU D (polySubst D.π D.pw ν''.2 p)) =
      decU D (polySubst D.π D.pw ν''.2 (polyRep hPQ r p)) := by
  obtain ⟨u, rfl⟩ := mk_surjective r
  rw [gamma_mk, polyRep_mk]
  exact freeGamma_intertwine D u ν'' p

section Injective

variable (hsurj : Function.Surjective D.π)

omit [DecidableEq I] [DecidableEq J] in
theorem map_surjInv : (ν.map (Function.surjInv hsurj)).map D.π = ν := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id ν]
  exact Multiset.map_congr rfl fun i _ => Function.surjInv_eq hsurj i

omit [DecidableEq I] [DecidableEq J] in
/-- Every sequence of weight `ν` lifts to weight `ν.map (surjInv π)`. -/
theorem exists_down_eq (i : Seq ν) :
    ∃ t : Seq (ν.map (Function.surjInv hsurj)), down D.π (map_surjInv D hsurj (ν := ν)) t = i := by
  have hc := card_eq D.π (map_surjInv D hsurj (ν := ν))
  refine ⟨⟨fun a => Function.surjInv hsurj (i.lbl (Fin.cast hc.symm a)), ?_⟩, ?_⟩
  · have h1 : (Finset.univ.val.map fun a => i.lbl (Fin.cast hc.symm a)) = ν := by
      rw [show (fun a => i.lbl (Fin.cast hc.symm a)) = i.1 ∘ finCongr hc.symm from rfl,
        ← Multiset.map_map, Multiset.map_univ_val_equiv]
      exact i.2
    have := congrArg (Multiset.map (Function.surjInv hsurj)) h1
    rw [Multiset.map_map] at this
    exact this
  · apply Subtype.ext
    funext a
    show D.π (Function.surjInv hsurj (i.lbl (Fin.cast hc.symm (Fin.cast hc a)))) = i.lbl a
    rw [Fin.cast_cast, Fin.cast_eq_self]
    exact Function.surjInv_eq hsurj _

include hsurj in
/-- **Webster, arXiv:1603.06311v3, §3.3, Lemma label `lem:gamma-homo`** (injectivity): if every
label of `I` has a preimage in `J` (nonempty spectra) and `P a b ≠ 0` for `a ≠ b`, then `γ` is
injective. -/
theorem gamma_injective (hP : ∀ a b, a ≠ b → P a b ≠ 0) :
    Function.Injective (gamma D hPQ (ν := ν)) := by
  intro r s hrs
  apply polyRep_injective hPQ hP
  refine LinearMap.ext fun p => ?_
  let ν'' : Lift D ν := ⟨_, map_surjInv D hsurj⟩
  refine polySubst_injective D.π ν''.2 D.pw D.pw_coeff_one (exists_down_eq D hsurj)
    (decU_injective D ?_)
  rw [← gamma_intertwine, ← gamma_intertwine, hrs]

end Injective

end Categorification.KLR.Unfurling
