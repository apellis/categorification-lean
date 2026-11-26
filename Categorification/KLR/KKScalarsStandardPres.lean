/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CL.Rescale
import Categorification.Diagrams.CL.Specialize
import Categorification.KLR.KKScalarsStandard

/-!
# The Cautis–Lauda presentation at the standard Khovanov–Lauda polynomials

The Cautis–Lauda polynomials `qCL S i j` only use the coefficients `s^{pq}_{ij}` with
`p < d_{ij}` and `q < d_{ji}`, so the presentation `presCL` only depends on these
(`presCL_congr_range`). For KLR polynomials equal to the Khovanov–Lauda ones, the scalars
`kkScalars` of Kang–Kashiwara agree with the Khovanov–Lauda scalars in these degrees, so the
Cautis–Lauda presentation with the scalars of `Q` is the presentation of Khovanov–Lauda III
(`presCL_kkScalars_of_kl`). This identifies the black part of the cyclotomic representation of
Webster, arXiv:1309.3796v3, Theorem 4.25, with an action of the 2-category of KL III.
-/

noncomputable section

namespace Categorification.KL3.Diagram.CL

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation MvPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

section Congr

omit [AddCommGroup X] [AddCommGroup Y] in
/-- `qCL S i j` only depends on `t_{ij}`, `t_{ji}` and the `s^{pq}_{ij}` with `p < d_{ij}`,
`q < d_{ji}`. -/
theorem qCL_congr_range {S S' : CLScalars C k} (ht : ∀ i j, i ≠ j → S.t i j = S'.t i j)
    (hs : ∀ i j p q, i ≠ j → p < C.dij i j → q < C.dij j i → S.s i j p q = S'.s i j p q)
    {i j : I} (h : i ≠ j) : qCL S i j = qCL S' i j := by
  unfold qCL
  rw [ht i j h, ht j i (Ne.symm h)]
  split_ifs
  · rfl
  · congr 1
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    rw [hs i j p q h (Finset.mem_range.1 hp) (Finset.mem_range.1 hq)]

variable (RD k) in
/-- The relations of `U_Q(g)` only depend on `t_{ij}` for `i ≠ j`, on `r` and on the
`s^{pq}_{ij}` with `i ≠ j`, `p < d_{ij}`, `q < d_{ji}`. -/
theorem relationCL_congr_range {S S' : CLScalars C k} (ht : ∀ i j, i ≠ j → S.t i j = S'.t i j)
    (hs : ∀ i j p q, i ≠ j → p < C.dij i j → q < C.dij j i → S.s i j p q = S'.s i j p q)
    (hr : S.r = S'.r) : relationCL RD k S = relationCL RD k S' := by
  have ht' : S.t = S'.t := by
    funext i j
    by_cases h : i = j
    · subst h; rw [S.t_self, S'.t_self]
    · exact ht i j h
  funext r
  cases r with
  | klr μ x =>
    dsimp only [relationCL]
    rw [relationR_congr k (fun c d h => qCL_congr_range ht hs h) (by rw [hr])]
  | _ => dsimp only [relationCL] <;> simp only [ht', hr]

variable (RD k) in
/-- `U_Q(g)` only depends on `t_{ij}` for `i ≠ j`, on `r` and on the `s^{pq}_{ij}` with
`i ≠ j`, `p < d_{ij}`, `q < d_{ji}`. -/
theorem presCL_congr_range {S S' : CLScalars C k} (ht : ∀ i j, i ≠ j → S.t i j = S'.t i j)
    (hs : ∀ i j p q, i ≠ j → p < C.dij i j → q < C.dij j i → S.s i j p q = S'.s i j p q)
    (hr : S.r = S'.r) : presCL RD k S = presCL RD k S' := by
  rw [presCL, presCL, relationCL_congr_range RD k ht hs hr]

end Congr

end Categorification.KL3.Diagram.CL

namespace Categorification.KLR

universe v

open QuantumGroup KL3.Diagram

variable {I : Type*} [DecidableEq I] {C : CartanDatum I} {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]

variable (RD : UDot.WeightDatum C X Y) in
/-- **The Cautis–Lauda presentation with the scalars of the Khovanov–Lauda polynomials is the
presentation of Khovanov–Lauda III**: if `Q_ij = qCL kl i j` for `i ≠ j`, then
`presCL (kkScalars Q) = pres`. -/
theorem presCL_kkScalars_of_kl (hQ : KLRSymm Q)
    (hunit : ∀ i j, i ≠ j → IsUnit (extremalCoeff C Q i j))
    (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j) :
    CL.presCL RD k (kkScalars C hQ hunit) = pres RD k :=
  (CL.presCL_congr_range RD k (S' := CL.CLScalars.kl) (fun _ _ h => kkScalars_t_eq_one hQ hunit fun _ => hstd _ _ h)
    (fun _ _ _ _ h hp hq => kkScalars_s_eq_zero_of_kl hQ hunit (fun _ => hstd _ _ h) hp hq)
    rfl).trans (CL.presCL_kl RD k)

end Categorification.KLR
