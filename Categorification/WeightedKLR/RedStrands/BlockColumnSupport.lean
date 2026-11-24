/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockShuffleCoordinateSupport

/-!
# The supported corner in the row quotient

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8, (6.21). A quotient class
fixed by the loading idempotents at a placed upper loading and a source-order
lower loading belongs to the juxtaposed column. A right-multiplication kernel
criterion on that column then implies the corresponding higher-ideal membership
criterion on representatives.
-/

noncomputable section

namespace Categorification.Stendhal.RedBlock

open KLR KLRAlgebra BraidedStendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (L M : List (Fin ℓ × Multiset I)) (f : Fin 2 ↪ Fin ℓ) (β : Multiset I) {ν : Multiset I}

local notation "row" => adjacentRow L M f β
local notation "μ" => stendhalWeight ℓ ν
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "α" => fun r i => boundaryCount (cut (f 0) (f 1) r) i row
local notation "κ" => L.map Prod.fst ++ f 0 :: f 1 :: M.map Prod.fst
local notation "J" => blockUpperIdeal k Q Λ ν (f 0) (f 1) α κ
local notation "p" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "q" => RingCon.mkₐ k (TwoSidedIdeal.ringCon J)
local notation "π" => AlgHom.comp q p
local notation "S" => affineStackBlocks Q Λ L M f β
local notation "F" => stackBlocks Q Λ L M f β
local notation "E" => orderedIdem Q Λ (fun _ => 1) row
local notation "pκ" => violMk k Q Λ ν (redProj k Q Λ ν κ)

/-- The left and right loading cuts of a quotient class put it in the ordinary column
when the upper loading is placed in the prescribed orders and the lower order is the
source order (Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8). -/
theorem mem_blockColumn_of_fixed_loadings (h : weightSum row = μ)
    (s : Loadings row) (ho : UncrossedLoading row s) (s₀ : Seq μ)
    (horder : redWord s₀ = κ) (z : (J).ringCon.Quotient) :
    let t := Seq.cast h (place row s)
    π (e t) * z = z → z * π (e s₀) = z →
      z ∈ blockColumn Q Λ L M f β h := by
  intro t hl hr
  change q (p (e t)) * z = z at hl
  change z * q (p (e s₀)) = z at hr
  have hordered : S h E * e t = e t :=
    affineStackBlocks_orderedIdem_mul_placed Q Λ L M f β h s ho
  have left : F h 1 * p (e t) = p (e t) := by
    change p (S h 1) * p (e t) = p (e t)
    rw [← map_mul p]
    apply congrArg p
    calc
      S h 1 * e t = S h 1 * (S h E * e t) := congrArg (S h 1 * ·) hordered.symm
      _ = e t := by rw [← mul_assoc, ← map_mul (S h), one_mul, hordered]
  have right : p (e s₀) * pκ = p (e s₀) := by
    change p (e s₀) * p (redIdem k Q Λ κ) = p (e s₀)
    rw [← map_mul p, e_mul_redIdem, ite_eq_left horder]
  obtain ⟨v, hv⟩ := RingCon.mkₐ_surjective («α» := k) (TwoSidedIdeal.ringCon J) z
  refine ⟨p (e t) * v * p (e s₀), ?_⟩
  change q (F h 1 * ((p (e t) * v * p (e s₀)) * pκ)) = z
  calc
    _ = q ((F h 1 * p (e t)) * v * p (e s₀)) := by simp only [mul_assoc, right]
    _ = z := by rw [left, map_mul q, map_mul q, hv, hl, hr]

/-- A supported right-multiplication kernel criterion on the quotient column gives the
corresponding higher-ideal membership criterion before quotienting. This is the interface
for the right leg in Webster, arXiv:1309.3796v2, §6.1, (6.21). -/
theorem mem_blockUpperIdeal_of_blockColumn_right_kernel (h : weightSum row = μ)
    (s : Loadings row) (ho : UncrossedLoading row s) (s₀ : Seq μ)
    (horder : redWord s₀ = κ) (r : R) :
    let t := Seq.cast h (place row s)
    (∀ x : blockColumn Q Λ L M f β h,
      π (e t) * x.1 = x.1 → x.1 * π (e s₀) = x.1 → x.1 * π r = 0 → x = 0) →
    ∀ v : V, p (e t) * v * p (e s₀) = v → v * p r ∈ J → v ∈ J := by
  intro t hkernel v hv hm
  have hleft : p (e t) * v = v := by
    calc
      _ = p (e t) * (p (e t) * v * p (e s₀)) := congrArg (p (e t) * ·) hv.symm
      _ = v := by rw [← mul_assoc, ← mul_assoc, ← map_mul p (e t) (e t), e_mul_self, hv]
  have hright : v * p (e s₀) = v := by
    calc
      _ = (p (e t) * v * p (e s₀)) * p (e s₀) := congrArg (· * p (e s₀)) hv.symm
      _ = v := by rw [mul_assoc (p (e t) * v), ← map_mul p (e s₀) (e s₀), e_mul_self, hv]
  have hl : π (e t) * q v = q v := (map_mul q _ _).symm.trans (congrArg q hleft)
  have hr : q v * π (e s₀) = q v := (map_mul q _ _).symm.trans (congrArg q hright)
  have hq_zero (a : V) : q a = 0 ↔ a ∈ J := by
    change (J).ringCon.mk' a = 0 ↔ _
    rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  let x : blockColumn Q Λ L M f β h :=
    ⟨q v, mem_blockColumn_of_fixed_loadings Q Λ L M f β h s ho s₀ horder (q v) hl hr⟩
  have hz : x.1 * π r = 0 :=
    (map_mul q v (p r)).symm.trans ((hq_zero _).2 hm)
  exact (hq_zero _).1 (congrArg Subtype.val (hkernel x hl hr hz))

end Categorification.Stendhal.RedBlock
