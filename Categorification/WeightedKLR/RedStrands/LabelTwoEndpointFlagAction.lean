/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalPolyRep
import Categorification.WeightedKLR.RedStrands.OrderProjection

import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorSlide
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
import Mathlib.Algebra.DualNumber

/-!
# Oriented polynomial flags at the label-two exterior cut

Webster, arXiv:1309.3796v2, §8.2, printed page 80. The orientation
chooses pure positional relabeling for moving a black strand rightwards
across the second red. The flags send the two black dots to opposite
square-zero coordinates. The polynomial action preserving any specified
family of flags descends through the Stendhal red relations.
-/

namespace Categorification.Stendhal.LabelTwo
open MvPolynomial Equiv

noncomputable section
variable {k σ τ : Type*} [CommRing k]

/-- Positional polynomial flag where the two black dot coordinates are opposite
square-zero variables. -/
def endpointFlagIdeal (a b : σ) : Ideal (MvPolynomial σ k) :=
  Ideal.span {X a + X b, X a ^ 2, X b ^ 2}

theorem sum_mem_endpointFlagIdeal (a b : σ) :
    (X a + X b : MvPolynomial σ k) ∈ endpointFlagIdeal a b :=
  Ideal.subset_span (by simp)

theorem left_sq_mem_endpointFlagIdeal (a b : σ) :
    (X a ^ 2 : MvPolynomial σ k) ∈ endpointFlagIdeal a b :=
  Ideal.subset_span (by simp)

theorem right_sq_mem_endpointFlagIdeal (a b : σ) :
    (X b ^ 2 : MvPolynomial σ k) ∈ endpointFlagIdeal a b :=
  Ideal.subset_span (by simp)

theorem rename_mem_endpointFlagIdeal (u : σ → τ) (a b : σ)
    {p : MvPolynomial σ k} (hp : p ∈ endpointFlagIdeal a b) :
    rename u p ∈ endpointFlagIdeal (u a) (u b) := by
  have h : endpointFlagIdeal a b ≤ (endpointFlagIdeal (k := k) (u a) (u b)).comap (rename u) := by
    apply Ideal.span_le.2
    intro f hf
    change rename u f ∈ endpointFlagIdeal (u a) (u b)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · simpa only [map_add, rename_X] using sum_mem_endpointFlagIdeal (k := k) (u a) (u b)
    · simpa only [map_pow, rename_X] using left_sq_mem_endpointFlagIdeal (k := k) (u a) (u b)
    · simpa only [map_pow, rename_X] using right_sq_mem_endpointFlagIdeal (k := k) (u a) (u b)
  exact h hp

theorem ddiff_mem_endpointFlagIdeal [DecidableEq σ] {a b : σ} (hab : a ≠ b)
    {p : MvPolynomial σ k} (hp : p ∈ endpointFlagIdeal a b) :
    ddiff a b p ∈ endpointFlagIdeal a b := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl | rfl
      · simp [ddiff_X_left hab, ddiff_X_right hab]
      · simpa [pow_two, ddiff_mul hab, ddiff_X_left hab] using
          sum_mem_endpointFlagIdeal (k := k) a b
      · simpa [pow_two, ddiff_mul hab, ddiff_X_right hab, add_comm (X b) (X a)] using
          (endpointFlagIdeal a b).neg_mem (sum_mem_endpointFlagIdeal (k := k) a b)
  | zero => simp
  | add f g _ _ hf hg => simpa only [map_add] using (endpointFlagIdeal a b).add_mem hf hg
  | smul f g hg hdd =>
      rw [smul_eq_mul, ddiff_mul hab]
      apply (endpointFlagIdeal a b).add_mem
      · exact (endpointFlagIdeal a b).mul_mem_left _ hg
      · exact (endpointFlagIdeal a b).mul_mem_left _ hdd


variable [DecidableEq σ]

/-- The square-zero test of an exterior flag. -/
def endpointFlagEval (a b : σ) : MvPolynomial σ k →ₐ[k] DualNumber k :=
  aeval fun i => if i = a then DualNumber.eps else if i = b then -DualNumber.eps else 0

theorem endpointFlagIdeal_le_ker {a b : σ} (hab : a ≠ b) :
    endpointFlagIdeal (k := k) a b ≤ RingHom.ker (endpointFlagEval (k := k) a b).toRingHom := by
  apply Ideal.span_le.2
  intro f hf
  change endpointFlagEval a b f = 0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl
  · simp [endpointFlagEval, hab.symm]
  · simp [endpointFlagEval, pow_two, DualNumber.eps_mul_eps]
  · simp [endpointFlagEval, hab.symm, pow_two, DualNumber.eps_mul_eps]

theorem endpointFlag_coefficients_eq_zero {a b : σ} (hab : a ≠ b) {c d : k}
    (h : C c + C d * X a ∈ endpointFlagIdeal a b) : c = 0 ∧ d = 0 := by
  have hev : endpointFlagEval a b (C c + C d * X a) = 0 :=
    endpointFlagIdeal_le_ker hab h
  have hc := congrArg (fun u : DualNumber k => u.fst) hev
  have hd := congrArg (fun u : DualNumber k => u.snd) hev
  exact ⟨by simpa [endpointFlagEval, TrivSqZeroExt.algebraMap_eq_inl] using hc, by simpa [endpointFlagEval, TrivSqZeroExt.algebraMap_eq_inl] using hd⟩

end
end Categorification.Stendhal.LabelTwo

namespace Categorification.Stendhal.LabelTwoEndpointFlag

open KLR KLRAlgebra KLR.PolyRep MvPolynomial TypeA Equiv

variable {k : Type*} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k)

abbrev weight := stendhalWeight 2 (Multiset.replicate 2 ())
local notation "m" => Multiset.card weight
local notation "R" => MvPolynomial (Fin m) k

/-- The factorization where crossing the second red rightwards from the
black side is a pure positional rename. The first red uses the opposite
orientation to impose the cyclotomic flag. -/
noncomputable def flagP : Unit ⊕ Fin 2 → Unit ⊕ Fin 2 → MvPolynomial (Fin 2) k
  | .inl _, .inl _ => 0
  | .inl _, .inr r => if r = 0 then X 1 ^ 2 else 1
  | .inr r, .inl _ => if r = 0 then 1 else X 0 ^ 2
  | .inr _, .inr _ => 0

noncomputable abbrev weights (_ : Fin 2) : Unit →₀ ℕ := Finsupp.single () 2

theorem flagP_factor : ∀ a b, a ≠ b →
    stendhalQ Q weights a b = flagP b a * rename ![1, 0] (flagP a b) := by
  rintro (i | r) (j | d) h
  · exact (h (by cases i; cases j; rfl)).elim
  · cases i
    fin_cases d <;> simp [stendhalQ, flagP, weights]
  · cases j
    fin_cases r <;> simp [stendhalQ, flagP, weights]
  · simp [stendhalQ, flagP]

/-- Setting red variables to zero commutes with all flag crossings. -/
theorem blackEval_crossComp_flagP (s : Seq weight) (j : ℕ) (h : j + 1 < m) (f : R) :
    blackEval (sadj m j • s) (crossComp (flagP) j h s f) =
      crossComp (flagP) j h s (blackEval s f) := by
  let a : Fin m := ⟨j, by omega⟩
  let b : Fin m := ⟨j + 1, h⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  by_cases he : s.lbl ⟨j, by omega⟩ = s.lbl ⟨j + 1, h⟩
  · have hs : sadj m j • s = s := by rw [sadj_eq h]; exact swap_smul_eq_self he
    simpa only [crossComp, he, hs, ↓reduceIte] using blackEval_ddiff s hab he f
  · simp only [crossComp, he, ↓reduceIte, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul]
    rw [blackEval_rename_perm]
    congr 1
    have hb : (sadj m j • s).lbl b = s.lbl a := by
      simp [b, a, KLR.Seq.lbl, KLR.Seq.smul_apply, sadj_eq h]
    have ha' : (sadj m j • s).lbl a = s.lbl b := by
      simp [b, a, KLR.Seq.lbl, KLR.Seq.smul_apply, sadj_eq h]
    cases ha : s.lbl ⟨j, by omega⟩ with
    | inl i =>
      cases hr : s.lbl ⟨j + 1, h⟩ with
      | inl _ => rw [flagP, map_zero, map_zero]
      | inr r =>
        rw [flagP]
        split_ifs
        · rw [map_pow, rename_X]
          change blackEval (sadj m j • s) (X b ^ 2) = X b ^ 2
          rw [map_pow, blackEval_X, show (sadj m j • s).1 b = .inl i from hb.trans ha]
          rfl
        · rw [map_one, map_one]
    | inr r =>
      cases hr : s.lbl ⟨j + 1, h⟩ with
      | inl i =>
        rw [flagP]
        split_ifs
        · rw [map_one, map_one]
        · rw [map_pow, rename_X]
          change blackEval (sadj m j • s) (X a ^ 2) = X a ^ 2
          rw [map_pow, blackEval_X, show (sadj m j • s).1 a = .inl i from ha'.trans hr]
          rfl
      | inr _ => rw [flagP, map_zero, map_zero]

local notation "PMod" => KLR.PolyRep.Pol k weight
local notation "A" => KLRAlgebra k (stendhalQ Q weights) weight
local notation "FRep" => polyRep (flagP_factor Q)

/-- The simultaneous flag relations on positional polynomial functions. -/
noncomputable def flagRelations (J : Seq weight → Ideal R) : Submodule k PMod where
  carrier := {f | ∀ s, blackEval s (f s) ∈ J s}
  zero_mem' := fun s => by rw [Pi.zero_apply, map_zero]; exact zero_mem _
  add_mem' := fun hf hg s => by
    rw [Pi.add_apply, map_add]
    exact add_mem (hf s) (hg s)
  smul_mem' := fun c f hf s => by
    rw [Pi.smul_apply, map_smul, Algebra.smul_def]
    exact (J s).mul_mem_left _ (hf s)

/-- The sole local condition required for descent to the flag quotients. -/
def PreservesFlags (J : Seq weight → Ideal R) : Prop :=
  ∀ (s : Seq weight) (j : ℕ) (h : j + 1 < m) (p : R), p ∈ J s →
    crossComp (flagP) j h s p ∈ J (sadj m j • s)

theorem flagRelations_stable (J : Seq weight → Ideal R) (hJ : PreservesFlags J)
    (a : A) (f : PMod) (hf : f ∈ flagRelations J) :
    FRep a f ∈ flagRelations J := by
  revert f
  obtain ⟨u, rfl⟩ := mk_surjective a
  induction u using FreeAlgebra.induction with
  | grade0 r =>
    intro f hf
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (flagRelations J).smul_mem r hf
  | grade1 g =>
    intro f hf
    cases g with
    | idem i =>
      change FRep (e i) f ∈ flagRelations J
      rw [polyRep_e]
      intro s
      rw [opE_apply]
      split_ifs with hs
      · subst s; exact hf i
      · rw [map_zero]; exact zero_mem _
    | dot a =>
      change FRep (x a) f ∈ flagRelations J
      rw [polyRep_x]
      intro s
      rw [opX_apply, map_mul]
      exact (J s).mul_mem_left _ (hf s)
    | cross j =>
      change FRep (ψ j) f ∈ flagRelations J
      rw [polyRep_ψ]
      intro s
      by_cases hj : j + 1 < m
      · rw [opΨ_apply (flagP) j hj]
        have hs : sadj m j • (sadj m j • s) = s := sadj_smul_sadj_smul s j
        have h := blackEval_crossComp_flagP (sadj m j • s) j hj (f (sadj m j • s))
        rw [hs] at h
        rw [h]
        simpa only [hs] using hJ _ j hj _ (hf (sadj m j • s))
      · rw [opΨ_eq_zero (flagP) (j := j) (Nat.le_of_not_gt hj), LinearMap.zero_apply, Pi.zero_apply,
          map_zero]
        exact zero_mem _
  | mul u v hu hv =>
    intro f hf
    rw [map_mul, map_mul]
    exact hu _ (hv _ hf)
  | add u v hu hv =>
    intro f hf
    rw [map_add, map_add, LinearMap.add_apply]
    exact add_mem (hu _ hf) (hv _ hf)

/-- The KLR polynomial action on the quotient by the positional flag relations. -/
noncomputable def flagQuotRep (J : Seq weight → Ideal R) (hJ : PreservesFlags J) :
    A →ₐ[k] Module.End k (PMod ⧸ flagRelations J) where
  toFun a := (flagRelations J).mapQ (flagRelations J) (FRep a)
    (fun f hf => flagRelations_stable Q J hJ a f hf)
  map_zero' := by
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := (flagRelations J).mkQ_surjective x
    simp [Submodule.mkQ_apply]
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := (flagRelations J).mkQ_surjective x
    simp [Submodule.mkQ_apply, Submodule.mapQ_apply]
  map_add' a b := by
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := (flagRelations J).mkQ_surjective x
    simp [Submodule.mkQ_apply, Submodule.mapQ_apply]
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := (flagRelations J).mkQ_surjective x
    simp [Submodule.mkQ_apply, Submodule.mapQ_apply, Module.End.mul_apply]
  commutes' c := by
    apply LinearMap.ext
    intro x
    obtain ⟨f, rfl⟩ := (flagRelations J).mkQ_surjective x
    simp [Submodule.mkQ_apply, Submodule.mapQ_apply, Algebra.algebraMap_eq_smul_one]

/-- A zero operator on the flag quotient has every positional test in its
flag ideal after setting red variables to zero. -/
theorem flagQuotRep_eq_zero_eval (J : Seq weight → Ideal R) (hJ : PreservesFlags J)
    {a : A} (ha : flagQuotRep Q J hJ a = 0) (f : PMod) (s : Seq weight) :
    blackEval s (FRep a f s) ∈ J s := by
  have hz := congrArg (fun g : Module.End k (PMod ⧸ flagRelations J) =>
    g ((flagRelations J).mkQ f)) ha
  change Submodule.Quotient.mk (FRep a f) = 0 at hz
  exact ((Submodule.Quotient.mk_eq_zero _).1 hz) s

private theorem flagQuotRep_apply_mkQ (J : Seq weight → Ideal R) (hJ : PreservesFlags J)
    (a : A) (f : PMod) :
    flagQuotRep Q J hJ a ((flagRelations J).mkQ f) =
      (flagRelations J).mkQ (FRep a f) := rfl

private theorem flagQuotRep_red_dot (J : Seq weight → Ideal R) (hJ : PreservesFlags J)
    (a : Fin m) (s : Seq weight) (ha : (s.lbl a).isRight) :
    flagQuotRep Q J hJ (x a * e s) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := (flagRelations J).mkQ_surjective z
  rw [flagQuotRep_apply_mkQ, LinearMap.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  intro t
  rw [map_mul, Module.End.mul_apply, polyRep_x, polyRep_e, opX_apply, opE_apply, map_mul]
  split_ifs with ht
  · subst t
    have hleft : ¬ (s.lbl a).isLeft := by cases hh : s.lbl a <;> simp_all
    rw [blackEval_X, ite_eq_right hleft, zero_mul]
    exact zero_mem _
  · rw [map_zero, mul_zero]
    exact zero_mem _

/-- If the chosen flag at a loading is zero, its idempotent acts by zero. -/
theorem flagQuotRep_e_eq_zero_of_flag_eq_top (J : Seq weight → Ideal R) (hJ : PreservesFlags J)
    (s : Seq weight) (h : J s = ⊤) :
    flagQuotRep Q J hJ (e s) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := (flagRelations J).mkQ_surjective z
  rw [flagQuotRep_apply_mkQ, LinearMap.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  intro t
  rw [polyRep_e, opE_apply]
  split_ifs with ht
  · subst t
    rw [h]
    exact Submodule.mem_top
  · rw [map_zero]; exact zero_mem _

private theorem flagQuotRep_red_cross (J : Seq weight → Ideal R) (hJ : PreservesFlags J)
    (j : ℕ) (hj : j + 1 < m) (s : Seq weight)
    (h₁ : (s.lbl ⟨j, by omega⟩).isRight)
    (h₂ : (s.lbl ⟨j+1, hj⟩).isRight) :
    flagQuotRep Q J hJ (ψ j * e s) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨f, rfl⟩ := (flagRelations J).mkQ_surjective z
  rw [flagQuotRep_apply_mkQ, LinearMap.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  intro t
  rw [map_mul, Module.End.mul_apply, polyRep_ψ, polyRep_e,
    opΨ_apply flagP j hj, opE_apply]
  split_ifs with he
  · rw [he]
    have hzero : crossComp (k := k) flagP j hj s = 0 := by
      cases hl : s.lbl ⟨j, by omega⟩ with
      | inl i => simp [hl] at h₁
      | inr a =>
        cases hr : s.lbl ⟨j+1,hj⟩ with
        | inl i => simp [hr] at h₂
        | inr b =>
          have hn : (s.lbl ⟨j, by omega⟩) ≠ s.lbl ⟨j+1,hj⟩ := by
            intro he
            have hb : s.lbl ⟨j+1,hj⟩ = .inr a := he.symm.trans hl
            have heq := eq_of_lbl_eq_inr hl hb
            exact (Nat.ne_of_lt (Nat.lt_succ_self j)) (congrArg Fin.val heq)
          rw [crossComp, ite_eq_right hn, hl, hr, flagP]
          simp
    rw [hzero, LinearMap.zero_apply, map_zero]
    exact zero_mem _
  · rw [map_zero, map_zero]
    exact zero_mem _

/-- The flag action factors through the red-dot and red-crossing relations. -/
noncomputable def allOrdersFlagRep (J : Seq weight → Ideal R) (hJ : PreservesFlags J) :
    StendhalAlgebraAllOrders k Q weights (Multiset.replicate 2 ()) →ₐ[k]
      Module.End k (PMod ⧸ flagRelations J) := by
  refine RingQuot.liftAlgHom k ⟨(flagQuotRep Q J hJ).comp (mk k _ _), ?_⟩
  intro u v h
  cases h with
  | klr h =>
    exact congrArg (flagQuotRep Q J hJ) (RingQuot.mkAlgHom_rel k h)
  | red_dot a s ha =>
    change flagQuotRep Q J hJ (mk k _ _ (fx k weight a * fe k weight s)) =
      flagQuotRep Q J hJ (mk k _ _ 0)
    rw [map_mul, map_zero, map_zero]
    exact flagQuotRep_red_dot Q J hJ a s ha
  | red_cross j hj s h₁ h₂ =>
    change flagQuotRep Q J hJ (mk k _ _ (fψ k weight j * fe k weight s)) =
      flagQuotRep Q J hJ (mk k _ _ 0)
    rw [map_mul, map_zero, map_zero]
    exact flagQuotRep_red_cross Q J hJ j hj s h₁ h₂

theorem allOrdersFlagRep_ofKLR (J : Seq weight → Ideal R) (hJ : PreservesFlags J)
    (a : A) :
    allOrdersFlagRep Q J hJ
      (StendhalAlgebraAllOrders.ofKLR k Q weights (Multiset.replicate 2 ()) a) =
      flagQuotRep Q J hJ a := by
  obtain ⟨u, rfl⟩ := mk_surjective a
  rw [StendhalAlgebraAllOrders.ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

end Categorification.Stendhal.LabelTwoEndpointFlag
