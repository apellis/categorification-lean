/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.StendhalPolyRep
import Categorification.WeightedKLR.RedStrands.BraidedViolatedQuotient

/-!
# Polynomial flags on the five-slot crossing

Webster, arXiv:1309.3796v2, Definition 6.3 and proof of Lemma 6.8 after (6.21).
Use the positional polynomial representation for three reds and two equal
blacks. The crossing of reds 2 and 1 acts by the variable transposition in
the exchanged direction. The remaining red/red crossings act by zero.
-/

namespace Categorification.Stendhal.FiveSlotFlag

open KLR KLRAlgebra KLR.PolyRep MvPolynomial TypeA Equiv

variable {k : Type*} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

abbrev weight := stendhalWeight 3 ({()} + {()} : Multiset Unit)
local notation "m" => Multiset.card weight
local notation "R" => MvPolynomial (Fin m) k

/-- The crossing parameters for the flag test, oriented from red order
`[0, 2, 1]` to `[0, 1, 2]`. -/
noncomputable def flagP : Unit ⊕ Fin 3 → Unit ⊕ Fin 3 → MvPolynomial (Fin 2) k
  | .inl _, .inl _ => 0
  | .inl i, .inr r => X 1 ^ Λ r i
  | .inr _, .inl _ => 1
  | .inr r, .inr d => if r = 2 ∧ d = 1 then 1 else 0

theorem flagP_factor : ∀ a b, a ≠ b →
    stendhalQ Q Λ a b = flagP Λ b a * rename ![1, 0] (flagP Λ a b) := by
  rintro (i | r) (j | d) h
  · exact (h (by cases i; cases j; rfl)).elim
  · simp [stendhalQ, flagP]
  · simp [stendhalQ, flagP]
  · fin_cases r <;> fin_cases d <;> simp [stendhalQ, flagP]

/-- Setting red variables to zero commutes with all flag crossings. -/
theorem blackEval_crossComp_flagP (s : Seq weight) (j : ℕ) (h : j + 1 < m) (f : R) :
    blackEval (sadj m j • s) (crossComp (flagP Λ) j h s f) =
      crossComp (flagP Λ) j h s (blackEval s f) := by
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
    cases ha : s.lbl ⟨j, by omega⟩ with
    | inl i =>
      cases hr : s.lbl ⟨j + 1, h⟩ with
      | inl _ => rw [flagP, map_zero, map_zero]
      | inr r =>
        rw [flagP, map_pow, rename_X]
        change blackEval (sadj m j • s) (X b ^ Λ r i) = X b ^ Λ r i
        rw [map_pow, blackEval_X, show (sadj m j • s).1 b = .inl i from hb.trans ha]
        rfl
    | inr r =>
      cases hr : s.lbl ⟨j + 1, h⟩ with
      | inl _ => rw [flagP, map_one, map_one]
      | inr r' =>
        rw [flagP]
        split_ifs <;> first | rw [map_one, map_one] | rw [map_zero, map_zero]

local notation "PMod" => KLR.PolyRep.Pol k weight
local notation "A" => KLRAlgebra k (stendhalQ Q Λ) weight
local notation "FRep" => polyRep (flagP_factor Q Λ)

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
    crossComp (flagP Λ) j h s p ∈ J (sadj m j • s)

theorem flagRelations_stable (J : Seq weight → Ideal R) (hJ : PreservesFlags Λ J)
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
      · rw [opΨ_apply (flagP Λ) j hj]
        have hs : sadj m j • (sadj m j • s) = s := sadj_smul_sadj_smul s j
        have h := blackEval_crossComp_flagP Λ (sadj m j • s) j hj (f (sadj m j • s))
        rw [hs] at h
        rw [h]
        simpa only [hs] using hJ _ j hj _ (hf (sadj m j • s))
      · rw [opΨ_eq_zero (flagP Λ) (j := j) (Nat.le_of_not_gt hj), LinearMap.zero_apply, Pi.zero_apply,
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
noncomputable def flagQuotRep (J : Seq weight → Ideal R) (hJ : PreservesFlags Λ J) :
    A →ₐ[k] Module.End k (PMod ⧸ flagRelations J) where
  toFun a := (flagRelations J).mapQ (flagRelations J) (FRep a)
    (fun f hf => flagRelations_stable Q Λ J hJ a f hf)
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
theorem flagQuotRep_eq_zero_eval (J : Seq weight → Ideal R) (hJ : PreservesFlags Λ J)
    {a : A} (ha : flagQuotRep Q Λ J hJ a = 0) (f : PMod) (s : Seq weight) :
    blackEval s (FRep a f s) ∈ J s := by
  have hz := congrArg (fun g : Module.End k (PMod ⧸ flagRelations J) =>
    g ((flagRelations J).mkQ f)) ha
  change Submodule.Quotient.mk (FRep a f) = 0 at hz
  exact ((Submodule.Quotient.mk_eq_zero _).1 hz) s

private theorem flagQuotRep_apply_mkQ (J : Seq weight → Ideal R) (hJ : PreservesFlags Λ J)
    (a : A) (f : PMod) :
    flagQuotRep Q Λ J hJ a ((flagRelations J).mkQ f) =
      (flagRelations J).mkQ (FRep a f) := rfl

private theorem flagQuotRep_red_dot (J : Seq weight → Ideal R) (hJ : PreservesFlags Λ J)
    (a : Fin m) (s : Seq weight) (ha : (s.lbl a).isRight) :
    flagQuotRep Q Λ J hJ (x a * e s) = 0 := by
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

/-- The flag action descends to braided Stendhal diagrams. -/
noncomputable def braidedFlagRep (J : Seq weight → Ideal R) (hJ : PreservesFlags Λ J) :
    BraidedStendhalAlgebra k Q Λ ({()} + {()} : Multiset Unit) →ₐ[k]
      Module.End k (PMod ⧸ flagRelations J) := by
  refine RingQuot.liftAlgHom k ⟨(flagQuotRep Q Λ J hJ).comp (mk k _ _), ?_⟩
  intro u v h
  cases h with
  | klr h =>
    exact congrArg (flagQuotRep Q Λ J hJ) (RingQuot.mkAlgHom_rel k h)
  | red_dot a s ha =>
    change flagQuotRep Q Λ J hJ (mk k _ _ (fx k weight a * fe k weight s)) =
      flagQuotRep Q Λ J hJ (mk k _ _ 0)
    rw [map_mul, map_zero, map_zero]
    exact flagQuotRep_red_dot Q Λ J hJ a s ha

theorem braidedFlagRep_ofKLR (J : Seq weight → Ideal R) (hJ : PreservesFlags Λ J)
    (a : A) :
    braidedFlagRep Q Λ J hJ
      (BraidedStendhalAlgebra.ofKLR k Q Λ ({()} + {()} : Multiset Unit) a) =
      flagQuotRep Q Λ J hJ a := by
  obtain ⟨u, rfl⟩ := mk_surjective a
  rw [BraidedStendhalAlgebra.ofKLR_mk]
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

private theorem flagQuotRep_violated_idem (J : Seq weight → Ideal R) (hJ : PreservesFlags Λ J)
    (s : Seq weight) (h : J s = ⊤) :
    flagQuotRep Q Λ J hJ (e s) = 0 := by
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

/-- The flag representation in the violated quotient. The zero flag
quotients at violated loadings are supplied by the ideal family. -/
noncomputable def violatedFlagRep (J : Seq weight → Ideal R)
    (hJ : PreservesFlags Λ J) (hV : ∀ s, IsViolated s → J s = ⊤) :
    BraidedStendhalAlgebra.ViolQuotient k Q Λ ({()} + {()} : Multiset Unit) →ₐ[k]
      Module.End k (PMod ⧸ flagRelations J) :=
  (BraidedStendhalAlgebra.violIdeal k Q Λ ({()} + {()} : Multiset Unit)).ringCon.liftₐ
    (braidedFlagRep Q Λ J hJ) (by
      apply (TwoSidedIdeal.ringCon_le_iff
        (J := TwoSidedIdeal.ker (braidedFlagRep Q Λ J hJ).toRingHom)).mp
      apply TwoSidedIdeal.span_le.mpr
      rintro _ ⟨s, hs, rfl⟩
      apply (TwoSidedIdeal.mem_ker _).2
      change braidedFlagRep Q Λ J hJ
        (BraidedStendhalAlgebra.ofKLR k Q Λ ({()} + {()} : Multiset Unit) (e s)) = 0
      rw [braidedFlagRep_ofKLR]
      exact flagQuotRep_violated_idem Q Λ J hJ s (hV s hs))

/-- A raw diagram vanishing in the violated quotient has every polynomial
test in the prescribed flag ideal at its output loading. -/
theorem eval_mem_flag_of_violMk_eq_zero (J : Seq weight → Ideal R)
    (hJ : PreservesFlags Λ J) (hV : ∀ s, IsViolated s → J s = ⊤)
    {a : A} (ha : BraidedStendhalAlgebra.violMk k Q Λ ({()} + {()} : Multiset Unit)
      (BraidedStendhalAlgebra.ofKLR k Q Λ ({()} + {()} : Multiset Unit) a) = 0)
    (f : PMod) (s : Seq weight) : blackEval s (FRep a f s) ∈ J s := by
  have hz := congrArg (violatedFlagRep Q Λ J hJ hV) ha
  rw [map_zero] at hz
  have hq (x : BraidedStendhalAlgebra k Q Λ ({()} + {()} : Multiset Unit)) :
      violatedFlagRep Q Λ J hJ hV
        (BraidedStendhalAlgebra.violMk k Q Λ ({()} + {()} : Multiset Unit) x) =
      braidedFlagRep Q Λ J hJ x := RingCon.liftₐ_mk _ _ _ _
  rw [hq, braidedFlagRep_ofKLR] at hz
  exact flagQuotRep_eq_zero_eval Q Λ J hJ hz f s

end Categorification.Stendhal.FiveSlotFlag
