/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftCurlCap
import Categorification.Diagrams.KL3.SidewaysDotSlide

/-!
# The decomposition of `1_{E_i F_i}` with extra dots in `U′` (Webster Prop. 3.30)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. Under the weight shift, the decomposition relation of `1_{E_i F_i 1_λ}`
(KL III Definition 3.1, `dg_decompEF`) is sent to a version with `c` extra dots on the
downward strand of the sideways crossings. This file proves that version in `U′`:
`Yz_eq_Rz` states that `c` dots on `F_i` in `E_i F_i` equal
`-(crossl ≫ (c dots) ≫ crossr) + decompSumEF c`, for every `c ∈ ℤ`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

section DecompEF

variable (lam : X) (i : I)

/-- The bubble terms of the decomposition of `1_{E F}` with `c` extra dots, in `U`. -/
def decompSumEF (c : ℤ) : End ((pres RD k).obj (ob RD lam [up i, dn i])) :=
  ∑ f ∈ Finset.range (ip RD i lam + c).toNat, ∑ g ∈ Finset.range (f + 1),
    dg RD k lam [up i, dn i] [] (dotCapEFLs i (f - g)) ≫
      ccwU RD k lam i (-ip RD i lam - 1 + g) ≫
      dg RD k lam [] [up i, dn i] (cupDotEFLs i ((ip RD i lam + c).toNat - 1 - f))

theorem cupDotEF_succ (m : ℕ) :
    dg RD k lam [] [up i, dn i] (cupDotEFLs i m) ≫
        dg RD k lam [up i, dn i] [up i, dn i] [([up i], .dot (dn i), [])] =
      dg RD k lam [] [up i, dn i] (cupDotEFLs i (m + 1)) := by
  rw [dg_comp (by schain) (by schain)]
  simp only [cupDotEFLs, List.replicate_succ', List.append_assoc]

theorem decompSumEF_succ (c : ℤ) :
    decompSumEF RD k lam i (c + 1) =
      curlCapU RD k i lam c ≫ dg RD k lam [] [up i, dn i] [([], .cup (up i), [])] +
        decompSumEF RD k lam i c ≫
          dg RD k lam [up i, dn i] [up i, dn i] [([up i], .dot (dn i), [])] := by
  unfold decompSumEF curlCapU
  rcases lt_or_ge (ip RD i lam + c) 0 with h | h
  · have h1 : (ip RD i lam + (c + 1)).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have h2 : (ip RD i lam + c).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have h3 : (ip RD i lam + 1 + c).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    rw [h1, h2, h3]
    simp
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, ip RD i lam + c = N :=
      ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    have h1 : (ip RD i lam + (c + 1)).toNat = N + 1 := by omega
    have h2 : (ip RD i lam + c).toNat = N := by omega
    have h3 : (ip RD i lam + 1 + c).toNat = N + 1 := by omega
    rw [h1, h2, h3, Finset.sum_range_succ, add_comm, Preadditive.sum_comp]
    congr 1
    · refine Finset.sum_congr rfl fun g hg => ?_
      have hg' := Finset.mem_range.mp hg
      have e : (ip RD i lam + c - g).toNat = N - g := by omega
      rw [e, Nat.add_sub_cancel, Nat.sub_self]
      simp only [Category.assoc]
      rfl
    · rw [Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun f hf => ?_
      have hf' := Finset.mem_range.mp hf
      rw [Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun g _ => ?_
      have e : N + 1 - 1 - f = N - 1 - f + 1 := by omega
      rw [e, Category.assoc, Category.assoc, cupDotEF_succ]

/-- `c` downward dots on `F_i` in `E_i F_i`, in `U′`. -/
abbrev Yz (c : ℤ) : lob RD k lam [up i, dn i] ⟶ lob RD k lam [up i, dn i] :=
  zdot RD k lam [up i] i [] c

/-- The right side of the decomposition of `1_{E_i F_i}` with `c` extra dots, in `U′`. -/
abbrev Rz (c : ℤ) : lob RD k lam [up i, dn i] ⟶ lob RD k lam [up i, dn i] :=
  -(ldg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) ≫ zdot RD k lam [] i [up i] c ≫
      ldg RD k lam [dn i, up i] [up i, dn i] (crossrL i i)) +
    (show lob RD k lam [up i, dn i] ⟶ lob RD k lam [up i, dn i] from
      (toLoc RD k).map (decompSumEF RD k lam i c))

theorem Yz_one : Yz RD k lam i 1 =
    ldg RD k lam [up i, dn i] [up i, dn i] [([up i], .dot (dn i), [])] := by
  rw [Yz, zdot_one, ldot, ← ldg_of]
  rfl

theorem Zz_one_crossr :
    zdot RD k lam [] i [up i] 1 ≫ ldg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) =
      ldg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫ Yz RD k lam i 1 +
        ldg RD k lam [dn i, up i] [] [([], .cap (up i), [])] ≫
          ldg RD k lam [] [up i, dn i] [([], .cup (up i), [])] := by
  rw [Yz_one, zdot_one, ldot, ← ldg_of]
  show ldg RD k lam [dn i, up i] [dn i, up i] [([], .dot (dn i), [up i])] ≫ _ = _
  rw [ldg_comp RD k (by schain) (by schain),
    ldg_comp RD k (by schain) (by schain), ldg_comp RD k (by schain) (by schain), ldg, ldg,
    ← Functor.map_add]
  exact congrArg (toLoc RD k).map (dg_dot_crossr_self RD k lam i)

theorem Rz_succ (c : ℤ) : Rz RD k lam i (c + 1) = Rz RD k lam i c ≫ Yz RD k lam i 1 := by
  have hcup : (toLoc RD k).map (dg RD k lam [] [up i, dn i] [([], .cup (up i), [])]) =
      ldg RD k lam [] [up i, dn i] [([], .cup (up i), [])] := rfl
  have hY : (toLoc RD k).map
      (dg RD k lam [up i, dn i] [up i, dn i] [([up i], .dot (dn i), [])]) =
      Yz RD k lam i 1 := (Yz_one RD k lam i).symm
  simp only [Rz]
  rw [decompSumEF_succ, (toLoc RD k).map_add, (toLoc RD k).map_comp, (toLoc RD k).map_comp,
    hcup, hY, ← KLz_eq, add_comm c 1, zdot_add, Category.assoc, Zz_one_crossr]
  simp only [KLz, Preadditive.comp_add, Preadditive.add_comp, Category.assoc, neg_add,
    Preadditive.neg_comp]
  abel

theorem Yz_eq_Rz (c : ℤ) : Yz RD k lam i c = Rz RD k lam i c := by
  induction c using Int.induction_on with
  | zero =>
    rw [Yz, zdot_zero, Rz, zdot_zero]
    erw [Category.id_comp]
    rw [ldg_comp RD k (by schain) (by schain)]
    have key := congrArg (toLoc RD k).map (dg_decompEF RD k i lam)
    rw [(toLoc RD k).map_add, (toLoc RD k).map_neg] at key
    refine (ldg_nil RD k lam [up i, dn i]).symm.trans (key.trans ?_)
    simp only [decompSumEF, add_zero]
  | succ n ih =>
    rw [Rz_succ, ← ih, Yz, Yz, ← zdot_add, add_comm]
  | pred n ih =>
    have e1 := Rz_succ RD k lam i (-(n : ℤ) - 1)
    rw [show -(n : ℤ) - 1 + 1 = -n by ring, ← ih] at e1
    have e2 : Yz RD k lam i (-n) = Yz RD k lam i (-(n : ℤ) - 1) ≫ Yz RD k lam i 1 := by
      rw [Yz, Yz, Yz, ← zdot_add]; congr 1; ring
    have hM : Mono (Yz RD k lam i 1) := by
      rw [Yz_one]; unfold ldg
      exact @IsIso.mono_of_iso _ _ _ _ _ (isIso_toLoc_dg_dot RD k lam [up i] (dn i) [])
    exact (cancel_mono (Yz RD k lam i 1)).mp (e2.symm.trans e1)

end DecompEF

end Categorification.KL3.Diagram
