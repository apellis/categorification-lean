/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftCurlCapFE

/-!
# The decomposition of `1_{F_i E_i}` with extra dots in `U′` (Webster Prop. 3.30)

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. Under the weight shift, the decomposition relation of `1_{F_i E_i 1_λ}`
(KL III Definition 3.1, `dg_decompFE`) is sent to a version with `c` extra dots on the
downward strand. This file proves that version in `U′`: `Wz_eq_Sz` states that `c` dots on
`F_i` in `F_i E_i` equal `-(crossr ≫ (c dots) ≫ crossl) + decompSumFE c`, for every `c ∈ ℤ`.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

section DecompFE

variable (lam : X) (i : I)

/-- The bubble terms of the decomposition of `1_{F E}` with `c` extra dots, in `U`. -/
def decompSumFE (c : ℤ) : End ((pres RD k).obj (ob RD lam [dn i, up i])) :=
  ∑ f ∈ Finset.range (-ip RD i lam + c).toNat, ∑ g ∈ Finset.range (f + 1),
    dg RD k lam [dn i, up i] [] (dotCapFELs i (f - g)) ≫
      cwU RD k lam i (ip RD i lam - 1 + g) ≫
      dg RD k lam [] [dn i, up i] (cupDotFELs i ((-ip RD i lam + c).toNat - 1 - f))

theorem cupDotFE_succ (m : ℕ) :
    dg RD k lam [] [dn i, up i] (cupDotFELs i m) ≫
        dg RD k lam [dn i, up i] [dn i, up i] [([], .dot (dn i), [up i])] =
      dg RD k lam [] [dn i, up i] (cupDotFELs i (m + 1)) := by
  have h1 : dg RD k lam [dn i, up i] [dn i, up i]
      (List.replicate m ([dn i], .dot (up i), []) ++ [([], .dot (dn i), [up i])]) =
      dg RD k lam [dn i, up i] [dn i, up i]
        ([([], .dot (dn i), [up i])] ++ List.replicate m ([dn i], .dot (up i), [])) := by
    simpa using dg_swap_dots RD k lam [] [] [] (dn i) (up i) m 1
  calc dg RD k lam [] [dn i, up i] (cupDotFELs i m) ≫
        dg RD k lam [dn i, up i] [dn i, up i] [([], .dot (dn i), [up i])]
      = dg RD k lam [] [dn i, up i] [([], .cup (dn i), [])] ≫
          dg RD k lam [dn i, up i] [dn i, up i]
            (List.replicate m ([dn i], .dot (up i), []) ++ [([], .dot (dn i), [up i])]) := by
        rw [dg_comp (by schain) (by schain), dg_comp (by schain) (by schain)]
        simp only [cupDotFELs, List.append_assoc]
    _ = dg RD k lam [] [dn i, up i] [([], .cup (dn i), [])] ≫
          dg RD k lam [dn i, up i] [dn i, up i] [([], .dot (dn i), [up i])] ≫
            dg RD k lam [dn i, up i] [dn i, up i]
              (List.replicate m ([dn i], .dot (up i), [])) := by
        rw [h1, ← dg_comp (A := [([], .dot (dn i), [up i])])
          (B := List.replicate m ([dn i], .dot (up i), [])) (by schain) (by schain)]
        rfl
    _ = dg RD k lam [] [dn i, up i] [([], .cup (dn i), []), ([dn i], .dot (up i), [])] ≫
            dg RD k lam [dn i, up i] [dn i, up i]
              (List.replicate m ([dn i], .dot (up i), [])) := by
        rw [← Category.assoc, dg_comp (by schain) (by schain), dg_dot_cupDn]
        rfl
    _ = _ := by
        rw [dg_comp (by schain) (by schain)]
        simp only [cupDotFELs, List.replicate_succ, List.cons_append, List.nil_append]

theorem decompSumFE_succ (c : ℤ) :
    decompSumFE RD k lam i (c + 1) =
      -(curlCapFE RD k i lam c ≫ dg RD k lam [] [dn i, up i] [([], .cup (dn i), [])]) +
        decompSumFE RD k lam i c ≫
          dg RD k lam [dn i, up i] [dn i, up i] [([], .dot (dn i), [up i])] := by
  unfold decompSumFE curlCapFE
  rw [Preadditive.neg_comp, neg_neg]
  rcases lt_or_ge (-ip RD i lam + c) 0 with h | h
  · have h1 : (-ip RD i lam + (c + 1)).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have h2 : (-ip RD i lam + c).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have h3 : (-ip RD i lam + 1 + c).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    rw [h1, h2, h3]
    simp
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, -ip RD i lam + c = N :=
      ⟨_, (Int.toNat_of_nonneg (by omega)).symm⟩
    have h1 : (-ip RD i lam + (c + 1)).toNat = N + 1 := by omega
    have h2 : (-ip RD i lam + c).toNat = N := by omega
    have h3 : (-ip RD i lam + 1 + c).toNat = N + 1 := by omega
    rw [h1, h2, h3, Finset.sum_range_succ, add_comm, Preadditive.sum_comp]
    congr 1
    · refine Finset.sum_congr rfl fun g hg => ?_
      have hg' := Finset.mem_range.mp hg
      have e : (-ip RD i lam + c - g).toNat = N - g := by omega
      rw [e, Nat.add_sub_cancel, Nat.sub_self]
      simp only [Category.assoc]
      rfl
    · rw [Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun f hf => ?_
      have hf' := Finset.mem_range.mp hf
      rw [Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun g _ => ?_
      have e : N + 1 - 1 - f = N - 1 - f + 1 := by omega
      rw [e, Category.assoc, Category.assoc, cupDotFE_succ]

/-- `c` downward dots on `F_i` in `F_i E_i`, in `U′`. -/
abbrev Wz (c : ℤ) : lob RD k lam [dn i, up i] ⟶ lob RD k lam [dn i, up i] :=
  zdot RD k lam [] i [up i] c

/-- The right side of the decomposition of `1_{F_i E_i}` with `c` extra dots, in `U′`. -/
abbrev Sz (c : ℤ) : lob RD k lam [dn i, up i] ⟶ lob RD k lam [dn i, up i] :=
  -(ldg RD k lam [dn i, up i] [up i, dn i] (crossrL i i) ≫ Yz RD k lam i c ≫
      ldg RD k lam [up i, dn i] [dn i, up i] (crosslL i i)) +
    (show lob RD k lam [dn i, up i] ⟶ lob RD k lam [dn i, up i] from
      (toLoc RD k).map (decompSumFE RD k lam i c))

theorem Wz_one : Wz RD k lam i 1 =
    ldg RD k lam [dn i, up i] [dn i, up i] [([], .dot (dn i), [up i])] := by
  rw [Wz, zdot_one, ldot, ← ldg_of]
  rfl

theorem Yz_one_crossl :
    Yz RD k lam i 1 ≫ ldg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) =
      ldg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) ≫ Wz RD k lam i 1 -
        ldg RD k lam [up i, dn i] [] [([], .cap (dn i), [])] ≫
          ldg RD k lam [] [dn i, up i] [([], .cup (dn i), [])] := by
  rw [Wz_one, Yz_one]
  rw [ldg_comp RD k (by schain) (by schain),
    ldg_comp RD k (by schain) (by schain), ldg_comp RD k (by schain) (by schain), ldg, ldg,
    ← Functor.map_sub]
  exact congrArg (toLoc RD k).map (dg_dot_crossl_self RD k lam i)

theorem Sz_succ (c : ℤ) : Sz RD k lam i (c + 1) = Sz RD k lam i c ≫ Wz RD k lam i 1 := by
  have hcup : (toLoc RD k).map (dg RD k lam [] [dn i, up i] [([], .cup (dn i), [])]) =
      ldg RD k lam [] [dn i, up i] [([], .cup (dn i), [])] := rfl
  have hW : (toLoc RD k).map
      (dg RD k lam [dn i, up i] [dn i, up i] [([], .dot (dn i), [up i])]) =
      Wz RD k lam i 1 := (Wz_one RD k lam i).symm
  simp only [Sz]
  rw [decompSumFE_succ, (toLoc RD k).map_add, (toLoc RD k).map_neg, (toLoc RD k).map_comp,
    (toLoc RD k).map_comp, hcup, hW, ← KLzR_eq, Yz, add_comm c 1, zdot_add, ← Yz, ← Yz,
    Category.assoc, Yz_one_crossl]
  simp only [KLzR, Preadditive.add_comp, Preadditive.comp_sub, Category.assoc,
    Preadditive.neg_comp]
  abel

theorem Wz_eq_Sz (c : ℤ) : Wz RD k lam i c = Sz RD k lam i c := by
  induction c using Int.induction_on with
  | zero =>
    rw [Wz, zdot_zero, Sz, Yz, zdot_zero]
    erw [Category.id_comp]
    rw [ldg_comp RD k (by schain) (by schain)]
    have key := congrArg (toLoc RD k).map (dg_decompFE RD k i lam)
    rw [(toLoc RD k).map_add, (toLoc RD k).map_neg] at key
    refine (ldg_nil RD k lam [dn i, up i]).symm.trans (key.trans ?_)
    simp only [decompSumFE, add_zero]
  | succ n ih =>
    rw [Sz_succ, ← ih, Wz, Wz, ← zdot_add, add_comm]
  | pred n ih =>
    have e1 := Sz_succ RD k lam i (-(n : ℤ) - 1)
    rw [show -(n : ℤ) - 1 + 1 = -n by ring, ← ih] at e1
    have e2 : Wz RD k lam i (-n) = Wz RD k lam i (-(n : ℤ) - 1) ≫ Wz RD k lam i 1 := by
      rw [Wz, Wz, Wz, ← zdot_add]; congr 1; ring
    have hM : Mono (Wz RD k lam i 1) := by
      rw [Wz_one]; unfold ldg
      exact @IsIso.mono_of_iso _ _ _ _ _ (isIso_toLoc_dg_dot RD k lam [] (dn i) [up i])
    exact (cancel_mono (Wz RD k lam i 1)).mp (e2.symm.trans e1)

end DecompFE

end Categorification.KL3.Diagram
