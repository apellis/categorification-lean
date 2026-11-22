/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftCurlL
import Categorification.Diagrams.KL3.SidewaysDotSlide

/-!
# The curl recursion for the shifted decomposition relation

Towards the decomposition relation of `E_i F_i` under the shift functor of
Webster arXiv:1309.3796v2, Proposition 3.30. An upward dot on the output strand of
`crossl_{ii}` slides to its input strand up to `cap ≫ cup` (`dg_crossl_dotE`), and the
morphisms `KLz c = crossl ≫ (F-dot)^c ≫ cap` of the localized category `U′` satisfy
`KLz (c + 1) = X ≫ KLz c + cap ≫ zccw c` (`KLz_succ`).
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- An upward dot on the upward output strand of `crossl_{ii}` slides down to its upward input
strand, up to the correction `cap ≫ cup`. -/
theorem dg_crossl_dotE (ν : X) (i : I) :
    dg RD k ν [up i, dn i] [dn i, up i] (crosslL i i ++ [([dn i], .dot (up i), [])]) =
      dg RD k ν [up i, dn i] [dn i, up i] (([], .dot (up i), [dn i]) :: crosslL i i) +
        dg RD k ν [up i, dn i] [dn i, up i] [([], .cap (dn i), []), ([], .cup (dn i), [])] := by
  simp only [crosslL, List.cons_append, List.nil_append]
  dswap 2
  rw [dg_stepL_at _ 1 [dn i] [dn i] (dg_slideLEq RD k _ i) (by (try dnorm); schain)
    (by (try dnorm); schain) (by dnorm)]
  rw [map_add, ctxL_dg RD k ν (by (try dnorm); schain) (by (try dnorm); schain),
    ctxL_dg RD k ν (by (try dnorm); schain) (by (try dnorm); schain)]
  dnorm
  congr 1
  · dswap 0
  · dswap 0

section KL

variable (lam : X) (i : I)

/-- `crossl_{ii}`, then `c` dots on the downward strand, then the cap `F_i E_i ⟶ 1`, in `U′`. -/
abbrev KLz (c : ℤ) : lob RD k lam [up i, dn i] ⟶ lob RD k lam [] :=
  ldg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) ≫ zdot RD k lam [] i [up i] c ≫
    ldg RD k lam [dn i, up i] [] [([], .cap (up i), [])]

/-- An upward dot on `E_i` in `E_i F_i`, in `U′`. -/
abbrev XEF : lob RD k lam [up i, dn i] ⟶ lob RD k lam [up i, dn i] :=
  ldg RD k lam [up i, dn i] [up i, dn i] [([], .dot (up i), [dn i])]

theorem KLz_succ (c : ℤ) :
    KLz RD k lam i (c + 1) = XEF RD k lam i ≫ KLz RD k lam i c +
      ldg RD k lam [up i, dn i] [] [([], .cap (dn i), [])] ≫
        zccw (RD := RD) (k := k) lam i c := by
  have F1 : zdot RD k lam [] i [up i] 1 ≫ ldg RD k lam [dn i, up i] [] [([], .cap (up i), [])] =
      ldg RD k lam [dn i, up i] [dn i, up i] [([dn i], .dot (up i), [])] ≫
        ldg RD k lam [dn i, up i] [] [([], .cap (up i), [])] := by
    rw [zdot_one, ldot, ← ldg_of]
    exact (ldg_comp RD k (A := [([], .dot (dn i), [up i])])
      (B := [([], .cap (up i), [])]) (by schain) (by schain)).trans
      ((congrArg (toLoc RD k).map (dg_dot_cap_up RD k lam i)).trans
        (ldg_comp RD k (A := [([dn i], .dot (up i), [])])
          (B := [([], .cap (up i), [])]) (by schain) (by schain)).symm)
  have F2 : zdot RD k lam [] i [up i] c ≫
      ldg RD k lam [dn i, up i] [dn i, up i] [([dn i], .dot (up i), [])] =
      ldg RD k lam [dn i, up i] [dn i, up i] [([dn i], .dot (up i), [])] ≫
        zdot RD k lam [] i [up i] c := by
    refine zdot_comp_of_one (RD := RD) (k := k) (A := []) (B := [up i])
      (A' := []) (B' := [up i]) lam _ ?_ c
    rw [zdot_one, ldot, ← ldg_of]
    exact (ldg_comp RD k (A := [([], .dot (dn i), [up i])])
      (B := [([dn i], .dot (up i), [])]) (by schain) (by schain)).trans
      ((congrArg (toLoc RD k).map
        (dg_swap RD k lam _ _ [] [] [] (.dot (dn i)) (.dot (up i)))).trans
        (ldg_comp RD k (A := [([dn i], .dot (up i), [])])
          (B := [([], .dot (dn i), [up i])]) (by schain) (by schain)).symm)
  have F3 : ldg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) ≫
      ldg RD k lam [dn i, up i] [dn i, up i] [([dn i], .dot (up i), [])] =
      XEF RD k lam i ≫ ldg RD k lam [up i, dn i] [dn i, up i] (crosslL i i) +
        ldg RD k lam [up i, dn i] [] [([], .cap (dn i), [])] ≫
          ldg RD k lam [] [dn i, up i] [([], .cup (dn i), [])] := by
    rw [ldg_comp RD k (by schain) (by schain), ldg_comp RD k (by schain) (by schain),
      ldg_comp RD k (by schain) (by schain), ldg, ldg, ← Functor.map_add]
    exact congrArg (toLoc RD k).map (dg_crossl_dotE RD k lam i)
  simp only [KLz, XEF, zccw]
  rw [add_comm, zdot_add, Category.assoc, F1, ← Category.assoc (zdot _ _ _ _ _ _ c), F2]
  simp only [Category.assoc]
  rw [← Category.assoc (ldg RD k lam [up i, dn i] [dn i, up i] (crosslL i i)), F3]
  simp only [Preadditive.add_comp, Category.assoc]

end KL

end Categorification.KL3.Diagram
