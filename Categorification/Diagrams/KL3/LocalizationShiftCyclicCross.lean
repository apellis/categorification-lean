/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftCyclic
import Categorification.Diagrams.KL3.LocalizationDotsDown

/-!
# The crossing cyclicity relations under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. The images of the cyclicity relations for crossings (KL III
`eq_cyclic_cross-gen`, `cycCrossR` and `cycCrossL`) under the weight shift
`shiftFree RD k δ a b` vanish (`shift_rel_cycCrossR`, `shift_rel_cycCrossL`).

The inverse dots inserted at the two cups and the two caps slide along the rotated strands to
the four ends of the downward crossing (`zg_cycCrossR`, `zg_cycCrossL`); the rotated crossing
is then replaced by the downward crossing (`dg_cycCrossR`, `dg_cycCrossL`), and the resulting
conjugate of the downward crossing by dot powers on its two strands is the crossing itself
(`zg_crossConj`). For distinct colours the dots slide through the crossing
(`dg_slideRNe_dn`, `dg_slideLNe_dn`); for equal colours the exponents agree, and the product
of the two dots commutes with the crossing (`dnDotPair_lcross`, from the nilHecke relations
`dg_slideREq_dn`, `dg_slideLEq_dn`).
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

theorem ldg_single_dot (ν : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    ldg RD k ν (u ++ [dn i] ++ v) (u ++ [dn i] ++ v) [(u, .dot (dn i), v)] =
      zdot RD k ν u i v 1 := by
  rw [zdot_one]; exact ldg_of RD k (sChain_single (u, .dot (dn i), v))

/-- The downward crossing `F_j F_i ⟶ F_i F_j` in `U′`. -/
abbrev lcross (ν : X) (j i : I) : lob RD k ν [dn j, dn i] ⟶ lob RD k ν [dn i, dn j] :=
  ldg RD k ν [dn j, dn i] [dn i, dn j] [([], .cross false j i, [])]

theorem zg_five (ν : X) (j i : I) (p q r s : ℤ) :
    zg RD k ν [dn j, dn i] [dn i, dn j] [.dot [dn j] i [] p, .dot [] j [dn i] q,
      .lay ([], .cross false j i, []), .dot [dn i] j [] r, .dot [] i [dn j] s] =
      zdot RD k ν [dn j] i [] p ≫ zdot RD k ν [] j [dn i] q ≫ lcross ν j i ≫
        zdot RD k ν [dn i] j [] r ≫ zdot RD k ν [] i [dn j] s := by
  erw [zg_cons_self ν _ (DStep.dot [dn j] i [] p), zg_cons_self ν _ (DStep.dot [] j [dn i] q),
    zg_cons_self ν _ (DStep.lay ([], .cross false j i, [])),
    zg_cons_self ν _ (DStep.dot [dn i] j [] r), zg_cons_self ν _ (DStep.dot [] i [dn j] s)]
  erw [zg_nil, Category.comp_id]
  rfl

theorem zg_lcross (ν : X) (j i : I) :
    zg RD k ν [dn j, dn i] [dn i, dn j] [.lay ([], .cross false j i, [])] = lcross ν j i := by
  erw [zg_cons_self ν _ (DStep.lay ([], .cross false j i, [])), zg_nil, Category.comp_id]
  rfl

theorem ldg_pair (ν : X) {s t r : List (Letter I)} (x y : LayerData I) (hx : SChain s [x] t)
    (hy : SChain t [y] r) :
    ldg RD k ν s t [x] ≫ ldg RD k ν t r [y] = ldg RD k ν s r [x, y] :=
  ldg_comp RD k hx hy

variable [DecidableEq I] in
theorem ldg_dot_lcross_ne (ν : X) (j i : I) (h : j ≠ i) (n : ℤ) :
    zdot RD k ν [] j [dn i] n ≫ lcross ν j i = lcross ν j i ≫ zdot RD k ν [dn i] j [] n := by
  refine zdot_comp_of_one (RD := RD) (k := k) (A := []) (B := [dn i]) (A' := [dn i])
    (B' := []) ν (lcross ν j i) ?_ n
  rw [← ldg_single_dot, ← ldg_single_dot]
  refine (ldg_pair ν _ _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)).trans
    (((congrArg (toLoc RD k).map (dg_slideRNe_dn RD k ν j i h))).trans
      (ldg_pair ν _ _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)).symm)

variable [DecidableEq I] in
theorem ldg_dot_lcross_ne' (ν : X) (j i : I) (h : j ≠ i) (n : ℤ) :
    zdot RD k ν [dn j] i [] n ≫ lcross ν j i = lcross ν j i ≫ zdot RD k ν [] i [dn j] n := by
  refine zdot_comp_of_one (RD := RD) (k := k) (A := [dn j]) (B := []) (A' := [])
    (B' := [dn j]) ν (lcross ν j i) ?_ n
  rw [← ldg_single_dot, ← ldg_single_dot]
  refine (ldg_pair ν _ _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)).trans
    (((congrArg (toLoc RD k).map (dg_slideLNe_dn RD k ν j i h))).symm.trans
      (ldg_pair ν _ _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)).symm)

section Equal

variable (ν : X) (c : I)

theorem dotUnit_val (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    (dotUnit RD k ν u i v).val = zdot RD k ν u i v 1 :=
  (zdot_one RD k ν u i v).symm

variable [DecidableEq I] in
theorem lcross_slideR_eq :
    zdot RD k ν [] c [dn c] 1 ≫ lcross ν c c =
      lcross ν c c ≫ zdot RD k ν [dn c] c [] 1 - 𝟙 _ := by
  rw [← ldg_single_dot, ← ldg_single_dot]
  refine (ldg_pair ν _ _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)).trans
    ((congrArg (toLoc RD k).map (dg_slideREq_dn RD k ν c)).trans ?_)
  rw [Functor.map_sub, dg_nil, CategoryTheory.Functor.map_id]
  exact congrArg (· - 𝟙 _) (ldg_pair ν _ _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)).symm

variable [DecidableEq I] in
theorem lcross_slideL_eq :
    lcross ν c c ≫ zdot RD k ν [] c [dn c] 1 =
      zdot RD k ν [dn c] c [] 1 ≫ lcross ν c c - 𝟙 _ := by
  rw [← ldg_single_dot, ← ldg_single_dot]
  refine (ldg_pair ν _ _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)).trans
    ((congrArg (toLoc RD k).map (dg_slideLEq_dn RD k ν c)).trans ?_)
  rw [Functor.map_sub, dg_nil, CategoryTheory.Functor.map_id]
  exact congrArg (· - 𝟙 _) (ldg_pair ν _ _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)).symm

theorem zdot_comm_two :
    zdot RD k ν [] c [dn c] 1 ≫ zdot RD k ν [dn c] c [] 1 =
      zdot RD k ν [dn c] c [] 1 ≫ zdot RD k ν [] c [dn c] 1 := by
  rw [← ldg_single_dot, ← ldg_single_dot]
  refine (ldg_pair ν _ _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)).trans
    (((congrArg (toLoc RD k).map
      (dg_swap RD k ν [dn c, dn c] [dn c, dn c] [] [] [] (.dot (dn c)) (.dot (dn c))))).trans
      (ldg_pair ν _ _ (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩)).symm)

/-- The product of the two dots on `F_c F_c`, as a unit. -/
abbrev dnDotPair : (End (lob RD k ν [dn c, dn c]))ˣ :=
  @HMul.hMul (End (lob RD k ν [dn c, dn c]))ˣ (End (lob RD k ν [dn c, dn c]))ˣ _ _
    (dotUnit RD k ν [] c [dn c]) (dotUnit RD k ν [dn c] c [])

theorem dnDotPair_comm :
    Commute (S := (End (lob RD k ν [dn c, dn c]))ˣ) (dotUnit RD k ν [] c [dn c])
      (dotUnit RD k ν [dn c] c []) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, End.mul_def, End.mul_def, dotUnit_val, dotUnit_val]
  exact (zdot_comm_two ν c).symm

variable [DecidableEq I] in
theorem dnDotPair_lcross :
    (dnDotPair (RD := RD) (k := k) ν c).val ≫ lcross ν c c =
      lcross ν c c ≫ (dnDotPair (RD := RD) (k := k) ν c).val := by
  rw [Units.val_mul, End.mul_def, dotUnit_val, dotUnit_val]
  have hL' : zdot RD k ν [dn c] c [] 1 ≫ lcross ν c c =
      lcross ν c c ≫ zdot RD k ν [] c [dn c] 1 + 𝟙 _ := by
    exact (eq_sub_iff_add_eq.mp (lcross_slideL_eq ν c)).symm
  rw [Category.assoc, lcross_slideR_eq, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, hL', Preadditive.add_comp, Category.id_comp, add_sub_cancel_right,
    Category.assoc, zdot_comm_two]

theorem dnDotPair_zpow (n : ℤ) :
    ((dnDotPair (RD := RD) (k := k) ν c) ^ n).val =
      zdot RD k ν [dn c] c [] n ≫ zdot RD k ν [] c [dn c] n := by
  rw [(dnDotPair_comm ν c).mul_zpow, Units.val_mul, End.mul_def]
  rfl

end Equal

theorem units_zpow_comp_neg {𝒞 : Type*} [Category 𝒞] {p : 𝒞} (U : (End p)ˣ) (n : ℤ) :
    (U ^ n).val ≫ (U ^ (-n)).val = 𝟙 _ := by
  rw [← End.mul_def, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]
  rfl

variable [DecidableEq I] in
/-- Conjugating the downward crossing by dot powers on its two strands. -/
theorem zg_crossConj (ν : X) (j i : I) (p q : ℤ) (h : i = j → p = q) :
    zg RD k ν [dn j, dn i] [dn i, dn j] [.dot [dn j] i [] p, .dot [] j [dn i] q,
      .lay ([], .cross false j i, []), .dot [dn i] j [] (-q), .dot [] i [dn j] (-p)] =
      zg RD k ν [dn j, dn i] [dn i, dn j] [.lay ([], .cross false j i, [])] := by
  rw [zg_five, zg_lcross]
  by_cases hij : i = j
  · subst hij
    obtain rfl := h rfl
    rw [← Category.assoc, ← dnDotPair_zpow ν i p, ← dnDotPair_zpow ν i (-p),
      ← Category.assoc,
      units_val_zpow_comp _ _ _ (dnDotPair_lcross ν i) p, Category.assoc, units_zpow_comp_neg,
      Category.comp_id]
  · rw [← Category.assoc (zdot RD k ν [] j [dn i] q), ldg_dot_lcross_ne ν j i (Ne.symm hij),
      Category.assoc, ← Category.assoc (zdot RD k ν [dn i] j [] q), zdot_neg_add_cancel,
      Category.id_comp, ← Category.assoc (zdot RD k ν [dn j] i [] p),
      ldg_dot_lcross_ne' ν j i (Ne.symm hij), Category.assoc, zdot_neg_add_cancel]
    exact Category.comp_id _

/-- Proves a goal `DChain s L t` for explicit lists by unfolding it step by step. -/
syntax "dchain" : tactic
macro_rules | `(tactic| dchain) => `(tactic| first | exact rfl | (refine ⟨rfl, ?_⟩; dchain))

variable (a b : I → ℤ)

variable [DecidableEq I] in
/-- The image of `rotCrossR` under the weight shift is the image of the downward crossing. -/
theorem zg_cycCrossR (ν : X) (j i : I) :
    zg RD k ν [dn j, dn i] [dn i, dn j]
      ([([dn j, dn i], .cup (up j), []), ([dn j, dn i, up j], .cup (up i), [dn j]),
        ([dn j, dn i], .cross true j i, [dn i, dn j]), ([dn j], .cap (up i), [up j, dn i, dn j]),
        ([], .cap (up j), [dn i, dn j])].flatMap (layStep a b)) =
      zg RD k ν [dn j, dn i] [dn i, dn j]
        ([([], .cross false j i, [])].flatMap (layStep a b)) := by
  -- move the dot inserted at the inner cap to the bottom of the left strand
  have e1 := (zg_slideL (RD := RD) (k := k) ν [dn j] [] [dn i, dn j] (.cross true j i) i
    (a i)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.lay ([dn j, dn i], .cup (up j), []), .dot [dn j, dn i, up j] j [] (-a j),
      .lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .dot [dn j, dn i, up j, up i] i [dn j] (-a i)])
    [.lay ([dn j], .cap (up i), [up j, dn i, dn j]), .dot [] j [up j, dn i, dn j] (a j),
      .lay ([], .cap (up j), [dn i, dn j])] e1 (by dchain) (by dchain) (by dchain)).trans ?_
  have e2 := (zg_dotComm (RD := RD) (k := k) ν [dn j] [up j, up i] [dn j] i i (a i)
    (-a i)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.lay ([dn j, dn i], .cup (up j), []), .dot [dn j, dn i, up j] j [] (-a j),
      .lay ([dn j, dn i, up j], .cup (up i), [dn j])])
    [.lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j]), .dot [] j [up j, dn i, dn j] (a j),
      .lay ([], .cap (up j), [dn i, dn j])] e2 (by dchain) (by dchain) (by dchain)).trans ?_
  have e3 := (zg_slideL (RD := RD) (k := k) ν [dn j] [up j] [dn j] (.cup (up i)) i (a i)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.lay ([dn j, dn i], .cup (up j), []), .dot [dn j, dn i, up j] j [] (-a j)])
    [.dot [dn j, dn i, up j, up i] i [dn j] (-a i),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j]), .dot [] j [up j, dn i, dn j] (a j),
      .lay ([], .cap (up j), [dn i, dn j])] e3 (by dchain) (by dchain) (by dchain)).trans ?_
  have e4 := (zg_dotComm (RD := RD) (k := k) ν [dn j] [up j] [] i j (a i) (-a j)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.lay ([dn j, dn i], .cup (up j), [])])
    [.lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .dot [dn j, dn i, up j, up i] i [dn j] (-a i),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j]), .dot [] j [up j, dn i, dn j] (a j),
      .lay ([], .cap (up j), [dn i, dn j])] e4 (by dchain) (by dchain) (by dchain)).trans ?_
  have e5 := (zg_slideL (RD := RD) (k := k) ν [dn j] [] [] (.cup (up j)) i (a i)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i]) (A := [])
    [.dot [dn j, dn i, up j] j [] (-a j), .lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .dot [dn j, dn i, up j, up i] i [dn j] (-a i),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j]), .dot [] j [up j, dn i, dn j] (a j),
      .lay ([], .cap (up j), [dn i, dn j])] e5 (by dchain) (by dchain) (by dchain)).trans ?_
  -- move the dot inserted at the outer cap to the bottom of the right strand
  have e6 := (zg_slideL (RD := RD) (k := k) ν [] [] [up j, dn i, dn j] (.cap (up i)) j
    (a j)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .lay ([dn j, dn i], .cup (up j), []),
      .dot [dn j, dn i, up j] j [] (-a j), .lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .dot [dn j, dn i, up j, up i] i [dn j] (-a i),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j])])
    [.lay ([], .cap (up j), [dn i, dn j])] e6 (by dchain) (by dchain) (by dchain)).trans ?_
  have e7 := (zg_slideL (RD := RD) (k := k) ν [] [dn i] [dn i, dn j] (.cross true j i) j
    (a j)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .lay ([dn j, dn i], .cup (up j), []),
      .dot [dn j, dn i, up j] j [] (-a j), .lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .dot [dn j, dn i, up j, up i] i [dn j] (-a i)])
    [.lay ([dn j], .cap (up i), [up j, dn i, dn j]), .lay ([], .cap (up j), [dn i, dn j])] e7
    (by dchain) (by dchain) (by dchain)).trans ?_
  have e8 := (zg_dotComm (RD := RD) (k := k) ν [] [dn i, up j, up i] [dn j] j i (a j)
    (-a i)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .lay ([dn j, dn i], .cup (up j), []),
      .dot [dn j, dn i, up j] j [] (-a j), .lay ([dn j, dn i, up j], .cup (up i), [dn j])])
    [.lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j]), .lay ([], .cap (up j), [dn i, dn j])] e8
    (by dchain) (by dchain) (by dchain)).trans ?_
  have e9 := (zg_slideL (RD := RD) (k := k) ν [] [dn i, up j] [dn j] (.cup (up i)) j
    (a j)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .lay ([dn j, dn i], .cup (up j), []),
      .dot [dn j, dn i, up j] j [] (-a j)])
    [.dot [dn j, dn i, up j, up i] i [dn j] (-a i),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j]), .lay ([], .cap (up j), [dn i, dn j])] e9
    (by dchain) (by dchain) (by dchain)).trans ?_
  have e10 := (zg_dotComm (RD := RD) (k := k) ν [] [dn i, up j] [] j j (a j) (-a j)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .lay ([dn j, dn i], .cup (up j), [])])
    [.lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .dot [dn j, dn i, up j, up i] i [dn j] (-a i),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j]), .lay ([], .cap (up j), [dn i, dn j])] e10
    (by dchain) (by dchain) (by dchain)).trans ?_
  have e11 := (zg_slideL (RD := RD) (k := k) ν [] [dn i] [] (.cup (up j)) j (a j)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i]) (A := [.dot [dn j] i [] (a i)])
    [.dot [dn j, dn i, up j] j [] (-a j), .lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .dot [dn j, dn i, up j, up i] i [dn j] (-a i),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j]), .lay ([], .cap (up j), [dn i, dn j])] e11
    (by dchain) (by dchain) (by dchain)).trans ?_
  -- move the dot inserted at the inner cup to the top of the left strand
  have e13 := zg_slideR (RD := RD) (k := k) ν [dn j, dn i] [] [dn j] (.cross true j i) i (-a i)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .dot [] j [dn i] (a j),
      .lay ([dn j, dn i], .cup (up j), []), .dot [dn j, dn i, up j] j [] (-a j),
      .lay ([dn j, dn i, up j], .cup (up i), [dn j])])
    [.lay ([dn j], .cap (up i), [up j, dn i, dn j]), .lay ([], .cap (up j), [dn i, dn j])] e13
    (by dchain) (by dchain) (by dchain)).trans ?_
  have e14 := zg_slideR (RD := RD) (k := k) ν [dn j] [up j] [dn j] (.cap (up i)) i (-a i)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .dot [] j [dn i] (a j),
      .lay ([dn j, dn i], .cup (up j), []), .dot [dn j, dn i, up j] j [] (-a j),
      .lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j])])
    [.lay ([], .cap (up j), [dn i, dn j])] e14 (by dchain) (by dchain) (by dchain)).trans ?_
  have e15 := zg_slideR (RD := RD) (k := k) ν [] [] [dn j] (.cap (up j)) i (-a i)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .dot [] j [dn i] (a j),
      .lay ([dn j, dn i], .cup (up j), []), .dot [dn j, dn i, up j] j [] (-a j),
      .lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j])])
    [] e15 (by dchain) (by dchain) (by dchain)).trans ?_
  -- move the dot inserted at the outer cup to the top of the right strand
  have e16 := zg_slideR (RD := RD) (k := k) ν [dn j, dn i, up j] [] [] (.cup (up i)) j (-a j)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .dot [] j [dn i] (a j),
      .lay ([dn j, dn i], .cup (up j), [])])
    [.lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j]), .lay ([], .cap (up j), [dn i, dn j]),
      .dot [] i [dn j] (-a i)] e16 (by dchain) (by dchain) (by dchain)).trans ?_
  have e17 := zg_slideR (RD := RD) (k := k) ν [dn j, dn i] [dn i] [] (.cross true j i) j (-a j)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .dot [] j [dn i] (a j),
      .lay ([dn j, dn i], .cup (up j), []), .lay ([dn j, dn i, up j], .cup (up i), [dn j])])
    [.lay ([dn j], .cap (up i), [up j, dn i, dn j]), .lay ([], .cap (up j), [dn i, dn j]),
      .dot [] i [dn j] (-a i)] e17 (by dchain) (by dchain) (by dchain)).trans ?_
  have e18 := zg_slideR (RD := RD) (k := k) ν [dn j] [up j, dn i] [] (.cap (up i)) j (-a j)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .dot [] j [dn i] (a j),
      .lay ([dn j, dn i], .cup (up j), []), .lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j])])
    [.lay ([], .cap (up j), [dn i, dn j]), .dot [] i [dn j] (-a i)] e18
    (by dchain) (by dchain) (by dchain)).trans ?_
  have e19 := zg_slideR (RD := RD) (k := k) ν [] [dn i] [] (.cap (up j)) j (-a j)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .dot [] j [dn i] (a j),
      .lay ([dn j, dn i], .cup (up j), []), .lay ([dn j, dn i, up j], .cup (up i), [dn j]),
      .lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
      .lay ([dn j], .cap (up i), [up j, dn i, dn j])])
    [.dot [] i [dn j] (-a i)] e19 (by dchain) (by dchain) (by dchain)).trans ?_
  -- replace the rotated upward crossing by the downward crossing
  have e20 : zg RD k ν [dn j, dn i] [dn i, dn j]
      [.lay ([dn j, dn i], .cup (up j), []), .lay ([dn j, dn i, up j], .cup (up i), [dn j]),
        .lay ([dn j, dn i], .cross true j i, [dn i, dn j]),
        .lay ([dn j], .cap (up i), [up j, dn i, dn j]), .lay ([], .cap (up j), [dn i, dn j])] =
      zg RD k ν [dn j, dn i] [dn i, dn j] [.lay ([], .cross false j i, [])] :=
    (zg_lays_all ν _ _ [_, _, _, _, _]).trans ((congrArg (toLoc RD k).map
      (dg_cycCrossR RD k j i ν).symm).trans (zg_lays_all ν _ _ [_]).symm)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (a i), .dot [] j [dn i] (a j)])
    [.dot [dn i] j [] (-a j), .dot [] i [dn j] (-a i)] e20
    (by dchain) (by dchain) (by dchain)).trans ?_
  exact zg_crossConj ν j i (a i) (a j) (by rintro rfl; rfl)

variable [DecidableEq I] in
/-- The image of `rotCrossL` under the weight shift is the image of the downward crossing. -/
theorem zg_cycCrossL (ν : X) (j i : I) :
    zg RD k ν [dn j, dn i] [dn i, dn j]
      ([([], .cup (dn i), [dn j, dn i]), ([dn i], .cup (dn j), [up i, dn j, dn i]),
        ([dn i, dn j], .cross true j i, [dn j, dn i]), ([dn i, dn j, up i], .cap (dn j), [dn i]),
        ([dn i, dn j], .cap (dn i), [])].flatMap (layStep a b)) =
      zg RD k ν [dn j, dn i] [dn i, dn j]
        ([([], .cross false j i, [])].flatMap (layStep a b)) := by
  -- move the dot inserted at the outer cap to the bottom of the right strand
  have s1 := (zg_slideR (RD := RD) (k := k) ν [dn i, dn j, up i] [] [] (.cap (dn j)) i
    (b i)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.lay ([], .cup (dn i), [dn j, dn i]), .dot [] i [up i, dn j, dn i] (-b i),
      .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .dot [dn i, dn j, up i, up j] j [dn i] (b j)])
    [.lay ([dn i, dn j], .cap (dn i), [])] s1 (by dchain) (by dchain) (by dchain)).trans ?_
  have s2 := zg_dotComm (RD := RD) (k := k) ν [dn i, dn j, up i, up j] [] [] j i (b j) (b i)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.lay ([], .cup (dn i), [dn j, dn i]), .dot [] i [up i, dn j, dn i] (-b i),
      .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i])])
    [.lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), [])] s2
    (by dchain) (by dchain) (by dchain)).trans ?_
  have s3 := (zg_slideR (RD := RD) (k := k) ν [dn i, dn j] [dn j] [] (.cross true j i) i
    (b i)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.lay ([], .cup (dn i), [dn j, dn i]), .dot [] i [up i, dn j, dn i] (-b i),
      .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j)])
    [.dot [dn i, dn j, up i, up j] j [dn i] (b j), .lay ([dn i, dn j, up i], .cap (dn j), [dn i]),
      .lay ([dn i, dn j], .cap (dn i), [])] s3 (by dchain) (by dchain) (by dchain)).trans ?_
  have s4 := zg_dotComm (RD := RD) (k := k) ν [dn i] [up j, up i, dn j] [] j i (-b j) (b i)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.lay ([], .cup (dn i), [dn j, dn i]), .dot [] i [up i, dn j, dn i] (-b i),
      .lay ([dn i], .cup (dn j), [up i, dn j, dn i])])
    [.lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .dot [dn i, dn j, up i, up j] j [dn i] (b j), .lay ([dn i, dn j, up i], .cap (dn j), [dn i]),
      .lay ([dn i, dn j], .cap (dn i), [])] s4 (by dchain) (by dchain) (by dchain)).trans ?_
  have s5 := (zg_slideR (RD := RD) (k := k) ν [dn i] [up i, dn j] [] (.cup (dn j)) i
    (b i)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.lay ([], .cup (dn i), [dn j, dn i]), .dot [] i [up i, dn j, dn i] (-b i)])
    [.dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .dot [dn i, dn j, up i, up j] j [dn i] (b j), .lay ([dn i, dn j, up i], .cap (dn j), [dn i]),
      .lay ([dn i, dn j], .cap (dn i), [])] s5 (by dchain) (by dchain) (by dchain)).trans ?_
  have s6 := zg_dotComm (RD := RD) (k := k) ν [] [up i, dn j] [] i i (-b i) (b i)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.lay ([], .cup (dn i), [dn j, dn i])])
    [.lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .dot [dn i, dn j, up i, up j] j [dn i] (b j), .lay ([dn i, dn j, up i], .cap (dn j), [dn i]),
      .lay ([dn i, dn j], .cap (dn i), [])] s6 (by dchain) (by dchain) (by dchain)).trans ?_
  have s7 := (zg_slideR (RD := RD) (k := k) ν [] [dn j] [] (.cup (dn i)) i (b i)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i]) (A := [])
    [.dot [] i [up i, dn j, dn i] (-b i), .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .dot [dn i, dn j, up i, up j] j [dn i] (b j), .lay ([dn i, dn j, up i], .cap (dn j), [dn i]),
      .lay ([dn i, dn j], .cap (dn i), [])] s7 (by dchain) (by dchain) (by dchain)).trans ?_
  -- move the dot inserted at the inner cap to the bottom of the left strand
  have r1 := (zg_slideR (RD := RD) (k := k) ν [dn i, dn j] [] [dn i] (.cross true j i) j
    (b j)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .lay ([], .cup (dn i), [dn j, dn i]),
      .dot [] i [up i, dn j, dn i] (-b i), .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j)])
    [.lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), [])] r1
    (by dchain) (by dchain) (by dchain)).trans ?_
  have r2 := zg_dotComm (RD := RD) (k := k) ν [dn i] [up j, up i] [dn i] j j (-b j) (b j)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .lay ([], .cup (dn i), [dn j, dn i]),
      .dot [] i [up i, dn j, dn i] (-b i), .lay ([dn i], .cup (dn j), [up i, dn j, dn i])])
    [.lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), [])] r2
    (by dchain) (by dchain) (by dchain)).trans ?_
  have r3 := (zg_slideR (RD := RD) (k := k) ν [dn i] [up i] [dn i] (.cup (dn j)) j (b j)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .lay ([], .cup (dn i), [dn j, dn i]),
      .dot [] i [up i, dn j, dn i] (-b i)])
    [.dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), [])] r3
    (by dchain) (by dchain) (by dchain)).trans ?_
  have r4 := zg_dotComm (RD := RD) (k := k) ν [] [up i] [dn i] i j (-b i) (b j)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .lay ([], .cup (dn i), [dn j, dn i])])
    [.lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), [])] r4
    (by dchain) (by dchain) (by dchain)).trans ?_
  have r5 := (zg_slideR (RD := RD) (k := k) ν [] [] [dn i] (.cup (dn i)) j (b j)).symm
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i]) (A := [.dot [dn j] i [] (b i)])
    [.dot [] i [up i, dn j, dn i] (-b i), .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), [])] r5
    (by dchain) (by dchain) (by dchain)).trans ?_
  -- move the dot inserted at the outer cup to the top of the right strand
  have p1 := zg_slideL (RD := RD) (k := k) ν [] [] [up i, dn j, dn i] (.cup (dn j)) i (-b i)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .dot [] j [dn i] (b j),
      .lay ([], .cup (dn i), [dn j, dn i])])
    [.dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), [])] p1
    (by dchain) (by dchain) (by dchain)).trans ?_
  have p2 := zg_dotComm (RD := RD) (k := k) ν [] [] [up j, up i, dn j, dn i] i j (-b i) (-b j)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .dot [] j [dn i] (b j),
      .lay ([], .cup (dn i), [dn j, dn i]), .lay ([dn i], .cup (dn j), [up i, dn j, dn i])])
    [.lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), [])] p2
    (by dchain) (by dchain) (by dchain)).trans ?_
  have p3 := zg_slideL (RD := RD) (k := k) ν [] [dn j] [dn j, dn i] (.cross true j i) i (-b i)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .dot [] j [dn i] (b j),
      .lay ([], .cup (dn i), [dn j, dn i]), .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j)])
    [.lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), [])] p3
    (by dchain) (by dchain) (by dchain)).trans ?_
  have p4 := zg_slideL (RD := RD) (k := k) ν [] [dn j, up i] [dn i] (.cap (dn j)) i (-b i)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .dot [] j [dn i] (b j),
      .lay ([], .cup (dn i), [dn j, dn i]), .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i])])
    [.lay ([dn i, dn j], .cap (dn i), [])] p4 (by dchain) (by dchain) (by dchain)).trans ?_
  have p5 := zg_slideL (RD := RD) (k := k) ν [] [dn j] [] (.cap (dn i)) i (-b i)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .dot [] j [dn i] (b j),
      .lay ([], .cup (dn i), [dn j, dn i]), .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .dot [dn i] j [up j, up i, dn j, dn i] (-b j),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .lay ([dn i, dn j, up i], .cap (dn j), [dn i])])
    [] p5 (by dchain) (by dchain) (by dchain)).trans ?_
  -- move the dot inserted at the inner cup to the top of the left strand
  have q1 := zg_slideL (RD := RD) (k := k) ν [dn i] [] [dn j, dn i] (.cross true j i) j (-b j)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .dot [] j [dn i] (b j),
      .lay ([], .cup (dn i), [dn j, dn i]), .lay ([dn i], .cup (dn j), [up i, dn j, dn i])])
    [.lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), []),
      .dot [] i [dn j] (-b i)] q1 (by dchain) (by dchain) (by dchain)).trans ?_
  have q2 := zg_slideL (RD := RD) (k := k) ν [dn i] [up i] [dn i] (.cap (dn j)) j (-b j)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .dot [] j [dn i] (b j),
      .lay ([], .cup (dn i), [dn j, dn i]), .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i])])
    [.lay ([dn i, dn j], .cap (dn i), []), .dot [] i [dn j] (-b i)] q2
    (by dchain) (by dchain) (by dchain)).trans ?_
  have q3 := zg_slideL (RD := RD) (k := k) ν [dn i] [] [] (.cap (dn i)) j (-b j)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .dot [] j [dn i] (b j),
      .lay ([], .cup (dn i), [dn j, dn i]), .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
      .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
      .lay ([dn i, dn j, up i], .cap (dn j), [dn i])])
    [.dot [] i [dn j] (-b i)] q3 (by dchain) (by dchain) (by dchain)).trans ?_
  -- replace the rotated upward crossing by the downward crossing
  have e : zg RD k ν [dn j, dn i] [dn i, dn j]
      [.lay ([], .cup (dn i), [dn j, dn i]), .lay ([dn i], .cup (dn j), [up i, dn j, dn i]),
        .lay ([dn i, dn j], .cross true j i, [dn j, dn i]),
        .lay ([dn i, dn j, up i], .cap (dn j), [dn i]), .lay ([dn i, dn j], .cap (dn i), [])] =
      zg RD k ν [dn j, dn i] [dn i, dn j] [.lay ([], .cross false j i, [])] :=
    (zg_lays_all ν _ _ [_, _, _, _, _]).trans ((congrArg (toLoc RD k).map
      (dg_cycCrossL RD k j i ν).symm).trans (zg_lays_all ν _ _ [_]).symm)
  refine (zg_local' ν [dn i, dn j] (s := [dn j, dn i])
    (A := [.dot [dn j] i [] (b i), .dot [] j [dn i] (b j)])
    [.dot [dn i] j [] (-b j), .dot [] i [dn j] (-b i)] e
    (by dchain) (by dchain) (by dchain)).trans ?_
  exact zg_crossConj ν j i (b i) (b j) (by rintro rfl; rfl)

variable (RD k) (δ : X)

/-- **The cyclicity relation `cycCrossR`** (KL III `eq_cyclic_cross-gen`) holds for the images
of the weight shift (Webster arXiv:1309.3796v2, Proposition 3.30). -/
theorem shift_rel_cycCrossR (j i : I) (μ : X) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.cycCrossR j i μ)))) = 0 := by
  classical
  exact shiftLin_mkD_sub RD k δ a b μ _ _ _ _ (zg_cycCrossR a b (μ + δ) j i)

/-- **The cyclicity relation `cycCrossL`** (KL III `eq_cyclic_cross-gen`) holds for the images
of the weight shift (Webster arXiv:1309.3796v2, Proposition 3.30). -/
theorem shift_rel_cycCrossL (j i : I) (μ : X) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.cycCrossL j i μ)))) = 0 := by
  classical
  exact shiftLin_mkD_sub RD k δ a b μ _ _ _ _ (zg_cycCrossL a b (μ + δ) j i)

end Categorification.KL3.Diagram

