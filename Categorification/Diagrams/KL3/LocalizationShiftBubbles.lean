/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftCyclic
import Categorification.Diagrams.KL3.BubbleSlidesAll

/-!
# The bubble relations under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. Under Webster's hypothesis `a i - b i = -⟨αᵢ^∨, δ⟩` the images of the bubble
relations of KL III (eq. (3.4) and the degree-zero normalizations: `cwNeg`, `ccwNeg`, `cwOne`,
`ccwOne`) under the weight shift `shiftFree RD k δ a b` vanish (`shift_rel_cwNeg`,
`shift_rel_ccwNeg`, `shift_rel_cwOne`, `shift_rel_ccwOne`).

The image of a clockwise bubble with `α` dots at weight `λ` is the bubble of `U′` at weight
`λ + δ` with `α + b i - a i = α + ⟨αᵢ^∨, δ⟩` dots on its downward strand (`zg_img_cw`), where a
negative number of dots means a power of the inverse dot; the counterclockwise case gives
`α - ⟨αᵢ^∨, δ⟩` dots (`zg_img_ccw`). These bubbles of `U′` are the images of the bubbles
`cwU`, `ccwU` of `U` with an integer number of dots (`zcw_eq`, `zccw_eq`), so the relations
follow from `cwU_eq_zero`, `cwU_deg0` and their counterclockwise analogues.
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y} {k : Type w} [CommRing k]

/-- A natural number of dots, as a composite of dot layers. -/
theorem zdot_nat (ν : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) (m : ℕ) :
    zdot RD k ν u i v (m : ℤ) =
      ldg RD k ν (u ++ [dn i] ++ v) (u ++ [dn i] ++ v) (List.replicate m (u, .dot (dn i), v)) := by
  induction m with
  | zero => rw [Nat.cast_zero, zdot_zero, List.replicate_zero, ldg_nil]
  | succ m ih =>
    have h1 : SChain (u ++ [dn i] ++ v) [(u, .dot (dn i), v)] (u ++ [dn i] ++ v) := ⟨rfl, rfl⟩
    rw [Nat.cast_succ, zdot_add, ih, zdot_one, ldot, ← ldg_of RD k h1,
      ldg_comp RD k h1 (SChain.replicate m u (dn i) v), List.replicate_succ]
    rfl

/-- A negative number of dots, as a power of the inverse dot. -/
theorem zdot_neg_nat (ν : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) (m : ℕ) :
    zdot RD k ν u i v (-(m : ℤ)) = iterComp (zdot RD k ν u i v (-1)) m := by
  induction m with
  | zero => rw [Nat.cast_zero, neg_zero, zdot_zero]; rfl
  | succ m ih =>
    rw [Nat.cast_succ, neg_add, zdot_add, ih]; rfl

variable (RD k) in
/-- `diag` commutes with iterated composition. -/
theorem diag_iterComp_lsig {a : Obj (lsig RD)} (f : a ⟶ a) (n : ℕ) :
    (presLoc RD k).diag (iterComp f n) = iterComp ((presLoc RD k).diag f) n := by
  induction n with
  | zero => exact (presLoc RD k).diag_id _
  | succ n ih => rw [iterComp, iterComp, Presentation.diag_comp, ih]

/-- The clockwise bubble of `U′` with `n ∈ ℤ` dots on its downward strand. -/
abbrev zcw (ν : X) (i : I) (n : ℤ) : lob RD k ν [] ⟶ lob RD k ν [] :=
  ldg RD k ν [] [up i, dn i] [([], .cup (up i), [])] ≫ zdot RD k ν [up i] i [] n ≫
    ldg RD k ν [up i, dn i] [] [([], .cap (dn i), [])]

/-- The clockwise bubble of `U′` is the image of the clockwise bubble `cwU` of `U`. -/
theorem zcw_eq (ν : X) (i : I) (n : ℤ) :
    zcw (RD := RD) (k := k) ν i n = (toLoc RD k).map (cwU RD k ν i n) := by
  have hc : SChain [] [([], .cup (up i), [])] [up i, dn i] := ⟨rfl, rfl⟩
  have hk : SChain [up i, dn i] [([], .cap (dn i), [])] [] := ⟨rfl, rfl⟩
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, zcw, zdot_nat, ← Category.assoc]
    erw [ldg_comp RD k hc (SChain.replicate m [up i] (dn i) [])]
    erw [ldg_comp RD k (SChain.append hc (SChain.replicate m [up i] (dn i) [])) hk]
    rw [cwU_of_nonneg]
    rfl
  | negSucc m =>
    have e := cwNegHonest_eq RD k ν i m
    rw [cwNegHonest, Presentation.diag_comp, Presentation.diag_comp, diag_iterComp_lsig,
      ← zdot_neg_one, ← zdot_neg_nat] at e
    rw [zcw, Int.negSucc_eq, ← Nat.cast_succ, ldg_of RD k hc, ldg_of RD k hk]
    exact e

/-- The counterclockwise bubble of `U′` with `n ∈ ℤ` dots on its downward strand. -/
abbrev zccw (ν : X) (i : I) (n : ℤ) : lob RD k ν [] ⟶ lob RD k ν [] :=
  ldg RD k ν [] [dn i, up i] [([], .cup (dn i), [])] ≫ zdot RD k ν [] i [up i] n ≫
    ldg RD k ν [dn i, up i] [] [([], .cap (up i), [])]

/-- The counterclockwise bubble of `U′` is the image of the bubble `ccwU` of `U`. -/
theorem zccw_eq (ν : X) (i : I) (n : ℤ) :
    zccw (RD := RD) (k := k) ν i n = (toLoc RD k).map (ccwU RD k ν i n) := by
  have hc : SChain [] [([], .cup (dn i), [])] [dn i, up i] := ⟨rfl, rfl⟩
  have hk : SChain [dn i, up i] [([], .cap (up i), [])] [] := ⟨rfl, rfl⟩
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, zccw, zdot_nat]
    erw [ldg_comp RD k (SChain.replicate m [] (dn i) [up i]) hk]
    rw [ldg, ldg]
    erw [dg_dots_cap_up]
    rw [← ldg, ← ldg]
    erw [ldg_comp RD k hc (SChain.append (SChain.replicate m [dn i] (up i) []) hk)]
    rw [ccwU_of_nonneg]
    rfl
  | negSucc m =>
    have e := ccwNegHonest_eq RD k ν i m
    rw [ccwNegHonest, Presentation.diag_comp, Presentation.diag_comp, diag_iterComp_lsig,
      ← zdot_neg_one, ← zdot_neg_nat] at e
    rw [zccw, Int.negSucc_eq, ← Nat.cast_succ, ldg_of RD k hc, ldg_of RD k hk]
    exact e

/-- Dots on the two strands of a cup–cap pair commute. -/
theorem ldot_rep_up (ν : X) (i : I) (α : ℕ) (n : ℤ) :
    zdot RD k ν [] i [up i] n ≫
        ldg RD k ν [dn i, up i] [dn i, up i] (List.replicate α ([dn i], .dot (up i), [])) =
      ldg RD k ν [dn i, up i] [dn i, up i] (List.replicate α ([dn i], .dot (up i), [])) ≫
        zdot RD k ν [] i [up i] n := by
  refine zdot_comp_of_one (RD := RD) (k := k) (A := []) (B := [up i]) (A' := [])
    (B' := [up i]) ν _ ?_ n
  have h1 : SChain [dn i, up i] [([], .dot (dn i), [up i])] [dn i, up i] := ⟨rfl, rfl⟩
  rw [zdot_one, ldot, ← ldg_of RD k h1]
  erw [ldg_comp RD k h1 (SChain.replicate α [dn i] (up i) []),
    ldg_comp RD k (SChain.replicate α [dn i] (up i) []) h1]
  exact congrArg (toLoc RD k).map
    (dg_swap_rep RD k ν [] [] [] (.dot (dn i)) (.dot (up i)) rfl α).symm

/-- Dot layers are unchanged by the weight shift. -/
theorem flatMap_layStep_dots (a b : I → ℤ) (α : ℕ) (u : List (Letter I)) (l : Letter I)
    (v : List (Letter I)) :
    (List.replicate α (u, Shape.dot l, v)).flatMap (layStep a b) =
      (List.replicate α (u, Shape.dot l, v)).map .lay := by
  induction α with
  | zero => rfl
  | succ α ih => rw [List.replicate_succ, List.flatMap_cons, ih]; rfl

variable (a b : I → ℤ)

/-- The image of a clockwise bubble with `α` dots under the weight shift. -/
theorem zg_img_cw (ν : X) (i : I) (α : ℕ) :
    zg RD k ν [] [] ((cwLs i α).flatMap (layStep a b)) = zcw ν i (b i + (α + -a i)) := by
  rw [cwLs, List.flatMap_append, List.flatMap_append,
    flatMap_layStep_dots a b α [up i] (dn i) []]
  have h1 : DChain [] ([([], Shape.cup (up i), [])].flatMap (layStep a b)) [up i, dn i] :=
    ⟨rfl, rfl, rfl⟩
  rw [zg_append ν (r := [up i, dn i]) [] _
      (DChain.append h1 (dChain_lays (SChain.replicate α [up i] (dn i) []))),
    zg_append ν (r := [up i, dn i]) _ _ h1]
  erw [zg_lays ν (SChain.replicate α [up i] (dn i) [])]
  erw [zg_cons_self ν _ (DStep.lay ([], .cup (up i), [])),
    zg_cons_self ν _ (DStep.dot [up i] i [] (-a i)), zg_nil, Category.comp_id,
    zg_cons_self ν _ (DStep.dot [up i] i [] (b i)),
    zg_cons_self ν _ (DStep.lay ([], .cap (dn i), []))]
  erw [zg_nil, Category.comp_id, ← zdot_nat]
  simp only [Category.assoc]
  show ldg RD k ν [] [up i, dn i] _ ≫ zdot RD k ν [up i] i [] (-a i) ≫
    zdot RD k ν [up i] i [] α ≫ zdot RD k ν [up i] i [] (b i) ≫ ldg RD k ν _ [] _ = _
  rw [← Category.assoc (zdot RD k ν [up i] i [] (-a i)), ← zdot_add,
    ← Category.assoc (zdot RD k ν [up i] i [] _), ← zdot_add]
  rfl

/-- The image of a counterclockwise bubble with `α` dots under the weight shift. -/
theorem zg_img_ccw (ν : X) (i : I) (α : ℕ) :
    zg RD k ν [] [] ((ccwLs i α).flatMap (layStep a b)) = zccw ν i (α + (a i + -b i)) := by
  rw [ccwLs, List.flatMap_append, List.flatMap_append,
    flatMap_layStep_dots a b α [dn i] (up i) []]
  have h1 : DChain [] ([([], Shape.cup (dn i), [])].flatMap (layStep a b)) [dn i, up i] :=
    ⟨rfl, rfl, rfl⟩
  rw [zg_append ν (r := [dn i, up i]) [] _
      (DChain.append h1 (dChain_lays (SChain.replicate α [dn i] (up i) []))),
    zg_append ν (r := [dn i, up i]) _ _ h1]
  erw [zg_lays ν (SChain.replicate α [dn i] (up i) [])]
  erw [zg_cons_self ν _ (DStep.lay ([], .cup (dn i), [])),
    zg_cons_self ν _ (DStep.dot [] i [up i] (-b i)), zg_nil, Category.comp_id,
    zg_cons_self ν _ (DStep.dot [] i [up i] (a i)),
    zg_cons_self ν _ (DStep.lay ([], .cap (up i), []))]
  erw [zg_nil, Category.comp_id]
  simp only [Category.assoc]
  show ldg RD k ν [] [dn i, up i] _ ≫ zdot RD k ν [] i [up i] (-b i) ≫
    ldg RD k ν [dn i, up i] [dn i, up i] (List.replicate α ([dn i], .dot (up i), [])) ≫
      zdot RD k ν [] i [up i] (a i) ≫ ldg RD k ν [dn i, up i] [] [([], .cap (up i), [])] = _
  have hk : SChain [dn i, up i] [([], .cap (up i), [])] [] := ⟨rfl, rfl⟩
  rw [← Category.assoc _ (zdot RD k ν [] i [up i] (a i)), ← ldot_rep_up, Category.assoc,
    ← Category.assoc (zdot RD k ν [] i [up i] (-b i)), ← zdot_add]
  erw [ldg_comp RD k (SChain.replicate α [dn i] (up i) []) hk]
  rw [ldg, ldg]
  erw [← dg_dots_cap_up]
  rw [← ldg, ← ldg]
  erw [← ldg_comp RD k (SChain.replicate α [] (dn i) [up i]) hk, ← zdot_nat]
  rw [← Category.assoc (zdot RD k ν [] i [up i] _), ← zdot_add]
  rfl

variable (RD k) (δ : X)

/-- A relation given by a single normal-form diagram holds for the images of the weight shift
as soon as the composite of its image vanishes. -/
theorem shiftLin_mkD_zero (μ : X) {s t : List (Letter I)} (ls : List (LayerData I))
    (h : SChain s ls t) (hz : zg RD k (μ + δ) s t (ls.flatMap (layStep a b)) = 0) :
    (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k (LinDiagram.of (mkD RD μ ls h))) =
      0 := by
  rw [inclLin_of, freeLift_map_of, shiftFree_map_mkD, imgList_eq_zg, hz, Limits.zero_comp,
    Limits.comp_zero]

/-- Additivity of the pairing with a simple coroot. -/
theorem ip_add_shift (i : I) (lam : X) : ip RD i (lam + δ) = ip RD i lam + ip RD i δ := by
  simp [ip]

/-- **The relation `cwNeg`** (KL III (3.4)) holds for the images of the weight shift. -/
theorem shift_rel_cwNeg (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X) (α : ℕ)
    (h : (α : ℤ) < ip RD i lam - 1) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.cwNeg i lam α h)))) = 0 := by
  show (freeLift k (shiftFree RD k δ a b)).map
    (inclLin RD k (LinDiagram.of (mkD RD lam (cwLs i α) (sChain_cwLs i α)))) = 0
  refine shiftLin_mkD_zero RD k a b δ lam _ _ ?_
  have := hab i
  have := ip_add_shift RD δ i lam
  rw [zg_img_cw, zcw_eq]
  erw [cwU_eq_zero RD k (lam + δ) i _ (by omega), CategoryTheory.Functor.map_zero]

/-- **The relation `ccwNeg`** (KL III (3.4)) holds for the images of the weight shift. -/
theorem shift_rel_ccwNeg (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X) (α : ℕ)
    (h : (α : ℤ) < -ip RD i lam - 1) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.ccwNeg i lam α h)))) = 0 := by
  show (freeLift k (shiftFree RD k δ a b)).map
    (inclLin RD k (LinDiagram.of (mkD RD lam (ccwLs i α) (sChain_ccwLs i α)))) = 0
  refine shiftLin_mkD_zero RD k a b δ lam _ _ ?_
  have := hab i
  have := ip_add_shift RD δ i lam
  rw [zg_img_ccw, zccw_eq]
  erw [ccwU_eq_zero RD k (lam + δ) i _ (by omega), CategoryTheory.Functor.map_zero]

/-- **The relation `cwOne`** (the clockwise degree-zero bubble is `1`) holds for the images of
the weight shift. -/
theorem shift_rel_cwOne (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X)
    (h : 1 ≤ ip RD i lam) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.cwOne i lam h)))) = 0 := by
  have e2 : 𝟙 (ob RD lam []) = mkD RD lam ([] : List (LayerData I)) rfl := by
    ext; simp
  show (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k
    (LinDiagram.of (mkD RD lam (cwLs i (ip RD i lam - 1).toNat) (sChain_cwLs i _)) -
      LinDiagram.of (𝟙 _))) = 0
  rw [e2]
  refine shiftLin_mkD_sub RD k δ a b lam _ _ _ _ ?_
  have := hab i
  have := ip_add_shift RD δ i lam
  have e : b i + (((ip RD i lam - 1).toNat : ℕ) + -a i) = ip RD i (lam + δ) - 1 := by omega
  rw [zg_img_cw, e, zcw_eq]
  erw [cwU_deg0, CategoryTheory.Functor.map_id]
  erw [List.flatMap_nil, zg_nil]
  rfl

/-- **The relation `ccwOne`** (the counterclockwise degree-zero bubble is `1`) holds for the
images of the weight shift. -/
theorem shift_rel_ccwOne (hab : ∀ i, a i - b i = -ip RD i δ) (i : I) (lam : X)
    (h : ip RD i lam ≤ -1) :
    (freeLift k (shiftFree RD k δ a b)).map
      ((presLoc RD k).rel (.inl (.inr (.ccwOne i lam h)))) = 0 := by
  have e2 : 𝟙 (ob RD lam []) = mkD RD lam ([] : List (LayerData I)) rfl := by
    ext; simp
  show (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k
    (LinDiagram.of (mkD RD lam (ccwLs i (-ip RD i lam - 1).toNat) (sChain_ccwLs i _)) -
      LinDiagram.of (𝟙 _))) = 0
  rw [e2]
  refine shiftLin_mkD_sub RD k δ a b lam _ _ _ _ ?_
  have := hab i
  have := ip_add_shift RD δ i lam
  have e : (((-ip RD i lam - 1).toNat : ℕ) : ℤ) + (a i + -b i) = -ip RD i (lam + δ) - 1 := by
    omega
  rw [zg_img_ccw, e, zccw_eq]
  erw [ccwU_deg0, CategoryTheory.Functor.map_id]
  erw [List.flatMap_nil, zg_nil]
  rfl

end Categorification.KL3.Diagram
