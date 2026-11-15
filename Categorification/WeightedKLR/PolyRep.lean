/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DividedDifference
import Categorification.WeightedKLR.Loading

/-!
# The polynomial representation of a weighted KLR algebra: elementary operators

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1,
Proposition `prop:action`.

The weighted KLR algebra acts on one copy of `k[y_s : s ∈ Strand ν]` for each chamber. Since
strands are indexed by colour and rank (`Strand ν`), a crossing of two strands of different
colours does not change the indexing, and acts by the identity; the paper's permutation `s_j`
of positional variables is this relabelling. The other events act as follows:

* a dot on strand `s`: multiplication by `y_s` (`dotOp`);
* crossing the wall `w = (e, a, b)` from the side where `b` is left of the ghost of `a` to the
  side where it is right of it: multiplication by `Q_e(y_a, y_b)` (`wallFactor`); in the other
  direction, the identity (`wallOp`);
* the crossing of the strands `s, s'` of colour `i` and consecutive ranks: the divided
  difference `∂_{s s'}` if there is no loop of weight `0` at `i`, and `P_i(y_s, y_{s'}) (1 - s)`
  if there is one (`psiOp`).

## Main results

The local relations of the paper's Definition `def:wKLR` that involve one event type:
* `dotOp_comm` : dots commute;
* `wallOp_comp_wallOp` : the ghost bigon, relation (2);
* `psiOp_comp_psiOp` : the strand bigon, relation (3);
* `psiOp_comp_dotOp_left`, `psiOp_comp_dotOp_right` : the nilHecke relations (1) for the two
  strands crossing (no loop); `psiOp_comp_dotOp_of_ne` : dots on other strands commute with `ψ`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

/-- The polynomial ring on which each idempotent of the weighted KLR algebra acts. -/
abbrev PolyRing (ν : I →₀ ℕ) (k : Type*) [CommRing k] := MvPolynomial (Strand ν) k

variable (k) in
omit [DecidableEq I] in
/-- A dot on strand `s`. -/
noncomputable def dotOp (s : Strand ν) : PolyRing ν k →ₗ[k] PolyRing ν k :=
  LinearMap.mulLeft k (X s)

omit [DecidableEq I] in
theorem dotOp_comm (s t : Strand ν) :
    dotOp k s ∘ₗ dotOp k t = dotOp k t ∘ₗ dotOp k s := by
  refine LinearMap.ext fun f => ?_
  exact mul_left_comm (X s) (X t) f

namespace Wall

/-- `Q_e(y_a, y_b)` for the wall `w = (e, a, b)`. -/
noncomputable def factor (w : Wall Γ ν) : PolyRing ν k :=
  aeval (Fin.cons (X w.src) (fun _ => X w.tgt) : Fin 2 → PolyRing ν k) (Γ.Q w.edge)

end Wall

/-- Crossing the wall `w`, from the side `σ` to the side `σ'` (`true` meaning strand `w.tgt` is
to the right of the ghost of `w.src`). Only the passage from `false` to `true` contributes a
factor. -/
noncomputable def wallOp (w : Wall Γ ν) (σ σ' : Bool) : PolyRing ν k →ₗ[k] PolyRing ν k :=
  if σ = false ∧ σ' = true then LinearMap.mulLeft k w.factor else LinearMap.id

omit [DecidableEq I] in
/-- The ghost bigon, relation (2) of the paper: crossing a wall and coming back multiplies by
`Q_e(y_a, y_b)`, whichever side one starts from. -/
theorem wallOp_comp_wallOp (w : Wall Γ ν) {σ σ' : Bool} (h : σ ≠ σ') :
    wallOp w σ' σ ∘ₗ wallOp w σ σ' = LinearMap.mulLeft k w.factor := by
  cases σ <;> cases σ' <;> simp_all [wallOp]

variable (Γ) in
/-- The crossing of strands `s` and `s'` of the same colour: `∂_{s s'}`, or
`P_i(y_s, y_{s'}) (1 - swap)` when there is a loop of weight `0` at the colour `i` of `s`. -/
noncomputable def psiOp (s s' : Strand ν) : PolyRing ν k →ₗ[k] PolyRing ν k :=
  match Γ.loop s.1 with
  | none => ddiff s s'
  | some P =>
    LinearMap.mulLeft k (aeval (Fin.cons (X s) (fun _ => X s') : Fin 2 → PolyRing ν k) P) ∘ₗ
      (LinearMap.id - (rename (swap s s')).toLinearMap)

/-- The loop factor `P_i(y_s, y_{s'})`. -/
noncomputable def loopFactor (P : MvPolynomial (Fin 2) k) (s s' : Strand ν) : PolyRing ν k :=
  aeval (Fin.cons (X s) (fun _ => X s') : Fin 2 → PolyRing ν k) P

theorem psiOp_of_none {s s' : Strand ν} (h : Γ.loop s.1 = none) :
    psiOp (k := k) Γ s s' = ddiff s s' := by
  simp [psiOp, h]

theorem psiOp_of_some {s s' : Strand ν} {P : MvPolynomial (Fin 2) k} (h : Γ.loop s.1 = some P)
    (f : PolyRing ν k) :
    psiOp Γ s s' f = loopFactor P s s' * (f - rename (swap s s') f) := by
  simp [psiOp, h, loopFactor]

theorem rename_swap_loopFactor {P : MvPolynomial (Fin 2) k}
    (hP : rename (swap (0 : Fin 2) 1) P = P) (s s' : Strand ν) :
    rename (swap s s') (loopFactor P s s') = loopFactor P s s' := by
  rw [loopFactor, ← AlgHom.comp_apply, comp_aeval]
  conv_rhs => rw [← hP, aeval_rename]
  congr 2
  funext j
  fin_cases j <;> simp [swap_apply_left, swap_apply_right]

/-- The strand bigon, relation (3) of the paper: `ψ² = 0` without a loop, and
`ψ² = 2 P_i(y_s, y_{s'}) ψ` with a loop whose polynomial `P_i` is symmetric. -/
theorem psiOp_comp_psiOp (hΓ : Γ.PSymm) {s s' : Strand ν} (hss' : s ≠ s') :
    psiOp Γ s s' ∘ₗ psiOp Γ s s' =
      match Γ.loop s.1 with
      | none => 0
      | some P => (2 : k) • (LinearMap.mulLeft k (loopFactor P s s') ∘ₗ psiOp Γ s s') := by
  rcases h : Γ.loop s.1 with _ | P
  · refine LinearMap.ext fun f => ?_
    simp [psiOp_of_none h, ddiff_ddiff hss']
  · refine LinearMap.ext fun f => ?_
    have hsym := rename_swap_loopFactor (hΓ _ P h) s s'
    simp only [LinearMap.comp_apply, psiOp_of_some h, LinearMap.smul_apply,
      LinearMap.mulLeft_apply, map_mul, map_sub, hsym, rename_swap_rename_swap]
    rw [Algebra.smul_def, map_ofNat]
    ring

/-- Relation (1) of the paper without a loop: `ψ y_s = y_{s'} ψ + 1`. -/
theorem psiOp_comp_dotOp_left {s s' : Strand ν} (h : Γ.loop s.1 = none) (hss' : s ≠ s') :
    psiOp Γ s s' ∘ₗ dotOp k s = dotOp k s' ∘ₗ psiOp Γ s s' + LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  simp [psiOp_of_none h, dotOp, ddiff_mul hss', swap_apply_left, ddiff_X_left hss', add_comm]

/-- Relation (1) of the paper without a loop: `ψ y_{s'} = y_s ψ - 1`. -/
theorem psiOp_comp_dotOp_right {s s' : Strand ν} (h : Γ.loop s.1 = none) (hss' : s ≠ s') :
    psiOp Γ s s' ∘ₗ dotOp k s' = dotOp k s ∘ₗ psiOp Γ s s' - LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  simp [psiOp_of_none h, dotOp, ddiff_mul hss', swap_apply_right, ddiff_X_right hss',
    sub_eq_neg_add]

/-- A dot on a third strand commutes with `ψ`. -/
theorem psiOp_comp_dotOp_of_ne {s s' t : Strand ν} (hss' : s ≠ s') (hts : t ≠ s)
    (hts' : t ≠ s') : psiOp Γ s s' ∘ₗ dotOp k t = dotOp k t ∘ₗ psiOp Γ s s' := by
  refine LinearMap.ext fun f => ?_
  rcases h : Γ.loop s.1 with _ | P
  · simp [psiOp_of_none h, dotOp, ddiff_mul hss', ddiff_X_of_ne hss' hts hts',
      swap_apply_of_ne_of_ne hts hts']
  · simp only [LinearMap.comp_apply, psiOp_of_some h, dotOp, LinearMap.mulLeft_apply, map_mul,
      rename_X, swap_apply_of_ne_of_ne hts hts']
    ring

end Categorification.WeightedKLR
