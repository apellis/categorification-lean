/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapGradedDegrees
import Categorification.Algebra.Graded.TensorGdim
import Categorification.Algebra.Graded.RightTwist

/-!
# The grading of the cap bimodules `K̃^{λ⁺}_λ` and `K^{λ⁺}_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
Definitions 7.14 and 7.15, with the diagram grading of Definitions 4.4–4.7. Webster's
categories `𝒱^λ_{1/D}` are categories of graded modules and his functors `𝕂`, `𝕋` are graded;
the bimodules carry the diagram grading, which Webster leaves implicit. We make it explicit.

Fix a grading datum `G` of the black strands, the symmetrizer `d` (`G.degX i = 2 d_i`), and a
grading `ℒ` of the coefficient module `L` (an additive decomposition compatible with the
grading of `T̃^{(μ, μ*)}`). The degree of a cap diagram `a · cap s n v · b` is
`deg a + deg v + deg b`: the cap itself and the element `v` at its maximum contribute only the
degree of `v`.

**All defining relations are homogeneous** (`CupCap.freeProj_of_isRel`), so this is a grading
of `K̃^{λ⁺}_λ`:

* additivity in `v`, the top idempotent, a dot or a crossing passing below the cap, and the
  action of the diagrams at the maximum on `L`, are homogeneous for any grading datum;
* (max1) and (max2) are homogeneous when a black strand crossing all strands at the maximum has
  degree zero (`CupCap.CapBalanced`), which holds in Webster's setting since the strands at the
  maximum of `L_μ` have weight `μ - w₀μ = μ + μ*`.

The proof constructs the degree projections `freeProj q` of the free bimodule from those of
the coefficients `T̃^λ ⊗ (T̃^{λ⁺})ᵐᵒᵖ` and of `L`, shows that they kill the relations, and
descends them to the projections `capProj q` of `K̃^{λ⁺}_λ`. Their ranges form a direct sum
decomposition (`CupCap.capTildeDecomposition`), compatible with the gradings of `T̃^λ` from
the top and of `T̃^{λ⁺}` from the bottom. The violated diagrams form a homogeneous
sub-bimodule (`CupCap.capProj_mem_violated`), so `K^{λ⁺}_λ` is graded as well
(`CupCap.capDecomposition`).

All degrees are integers. Webster grades by `(1/D)ℤ` because of the red/red crossings; in
`K̃^{λ⁺}_λ` the only new diagrams are black strands crossing the legs of the cap, of degree
`d_i μ^i` and `d_i μ*^i`.

## Main definitions

* `CupCap.envGrade`: the grading of `T̃^λ ⊗ (T̃^{λ⁺})ᵐᵒᵖ`.
* `CupCap.freeProj`, `CupCap.capProj`, `CupCap.capQuotProj`: the degree projections of the free
  bimodule, of `K̃^{λ⁺}_λ` and of `K^{λ⁺}_λ`.
* `CupCap.CapBalanced` (in `CupCapGradedDegrees`) and `CupCap.IsGradedCoeff`: the hypotheses.
* `CupCap.capTildeGrade`, `CupCap.capGrade`: the gradings of `K̃^{λ⁺}_λ` and `K^{λ⁺}_λ`.

## Main results

* `CupCap.freeProj_of_isRel`, `CupCap.freeProj_relations`: the relations of Definition 7.15
  are homogeneous.
* `CupCap.isInternal_capTildeGrade`, `CupCap.isInternal_capGrade`.
* `CupCap.envMk_smul_mem_capTildeGrade`, `CupCap.envMk_smul_mem_capGrade`: the gradings are
  compatible with the actions of the top and bottom algebras.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite DirectSum Categorification.Graded
open scoped TensorProduct

/-! ### Projections onto the ranges of orthogonal projections -/

section Projections

variable {X : Type*} [AddCommGroup X] (P : ℤ → X →+ X)

variable {P} in
theorem apply_coeAddMonoidHom_of_projections
    (horth : ∀ q q' x, P q (P q' x) = if q = q' then P q' x else 0)
    (y : ⨁ q, (P q).range) (q : ℤ) :
    P q (DirectSum.coeAddMonoidHom (fun q => (P q).range) y) = y q := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | of q' z =>
    obtain ⟨z, hz⟩ := z
    obtain ⟨w, rfl⟩ := AddMonoidHom.mem_range.mp hz
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases h : q = q'
    · subst h
      rw [DirectSum.of_eq_same, horth, ite_eq_left rfl]
    · rw [DirectSum.of_eq_of_ne _ _ _ h, horth, ite_eq_right h]
      rfl
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', DirectSum.add_apply, AddSubgroup.coe_add]

/-- **Orthogonal projections whose ranges span give a direct sum decomposition.** -/
theorem isInternal_range_of_projections
    (horth : ∀ q q' x, P q (P q' x) = if q = q' then P q' x else 0)
    (hspan : ∀ x, x ∈ ⨆ q, (P q).range) : IsInternal fun q => (P q).range := by
  classical
  constructor
  · intro y y' h
    ext q
    rw [← apply_coeAddMonoidHom_of_projections horth, ← apply_coeAddMonoidHom_of_projections horth,
      h]
  · intro x
    refine AddSubgroup.iSup_induction _
      (C := fun x => ∃ y, DirectSum.coeAddMonoidHom (fun q => (P q).range) y = x)
      (hspan x) ?_ ?_ ?_
    · intro q x hx
      exact ⟨DirectSum.of (fun q => (P q).range) q ⟨x, hx⟩, DirectSum.coeAddMonoidHom_of _ _ _⟩
    · exact ⟨0, map_zero _⟩
    · rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
      exact ⟨y + y', map_add _ _ _⟩

end Projections

section Shift

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] (ℳ : ℤ → AddSubgroup M)
  (ℳ' : ℤ → AddSubgroup M') [Decomposition ℳ] [Decomposition ℳ']

/-- An additive map raising degrees by `r` shifts the homogeneous components by `r`. -/
theorem decompose_map_of_shift (f : M →+ M') (r : ℤ)
    (hf : ∀ p x, x ∈ ℳ p → f x ∈ ℳ' (p + r)) (x : M) (q : ℤ) :
    (decompose ℳ' (f x) q : M') = f (decompose ℳ x (q - r)) := by
  classical
  induction x using Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous p x =>
    by_cases h : p + r = q
    · subst h
      rw [decompose_of_mem_same _ (hf p x x.2), add_sub_cancel_right,
        decompose_of_mem_same _ x.2]
    · rw [decompose_of_mem_ne _ (hf p x x.2) h, decompose_of_mem_ne _ x.2 (by omega), map_zero]
  | add x y hx hy =>
    rw [map_add, decompose_add, DirectSum.add_apply, AddSubgroup.coe_add, hx, hy, decompose_add,
      DirectSum.add_apply, AddSubgroup.coe_add, map_add]

end Shift

/-! ### The grading of the coefficients -/

section Grading

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}
  (G : KLR.GradingDatum Q) (d : I → ℤ) (hd : ∀ i, G.degX i = 2 * d i)

set_option hygiene false in
local notation "m" => Multiset.card (stendhalWeight ℓ ν)
set_option hygiene false in
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
set_option hygiene false in
local notation "Gt" => stendhalGradingDatum Λ G d hd
set_option hygiene false in
local notation "Gb" => stendhalGradingDatum (plusLabels Λ Λc j hj) G d hd
set_option hygiene false in
local notation "Gc" => stendhalGradingDatum Λc G d hd
set_option hygiene false in
local notation "Tt" => StendhalAlgebra k Q Λ ν
set_option hygiene false in
local notation "Tb" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
set_option hygiene false in
local notation "Tc" => StendhalAlgebra k Q Λc ν₀
set_option hygiene false in
local notation "Ev" => Env k Q Λ Λc j hj ν ν₀

variable (Λ Λc j hj ν ν₀) in
/-- The grading of `T̃^λ ⊗ (T̃^{λ⁺})ᵐᵒᵖ`, the ring whose modules are `T̃^λ`–`T̃^{λ⁺}`
bimodules: the tensor product of the diagram gradings. -/
def envGrade : ℤ → Submodule k (Tt ⊗[k] Tbᵐᵒᵖ) :=
  tensorGrading (stendhalGrade (Gt) ν) (oppositeGrade (stendhalGrade (Gb) (ν + ν₀)))

noncomputable instance envDecomposition : Decomposition (envGrade Λ Λc j hj ν ν₀ G d hd) :=
  tensorDecomposition _ _

instance envGradedMonoid : SetLike.GradedMonoid (envGrade Λ Λc j hj ν ν₀ G d hd) :=
  tensorGrading_gradedMonoid _ _

theorem envMk_mem_envGrade {p r : ℤ} {a : Tt} {b : Tb} (ha : a ∈ stendhalGrade (Gt) ν p)
    (hb : b ∈ stendhalGrade (Gb) (ν + ν₀) r) :
    (Env.mk a b : Ev) ∈ envGrade Λ Λc j hj ν ν₀ G d hd (p + r) :=
  tmul_mem_tensorGrading ha (show b ∈ stendhalGrade (Gb) (ν + ν₀) r from hb)

set_option hygiene false in
local notation "𝓔" => envGrade Λ Λc j hj ν ν₀ G d hd

theorem envGrade_mul_mem {p r : ℤ} {c c' : Tt ⊗[k] Tbᵐᵒᵖ} (hc : c ∈ 𝓔 p) (hc' : c' ∈ 𝓔 r) :
    c * c' ∈ 𝓔 (p + r) :=
  (envGradedMonoid (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) G d hd).mul_mem
    hc hc'

theorem envGrade_one_mem : (1 : Tt ⊗[k] Tbᵐᵒᵖ) ∈ 𝓔 0 :=
  (envGradedMonoid (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) G d hd).one_mem

/-- An element of `T̃^λ ⊗ (T̃^{λ⁺})ᵐᵒᵖ`, as an element of the ring `Env`. -/
abbrev toEnv (c : Tt ⊗[k] Tbᵐᵒᵖ) : Ev := c

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  (ℒ : ℤ → AddSubgroup L) [Decomposition ℒ]

/-- The class of the cap generator `cap s n v` in `K̃^{λ⁺}_λ`. -/
def capMk (σ : CapIdx ℓ ν) (v : L) : CapTilde k Q Λ Λc j hj ν ν₀ L :=
  Submodule.Quotient.mk (gen σ v)

/-- The degree `q` part of a cap diagram with coefficient `c` and generator `cap σ v`, for
`c` in the degree `p` part of the coefficients: `c · cap σ v_{q - p}`. -/
def capPieceHom (q : ℤ) (σ : CapIdx ℓ ν) (v : L) (p : ℤ) :
    𝓔 p →+ CapTilde k Q Λ Λc j hj ν ν₀ L where
  toFun c := toEnv (c : Tt ⊗[k] Tbᵐᵒᵖ) • capMk σ (decompose ℒ v (q - p) : L)
  map_zero' := zero_smul _ _
  map_add' _ _ := add_smul _ _ _

/-- The degree `q` part of a cap diagram with coefficient `c` and generator `cap σ v`. -/
def capPiece (q : ℤ) (σ : CapIdx ℓ ν) (v : L) : Ev →+ CapTilde k Q Λ Λc j hj ν ν₀ L :=
  (DirectSum.toAddMonoid (capPieceHom G d hd ℒ q σ v)).comp
    (decomposeAddEquiv (𝓔)).toAddMonoidHom

/-- The degree `q` part, on the free bimodule. -/
def freeProj (q : ℤ) : FreeCap k Q Λ Λc j hj ν ν₀ L →+ CapTilde k Q Λ Λc j hj ν ν₀ L :=
  Finsupp.liftAddHom fun σv => capPiece G d hd ℒ q σv.1 σv.2

theorem freeProj_single_of_mem (q : ℤ) (σ : CapIdx ℓ ν) (v : L) {p : ℤ}
    {c : Tt ⊗[k] Tbᵐᵒᵖ} (hc : c ∈ 𝓔 p) :
    freeProj G d hd ℒ q (Finsupp.single (σ, v) (toEnv c)) =
      toEnv c • capMk σ (decompose ℒ v (q - p) : L) := by
  rw [freeProj, Finsupp.liftAddHom_apply_single]
  change DirectSum.toAddMonoid (capPieceHom G d hd ℒ q σ v) (decompose (𝓔) c) = _
  rw [decompose_of_mem _ hc, DirectSum.toAddMonoid_of]
  rfl

theorem freeProj_smul (q : ℤ) {p : ℤ} {c : Tt ⊗[k] Tbᵐᵒᵖ} (hc : c ∈ 𝓔 p)
    (z : FreeCap k Q Λ Λc j hj ν ν₀ L) :
    freeProj G d hd ℒ q (toEnv c • z) = toEnv c • freeProj G d hd ℒ (q - p) z := by
  induction z using Finsupp.induction_linear with
  | zero => rw [smul_zero, map_zero, map_zero, smul_zero]
  | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
  | single a c' =>
    obtain ⟨σ, v⟩ := a
    change freeProj G d hd ℒ q (toEnv c • Finsupp.single (σ, v) (toEnv c')) =
      toEnv c • freeProj G d hd ℒ (q - p) (Finsupp.single (σ, v) (toEnv c'))
    induction (c' : Tt ⊗[k] Tbᵐᵒᵖ) using Decomposition.inductionOn (𝓔) with
    | zero =>
      rw [show toEnv (0 : Tt ⊗[k] Tbᵐᵒᵖ) = 0 from rfl, Finsupp.single_zero, smul_zero,
        map_zero, map_zero, smul_zero]
    | @homogeneous r c' =>
      rw [Finsupp.smul_single, smul_eq_mul, freeProj_single_of_mem G d hd ℒ (q - p) σ v c'.2,
        smul_smul, sub_sub]
      exact freeProj_single_of_mem G d hd ℒ q σ v (envGrade_mul_mem G d hd hc c'.2)
    | add x y hx hy =>
      rw [show toEnv (x + y) = toEnv x + toEnv y from rfl, Finsupp.single_add, smul_add,
        map_add, hx, hy, map_add, smul_add]

/-! ### Consequences of the relations in `K̃^{λ⁺}_λ` -/

omit [Decomposition ℒ] in
theorem capMk_add (σ : CapIdx ℓ ν) (v w : L) :
    (capMk σ (v + w) : CapTilde k Q Λ Λc j hj ν ν₀ L) = capMk σ v + capMk σ w := by
  have h := mk_eq_zero_of_isRel (IsRel.add (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (j := j)
    (hj := hj) (ν₀ := ν₀) σ v w)
  rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_sub, sub_sub, sub_eq_zero] at h
  exact h

omit [Decomposition ℒ] in
theorem capMk_zero (σ : CapIdx ℓ ν) :
    (capMk σ (0 : L) : CapTilde k Q Λ Λc j hj ν ν₀ L) = 0 := by
  have h := capMk_add (k := k) (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀)
    σ (0 : L) 0
  rw [add_zero] at h
  exact left_eq_add.mp h

omit [Decomposition ℒ] in
theorem mk_single (σ : CapIdx ℓ ν) (v : L) (c : Ev) :
    (Submodule.Quotient.mk (Finsupp.single (σ, v) c) : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      c • capMk σ v := by
  rw [capMk, ← Submodule.Quotient.mk_smul, gen, Finsupp.smul_single, smul_eq_mul, mul_one]

omit [Decomposition ℒ] in
theorem mk_act (a : Tt) (b : Tb) (σ : CapIdx ℓ ν) (v : L) :
    (Submodule.Quotient.mk (act a b (gen σ v)) : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      Env.mk a b • capMk σ v :=
  Submodule.Quotient.mk_smul _ _ _

theorem freeProj_gen (q : ℤ) (σ : CapIdx ℓ ν) (v : L) :
    freeProj G d hd ℒ q (gen σ v : FreeCap k Q Λ Λc j hj ν ν₀ L) =
      (capMk σ (decompose ℒ v q : L) : CapTilde k Q Λ Λc j hj ν ν₀ L) := by
  have h := freeProj_single_of_mem G d hd ℒ q σ v
    (envGrade_one_mem (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν := ν) (ν₀ := ν₀) G d hd)
  rw [sub_zero] at h
  exact h.trans (one_smul _ _)

theorem freeProj_act_of_mem (q : ℤ) (σ : CapIdx ℓ ν) (v : L) {p r : ℤ} {a : Tt} {b : Tb}
    (ha : a ∈ stendhalGrade (Gt) ν p) (hb : b ∈ stendhalGrade (Gb) (ν + ν₀) r) :
    freeProj G d hd ℒ q (act a b (gen σ v : FreeCap k Q Λ Λc j hj ν ν₀ L)) =
      Env.mk a b • capMk σ (decompose ℒ v (q - (p + r)) : L) := by
  have h := freeProj_smul G d hd ℒ q (envMk_mem_envGrade G d hd ha hb) (gen σ v)
  rw [freeProj_gen] at h
  exact h

/-- An element of `Env`, as an element of `T̃^λ ⊗ (T̃^{λ⁺})ᵐᵒᵖ`. -/
abbrev ofEnv (c : Ev) : Tt ⊗[k] Tbᵐᵒᵖ := c

omit [Decomposition ℒ] in
theorem mk_eq_mk_of_isRel {z₁ z₂ : FreeCap k Q Λ Λc j hj ν ν₀ L}
    (h : IsRel k Q Λ Λc j hj ν ν₀ L (z₁ - z₂)) :
    (Submodule.Quotient.mk z₁ : CapTilde k Q Λ Λc j hj ν ν₀ L) = Submodule.Quotient.mk z₂ := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  exact mk_eq_zero_of_isRel h

/-- The idempotents at the top and the bottom of `cap(s, n, -)`. -/
def capIdem (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) : Ev :=
  Env.mk (topMap k Q Λ ν (KLRAlgebra.e s))
    (botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) 1))

omit [Decomposition ℒ] in
theorem capIdem_smul_capMk (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (w : L) :
    (capIdem s n : Ev) • (capMk (s, n) w : CapTilde k Q Λ Λc j hj ν ν₀ L) = capMk (s, n) w := by
  have hbox : (Submodule.Quotient.mk (gen (s, n) (op (cupMap k Q Λc ν₀ 1) • w)) :
      CapTilde k Q Λ Λc j hj ν ν₀ L) = Submodule.Quotient.mk (act 1
        (botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) 1))
        (gen (s, n) w)) :=
    mk_eq_mk_of_isRel (IsRel.box s n w 1)
  have hidem : (Submodule.Quotient.mk (act (topMap k Q Λ ν (KLRAlgebra.e s)) 1
      (gen (s, n) w)) : CapTilde k Q Λ Λc j hj ν ν₀ L) = Submodule.Quotient.mk (gen (s, n) w) :=
    mk_eq_mk_of_isRel (IsRel.idem s n w)
  rw [map_one, op_one, one_smul] at hbox
  rw [capIdem, show Env.mk (topMap k Q Λ ν (KLRAlgebra.e s))
      (botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) 1)) =
      Env.mk (topMap k Q Λ ν (KLRAlgebra.e s)) 1 *
        Env.mk 1 (botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) 1))
      by rw [Env.mk_mul_mk, mul_one, mul_one], mul_smul, capMk, ← Submodule.Quotient.mk_smul,
    ← act, ← hbox, ← Submodule.Quotient.mk_smul, ← act, hidem]

omit [Decomposition ℒ] in
/-- Coefficients of `cap(s, n, -)` may be multiplied by its idempotents. -/
theorem smul_capMk_eq (c : Ev) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (w : L) :
    c • (capMk (s, n) w : CapTilde k Q Λ Λc j hj ν ν₀ L) =
      (c * (capIdem s n : Ev)) • capMk (s, n) w :=
  by rw [mul_smul, capIdem_smul_capMk]

theorem capIdem_mem (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) :
    ofEnv ((capIdem s n : Ev)) ∈ 𝓔 0 := by
  have h := envMk_mem_envGrade G d hd
    (topMap_mem_grade G d hd (GradingDatum.e_mem_grade (Gt) s))
    (botMap_mem_grade G d hd (insertMap_mem_grade (j := j) (hj := hj) G d hd s
      (Nat.lt_succ_iff.1 n.2)
      (SetLike.GradedOne.one_mem (A := (Gc).grade (stendhalWeight 2 ν₀)))))
  rwa [add_zero] at h

theorem freeProj_single_eq_mul (q : ℤ) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (c : Tt ⊗[k] Tbᵐᵒᵖ) :
    freeProj G d hd ℒ q (Finsupp.single ((s, n), v) (toEnv c)) =
      freeProj G d hd ℒ q (Finsupp.single ((s, n), v) (toEnv c * (capIdem s n : Ev))) := by
  induction c using Decomposition.inductionOn (𝓔) with
  | zero => rw [show toEnv (0 : Tt ⊗[k] Tbᵐᵒᵖ) = 0 from rfl, zero_mul]
  | @homogeneous p c =>
    have hc := envGrade_mul_mem G d hd c.2 (capIdem_mem G d hd s n)
    rw [add_zero] at hc
    rw [freeProj_single_of_mem G d hd ℒ q (s, n) v c.2, smul_capMk_eq]
    exact (freeProj_single_of_mem G d hd ℒ q (s, n) v hc).symm
  | add x y hx hy =>
    rw [show toEnv (x + y) = toEnv x + toEnv y from rfl, Finsupp.single_add, map_add, hx, hy,
      add_mul, Finsupp.single_add, map_add]

/-- **The degree `q` part of a cap diagram** `a · cap(s, n, v) · b`, when the diagrams `a` and
`b` composed with the idempotents of the cap are homogeneous of total degree `δ`. -/
theorem freeProj_act_gen (q : ℤ) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (a : Tt) (b : Tb) {δ : ℤ} (h : ofEnv (Env.mk a b * (capIdem s n : Ev)) ∈ 𝓔 δ) :
    freeProj G d hd ℒ q (act a b (gen (s, n) v : FreeCap k Q Λ Λc j hj ν ν₀ L)) =
      Env.mk a b • capMk (s, n) (decompose ℒ v (q - δ) : L) := by
  rw [act, gen, Finsupp.smul_single, smul_eq_mul, mul_one,
    show Env.mk a b = toEnv (ofEnv (Env.mk a b)) from rfl, freeProj_single_eq_mul,
    show toEnv (ofEnv (Env.mk a b)) * (capIdem s n : Ev) =
      toEnv (ofEnv (Env.mk a b * (capIdem s n : Ev))) from rfl,
    freeProj_single_of_mem G d hd ℒ q (s, n) v h]
  exact (smul_capMk_eq _ _ _ _).symm

omit [Decomposition ℒ] in
theorem envMk_mul_capIdem (a : Tt) (b : Tb) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) :
    Env.mk a b * (capIdem s n : Ev) = Env.mk (a * topMap k Q Λ ν (KLRAlgebra.e s))
      (botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) 1) * b) :=
  Env.mk_mul_mk _ _ _ _

/-- The degree `q` part of `a · cap(s, n, v) · b`, when `a e_s` and `e b` are homogeneous, for
the idempotents `e_s` at the top and `e` at the bottom of the cap. -/
theorem freeProj_act_gen_of_mem (q : ℤ) (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    {a : Tt} {b : Tb} {p r : ℤ}
    (ha : a * topMap k Q Λ ν (KLRAlgebra.e s) ∈ stendhalGrade (Gt) ν p)
    (hb : botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) 1) * b ∈
      stendhalGrade (Gb) (ν + ν₀) r) :
    freeProj G d hd ℒ q (act a b (gen (s, n) v : FreeCap k Q Λ Λc j hj ν ν₀ L)) =
      Env.mk a b • capMk (s, n) (decompose ℒ v (q - (p + r)) : L) := by
  refine freeProj_act_gen G d hd ℒ q s n v a b ?_
  rw [envMk_mul_capIdem]
  exact envMk_mem_envGrade G d hd ha hb

omit [DecidableEq I] in
theorem ψw_mul_e_mem_grade {J : Type*} [DecidableEq J] {ν' : Multiset J}
    {Q' : J → J → MvPolynomial (Fin 2) k} (G' : GradingDatum Q') (ρ : List ℕ) (i : Seq ν') :
    (ψw ρ * KLRAlgebra.e i : KLRAlgebra k Q' ν') ∈ G'.grade ν' (G'.degW ρ i) := by
  have h := G'.ψw_mul_pol_mul_e_mem_grade ρ i (MvPolynomial.isWeightedHomogeneous_one (R := k) _)
  rwa [map_one, mul_one, add_zero] at h

/-- The bottom idempotent of `cap(s, n, -)` followed by `y` is homogeneous of degree `δ` if
each of its summands is. -/
theorem botIdem_mul_mem (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) {δ : ℤ}
    {y : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))}
    (h : ∀ t : Seq (stendhalWeight 2 ν₀), KLRAlgebra.e
      (insertSeq s n (Nat.lt_succ_iff.1 n.2) (Seq.map (cupColour j hj) t)) * y ∈
        (Gb).grade _ δ) :
    botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) 1) *
      botMap k Q Λ Λc j hj ν ν₀ y ∈ stendhalGrade (Gb) (ν + ν₀) δ := by
  rw [← map_mul, insertMap_one, eSum_insertSet, Finset.sum_mul]
  exact botMap_mem_grade G d hd (sum_mem fun t _ => h t)

theorem botIdem_mem (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) :
    botMap k Q Λ Λc j hj ν ν₀ (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) 1) * 1 ∈
      stendhalGrade (Gb) (ν + ν₀) 0 := by
  rw [mul_one]
  exact botMap_mem_grade G d hd (insertMap_mem_grade (j := j) (hj := hj) G d hd s _
    (SetLike.GradedOne.one_mem (A := (Gc).grade (stendhalWeight 2 ν₀))))

theorem topIdem_mem (s : Seq (stendhalWeight ℓ ν)) :
    (1 : Tt) * topMap k Q Λ ν (KLRAlgebra.e s) ∈ stendhalGrade (Gt) ν 0 := by
  rw [one_mul]
  exact topMap_mem_grade G d hd (GradingDatum.e_mem_grade (Gt) s)

/-- `L` is a graded right module over `T̃^{(μ, μ*)}`. -/
def IsGradedCoeff : Prop :=
  ∀ (r p : ℤ) (x : Tc), x ∈ stendhalGrade (Gc) ν₀ r → ∀ v ∈ ℒ p, op x • v ∈ ℒ (p + r)

omit [DecidableEq I] in
theorem insertSeq_congr (s : Seq (stendhalWeight ℓ ν)) {a b : ℕ} (h : a = b) (ha : a ≤ m)
    (hb : b ≤ m) (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) :
    insertSeq s a ha t = insertSeq s b hb t := by
  subst h; rfl

omit [Decomposition ℒ] in
theorem insertMap_zero (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) :
    insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s n hn 0 = 0 := by
  have h := insertMap_add (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s hn 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem one_mem_top : (1 : Tt) ∈ stendhalGrade (Gt) ν 0 :=
  SetLike.GradedOne.one_mem

theorem freeProj_box_of_mem (hℒ : IsGradedCoeff (Λc := Λc) (ν₀ := ν₀) G d hd ℒ) (q : ℤ)
    (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L) {r : ℤ}
    {x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)} (hx : x ∈ (Gc).grade _ r) :
    freeProj G d hd ℒ q ((gen (s, n) (op (cupMap k Q Λc ν₀ x) • v) :
      FreeCap k Q Λ Λc j hj ν ν₀ L) - act 1 (botMap k Q Λ Λc j hj ν ν₀
        (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) x)) (gen (s, n) v)) = 0 := by
  have hsh : (decompose ℒ (op (cupMap k Q Λc ν₀ x) • v) q : L) =
      op (cupMap k Q Λc ν₀ x) • (decompose ℒ v (q - r) : L) :=
    decompose_map_of_shift ℒ ℒ
      (AddMonoidHom.mk' (fun w : L => op (cupMap k Q Λc ν₀ x) • w) (smul_add _)) r
      (fun p w hw => hℒ r p _ (cupMap_mem_grade G d hd hx) w hw) v q
  have hb := botMap_mem_grade G d hd (insertMap_mem_grade (Λ := Λ) (j := j) (hj := hj) G d hd s
    (Nat.lt_succ_iff.1 n.2) hx)
  rw [map_sub, freeProj_gen, hsh, freeProj_act_of_mem G d hd ℒ q (s, n) v (one_mem_top G d hd) hb,
    zero_add, sub_eq_zero, ← mk_act, capMk]
  exact mk_eq_mk_of_isRel (IsRel.box s n _ x)

theorem freeProj_box (hℒ : IsGradedCoeff (Λc := Λc) (ν₀ := ν₀) G d hd ℒ) (q : ℤ)
    (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1)) (v : L)
    (x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)) :
    freeProj G d hd ℒ q ((gen (s, n) (op (cupMap k Q Λc ν₀ x) • v) :
      FreeCap k Q Λ Λc j hj ν ν₀ L) - act 1 (botMap k Q Λ Λc j hj ν ν₀
        (insertMap Q Λ Λc s n (Nat.lt_succ_iff.1 n.2) x)) (gen (s, n) v)) = 0 := by
  induction x using Decomposition.inductionOn ((Gc).grade (stendhalWeight 2 ν₀)) with
  | zero => exact freeProj_box_of_mem G d hd ℒ hℒ q s n v (r := 0) (zero_mem _)
  | @homogeneous r x => exact freeProj_box_of_mem G d hd ℒ hℒ q s n v x.2
  | add x y hx hy =>
    rw [map_sub, freeProj_gen] at hx hy ⊢
    rw [map_add, op_add, add_smul, decompose_add, DirectSum.add_apply, AddSubgroup.coe_add,
      capMk_add, insertMap_add, map_add, act, Env.mk_add_right, add_smul, map_add, ← act,
      ← act, add_sub_add_comm, hx, hy, add_zero]

/-- **The relations of `K̃^{λ⁺}_λ` are homogeneous**: every degree projection of the free
bimodule kills them. For (max1) and (max2) this uses the balance condition `CapBalanced`, and
for the action at the maximum that `L` is graded. -/
theorem freeProj_of_isRel (hbal : CapBalanced Λc ν₀ G d)
    (hℒ : IsGradedCoeff (Λc := Λc) (ν₀ := ν₀) G d hd ℒ)
    {z : FreeCap k Q Λ Λc j hj ν ν₀ L} (hz : IsRel k Q Λ Λc j hj ν ν₀ L z) (q : ℤ) :
    freeProj G d hd ℒ q z = 0 := by
  cases hz with
  | add σ v w =>
    rw [map_sub, map_sub, freeProj_gen, freeProj_gen, freeProj_gen, decompose_add,
      DirectSum.add_apply, AddSubgroup.coe_add, capMk_add, sub_sub, sub_self]
  | idem s n v =>
    have ha : topMap k Q Λ ν (KLRAlgebra.e s) * topMap k Q Λ ν (KLRAlgebra.e s) ∈
        stendhalGrade (Gt) ν 0 := by
      rw [← map_mul, KLRAlgebra.e_mul_self]
      exact topMap_mem_grade G d hd (GradingDatum.e_mem_grade (Gt) s)
    rw [map_sub, freeProj_act_gen_of_mem G d hd ℒ q s n v ha (botIdem_mem G d hd s n),
      freeProj_gen, add_zero, sub_zero, sub_eq_zero, ← mk_act, capMk]
    exact mk_eq_mk_of_isRel (IsRel.idem s n _)
  | box s n v x => exact freeProj_box G d hd ℒ hℒ q s n v x
  | dot s n v a =>
    have ha : topMap k Q Λ ν (KLRAlgebra.x a) * topMap k Q Λ ν (KLRAlgebra.e s) ∈
        stendhalGrade (Gt) ν ((Gt).dx a s) := by
      rw [← map_mul]
      exact topMap_mem_grade G d hd ((Gt).x_mul_e_mem_grade a s)
    have hb := botIdem_mul_mem (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) G d hd
      s n (δ := (Gt).dx a s)
      (y := KLRAlgebra.x (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a)) fun t => by
        rw [KLRAlgebra.e_mul_x, ← dx_dotPos G d hd s n _ a]
        exact (Gb).x_mul_e_mem_grade _ _
    rw [map_sub, freeProj_act_gen_of_mem G d hd ℒ q s n v ha (botIdem_mem G d hd s n),
      freeProj_act_gen_of_mem G d hd ℒ q s n v (topIdem_mem G d hd s) hb, add_zero, zero_add,
      sub_eq_zero, ← mk_act, ← mk_act]
    exact mk_eq_mk_of_isRel (IsRel.dot s n _ a)
  | cross s n v p hp =>
    have ha : topMap k Q Λ ν (KLRAlgebra.ψ p) * topMap k Q Λ ν (KLRAlgebra.e s) ∈
        stendhalGrade (Gt) ν ((Gt).dψ p s) := by
      rw [← map_mul]
      exact topMap_mem_grade G d hd ((Gt).ψ_mul_e_mem_grade' p s)
    have hb := botIdem_mul_mem (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) G d hd
      (sadj m p • s) n (δ := (Gt).dψ p s)
      (y := KLRAlgebra.ψ (crossPos n N p)) fun t => by
        rw [KLRAlgebra.e_mul_ψ, ← smul_insertSeq_old s _ _ hp, Multiset.card_map,
          KLRAlgebra.sadj_smul_smul,
          ← dψ_crossPos G d hd s _ _ hp]
        exact (Gb).ψ_mul_e_mem_grade' _ _
    rw [map_sub, freeProj_act_gen_of_mem G d hd ℒ q s n v ha (botIdem_mem G d hd s n),
      freeProj_act_gen_of_mem G d hd ℒ q (sadj m p • s) n v (topIdem_mem G d hd _) hb, add_zero,
      zero_add, sub_eq_zero, ← mk_act, ← mk_act]
    exact mk_eq_mk_of_isRel (IsRel.cross s n _ p hp)
  | «over» s n v i hn hi =>
    have hq : n.val - 1 + 1 ≤ m := by omega
    have hb := botIdem_mul_mem (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) G d hd
      s n (δ := 0) (y := underRight N (n - 1)) fun t => by
      rw [insertSeq_congr s (show n.val = n.val - 1 + 1 by omega) _ hq,
        ← underRight_mul_e_insertSeq, underRight, ← (hbal i).1,
        ← degW_underRight G d hd s (by omega) hi]
      exact ψw_mul_e_mem_grade (Gb) _ _
    rw [map_sub, freeProj_act_gen_of_mem G d hd ℒ q s n v (topIdem_mem G d hd s) hb,
      freeProj_act_of_mem G d hd ℒ q _ v (SetLike.algebraMap_mem_graded _ _)
        (SetLike.GradedOne.one_mem (A := stendhalGrade (Gb) (ν + ν₀))),
      add_zero, sub_eq_zero, ← mk_act, ← mk_act]
    exact mk_eq_mk_of_isRel (IsRel.over s n _ i hn hi)
  | under s n v i hn hi =>
    have hb := botIdem_mul_mem (Λ := Λ) (Λc := Λc) (j := j) (hj := hj) (ν₀ := ν₀) G d hd
      s n (δ := 0) (y := underLeft N n) fun t => by
      rw [← underLeft_mul_e_insertSeq, underLeft, ← (hbal i).2,
        ← degW_underLeft G d hd s (by omega) hi]
      exact ψw_mul_e_mem_grade (Gb) _ _
    rw [map_sub, freeProj_act_gen_of_mem G d hd ℒ q s n v (topIdem_mem G d hd s) hb,
      freeProj_gen, add_zero, sub_zero, sub_eq_zero, ← mk_act, capMk]
    exact mk_eq_mk_of_isRel (IsRel.under s n _ i hn hi)

theorem freeProj_relations (hbal : CapBalanced Λc ν₀ G d)
    (hℒ : IsGradedCoeff (Λc := Λc) (ν₀ := ν₀) G d hd ℒ) {z : FreeCap k Q Λ Λc j hj ν ν₀ L}
    (hz : z ∈ relations k Q Λ Λc j hj ν ν₀ L) : ∀ q, freeProj G d hd ℒ q z = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz => exact freeProj_of_isRel G d hd ℒ hbal hℒ hz
  | zero => exact fun q => map_zero _
  | add z z' _ _ hz hz' => exact fun q => by rw [map_add, hz, hz', add_zero]
  | smul c z _ hz =>
    intro q
    change freeProj G d hd ℒ q (toEnv (ofEnv c) • z) = 0
    induction ofEnv c using Decomposition.inductionOn (𝓔) with
    | zero => rw [show toEnv (0 : Tt ⊗[k] Tbᵐᵒᵖ) = 0 from rfl, zero_smul, map_zero]
    | @homogeneous p c => rw [freeProj_smul G d hd ℒ q c.2, hz, smul_zero]
    | add x y hx hy => rw [show toEnv (x + y) = toEnv x + toEnv y from rfl, add_smul, map_add,
        hx, hy, add_zero]

/-- **The degree `q` projection of `K̃^{λ⁺}_λ`**. -/
def capProj (hbal : CapBalanced Λc ν₀ G d) (hℒ : IsGradedCoeff (Λc := Λc) (ν₀ := ν₀) G d hd ℒ)
    (q : ℤ) : CapTilde k Q Λ Λc j hj ν ν₀ L →+ CapTilde k Q Λ Λc j hj ν ν₀ L :=
  QuotientAddGroup.lift (relations k Q Λ Λc j hj ν ν₀ L).toAddSubgroup (freeProj G d hd ℒ q)
    fun _ hz => freeProj_relations G d hd ℒ hbal hℒ hz q

section Projection

variable (hbal : CapBalanced Λc ν₀ G d) (hℒ : IsGradedCoeff (Λc := Λc) (ν₀ := ν₀) G d hd ℒ)

set_option hygiene false in
local notation "𝐏" => capProj (Λ := Λ) (j := j) (hj := hj) (ν := ν) G d hd ℒ hbal hℒ

theorem capProj_mk (q : ℤ) (z : FreeCap k Q Λ Λc j hj ν ν₀ L) :
    𝐏 q (Submodule.Quotient.mk z) = freeProj G d hd ℒ q z := rfl

theorem capProj_capMk (q : ℤ) (σ : CapIdx ℓ ν) (v : L) :
    𝐏 q (capMk σ v) = capMk σ (decompose ℒ v q : L) :=
  freeProj_gen G d hd ℒ q σ v

theorem capProj_smul (q : ℤ) {p : ℤ} {c : Tt ⊗[k] Tbᵐᵒᵖ} (hc : c ∈ 𝓔 p)
    (x : CapTilde k Q Λ Λc j hj ν ν₀ L) : 𝐏 q (toEnv c • x) = toEnv c • 𝐏 (q - p) x := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rw [← Submodule.Quotient.mk_smul, capProj_mk, capProj_mk, freeProj_smul G d hd ℒ q hc]

theorem capProj_single_of_mem (q : ℤ) (σ : CapIdx ℓ ν) {p r : ℤ} {c : Tt ⊗[k] Tbᵐᵒᵖ}
    (hc : c ∈ 𝓔 p) {v : L} (hv : v ∈ ℒ r) :
    𝐏 q (toEnv c • capMk σ v) = if q = p + r then toEnv c • capMk σ v else 0 := by
  rw [capProj_smul G d hd ℒ hbal hℒ q hc, capProj_capMk]
  by_cases h : q = p + r
  · rw [ite_eq_left h, show q - p = r by omega, decompose_of_mem_same _ hv]
  · rw [ite_eq_right h, decompose_of_mem_ne _ hv (by omega), capMk_zero, smul_zero]

/-- `K̃^{λ⁺}_λ` is spanned by the elements `c · cap(σ, v)` with `c` and `v` homogeneous. -/
theorem capTilde_induction {C : CapTilde k Q Λ Λc j hj ν ν₀ L → Prop} (h0 : C 0)
    (hadd : ∀ x y, C x → C y → C (x + y))
    (hgen : ∀ (σ : CapIdx ℓ ν) (p r : ℤ) (c : Tt ⊗[k] Tbᵐᵒᵖ), c ∈ 𝓔 p → ∀ v ∈ ℒ r,
      C (toEnv c • capMk σ v)) (x : CapTilde k Q Λ Λc j hj ν ν₀ L) : C x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
  induction z using Finsupp.induction_linear with
  | zero => exact h0
  | add z z' hz hz' => rw [Submodule.Quotient.mk_add]; exact hadd _ _ hz hz'
  | single a c =>
    obtain ⟨σ, v⟩ := a
    rw [mk_single]
    change C (toEnv (ofEnv c) • capMk σ v)
    induction ofEnv c using Decomposition.inductionOn (𝓔) with
    | zero => rw [show toEnv (0 : Tt ⊗[k] Tbᵐᵒᵖ) = 0 from rfl, zero_smul]; exact h0
    | add x y hx hy =>
      rw [show toEnv (x + y) = toEnv x + toEnv y from rfl, add_smul]; exact hadd _ _ hx hy
    | @homogeneous p c =>
      induction v using Decomposition.inductionOn ℒ with
      | zero => rw [capMk_zero, smul_zero]; exact h0
      | add v w hv hw => rw [capMk_add, smul_add]; exact hadd _ _ hv hw
      | @homogeneous r v => exact hgen σ p r c c.2 v v.2

theorem capProj_capProj (q q' : ℤ) (x : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    𝐏 q (𝐏 q' x) = if q = q' then 𝐏 q' x else 0 := by
  by_cases h : q = q'
  · subst h
    rw [ite_eq_left rfl]
    induction x using capTilde_induction G d hd ℒ with
    | h0 => rw [map_zero, map_zero]
    | hadd x y hx hy => rw [map_add, map_add, hx, hy]
    | hgen σ p r c hc v hv =>
      rw [capProj_single_of_mem G d hd ℒ hbal hℒ q σ hc hv]
      split_ifs with h'
      · rw [capProj_single_of_mem G d hd ℒ hbal hℒ q σ hc hv, ite_eq_left h']
      · rw [map_zero]
  · rw [ite_eq_right h]
    induction x using capTilde_induction G d hd ℒ with
    | h0 => rw [map_zero, map_zero]
    | hadd x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | hgen σ p r c hc v hv =>
      rw [capProj_single_of_mem G d hd ℒ hbal hℒ q' σ hc hv]
      split_ifs with h'
      · rw [capProj_single_of_mem G d hd ℒ hbal hℒ q σ hc hv, ite_eq_right (by omega)]
      · rw [map_zero]

theorem mem_iSup_capProj_range (x : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    x ∈ ⨆ q, (𝐏 q).range := by
  induction x using capTilde_induction G d hd ℒ with
  | h0 => exact zero_mem _
  | hadd x y hx hy => exact add_mem hx hy
  | hgen σ p r c hc v hv =>
    refine AddSubgroup.mem_iSup_of_mem (p + r) ⟨toEnv c • capMk σ v, ?_⟩
    rw [capProj_single_of_mem G d hd ℒ hbal hℒ _ σ hc hv, ite_eq_left rfl]

variable (Λ j hj ν) in
/-- **The grading of `K̃^{λ⁺}_λ`**: the degree of `a · cap(s, n, v) · b` is
`deg a + deg v + deg b`. -/
def capTildeGrade (q : ℤ) : AddSubgroup (CapTilde k Q Λ Λc j hj ν ν₀ L) := (𝐏 q).range

set_option hygiene false in
local notation "𝒦" => capTildeGrade Λ j hj ν G d hd ℒ hbal hℒ

theorem isInternal_capTildeGrade : IsInternal (𝒦) :=
  isInternal_range_of_projections _ (capProj_capProj G d hd ℒ hbal hℒ)
    (mem_iSup_capProj_range G d hd ℒ hbal hℒ)

noncomputable instance capTildeDecomposition : Decomposition (𝒦) :=
  (isInternal_capTildeGrade (Λ := Λ) (j := j) (hj := hj) (ν := ν) G d hd ℒ hbal
    hℒ).chooseDecomposition _

theorem mem_capTildeGrade_iff {q : ℤ} {x : CapTilde k Q Λ Λc j hj ν ν₀ L} :
    x ∈ 𝒦 q ↔ 𝐏 q x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [capProj_capProj, ite_eq_left rfl]
  · intro h
    exact ⟨x, h⟩

/-- The coefficient ring acts by graded maps. -/
theorem smul_mem_capTildeGrade {p r : ℤ} {c : Tt ⊗[k] Tbᵐᵒᵖ} (hc : c ∈ 𝓔 p)
    {x : CapTilde k Q Λ Λc j hj ν ν₀ L} (hx : x ∈ 𝒦 r) :
    toEnv c • x ∈ 𝒦 (p + r) := by
  rw [mem_capTildeGrade_iff] at hx ⊢
  rw [capProj_smul G d hd ℒ hbal hℒ _ hc, add_sub_cancel_left, hx]

theorem envMk_smul_mem_capTildeGrade {p r e : ℤ} {a : Tt} {b : Tb}
    (ha : a ∈ stendhalGrade (Gt) ν p) (hb : b ∈ stendhalGrade (Gb) (ν + ν₀) r)
    {x : CapTilde k Q Λ Λc j hj ν ν₀ L} (hx : x ∈ 𝒦 e) :
    Env.mk a b • x ∈ 𝒦 (p + r + e) :=
  smul_mem_capTildeGrade (Λ := Λ) (j := j) (hj := hj) (ν := ν) G d hd ℒ hbal hℒ
    (envMk_mem_envGrade G d hd ha hb) hx

theorem capMk_mem_capTildeGrade (σ : CapIdx ℓ ν) {r : ℤ} {v : L} (hv : v ∈ ℒ r) :
    (capMk σ v : CapTilde k Q Λ Λc j hj ν ν₀ L) ∈ 𝒦 r := by
  rw [mem_capTildeGrade_iff, capProj_capMk, decompose_of_mem_same _ hv]

/-! ### The grading of `K^{λ⁺}_λ` -/

omit [DecidableEq I] in
theorem decompose_mem_violatedIdeal {ℓ' : ℕ} {Λ' : Fin ℓ' → I →₀ ℕ} {ν' : Multiset I}
    (G' : GradingDatum (stendhalQ Q Λ')) [DecidableEq I]
    {a : StendhalAlgebra k Q Λ' ν'} (ha : a ∈ StendhalAlgebra.violatedIdeal k Q Λ' ν') (p : ℤ) :
    (decompose (stendhalGrade G' ν') a p : StendhalAlgebra k Q Λ' ν') ∈
      StendhalAlgebra.violatedIdeal k Q Λ' ν' :=
  Graded.decompose_mem_twoSidedSpan (𝒜 := stendhalGrade G' ν') (by
    rintro _ ⟨i, hi, _, rfl⟩
    exact ⟨0, e_mem_stendhalGrade G' ν' i hi⟩) ha p

omit [Decomposition ℒ] in
theorem envMk_sum_left {ι : Type*} (S : Finset ι) (f : ι → Tt) (b : Tb) :
    Env.mk (∑ i ∈ S, f i) b = ∑ i ∈ S, (Env.mk (f i) b : Ev) :=
  TensorProduct.sum_tmul _ _ _

omit [Decomposition ℒ] in
theorem envMk_sum_right {ι : Type*} (S : Finset ι) (a : Tt) (f : ι → Tb) :
    Env.mk a (∑ i ∈ S, f i) = ∑ i ∈ S, (Env.mk a (f i) : Ev) := by
  rw [Env.mk, show op (∑ i ∈ S, f i) = ∑ i ∈ S, op (f i) from
    map_sum (MulOpposite.opAddEquiv : Tb ≃+ Tbᵐᵒᵖ) f S]
  exact TensorProduct.tmul_sum _ _ _

theorem capProj_envMk_one_smul_mem {a : Tt} (ha : a ∈ StendhalAlgebra.violatedIdeal k Q Λ ν)
    (y : CapTilde k Q Λ Λc j hj ν ν₀ L) (q : ℤ) :
    𝐏 q (Env.mk a (1 : Tb) • y) ∈ violated k Q Λ Λc j hj ν ν₀ L := by
  classical
  rw [← sum_support_decompose (stendhalGrade (Gt) ν) a, envMk_sum_left, Finset.sum_smul,
    map_sum]
  refine sum_mem fun p _ => ?_
  rw [capProj_smul G d hd ℒ hbal hℒ q (envMk_mem_envGrade G d hd (SetLike.coe_mem _)
    (SetLike.GradedOne.one_mem (A := stendhalGrade (Gb) (ν + ν₀))))]
  exact Submodule.subset_span (Or.inl ⟨_, decompose_mem_violatedIdeal (Gt) ha p, _, rfl⟩)

theorem capProj_envMk_smul_one_mem {b : Tb}
    (hb : b ∈ StendhalAlgebra.violatedIdeal k Q (plusLabels Λ Λc j hj) (ν + ν₀))
    (y : CapTilde k Q Λ Λc j hj ν ν₀ L) (q : ℤ) :
    𝐏 q (Env.mk (1 : Tt) b • y) ∈ violated k Q Λ Λc j hj ν ν₀ L := by
  classical
  rw [← sum_support_decompose (stendhalGrade (Gb) (ν + ν₀)) b, envMk_sum_right,
    Finset.sum_smul, map_sum]
  refine sum_mem fun r _ => ?_
  rw [capProj_smul G d hd ℒ hbal hℒ q (envMk_mem_envGrade G d hd
    (SetLike.GradedOne.one_mem (A := stendhalGrade (Gt) ν)) (SetLike.coe_mem _))]
  exact Submodule.subset_span (Or.inr ⟨_, decompose_mem_violatedIdeal (Gb) hb r, _, rfl⟩)

theorem capProj_mem_violated {x : CapTilde k Q Λ Λc j hj ν ν₀ L}
    (hx : x ∈ violated k Q Λ Λc j hj ν ν₀ L) (q : ℤ) :
    𝐏 q x ∈ violated k Q Λ Λc j hj ν ν₀ L := by
  classical
  induction hx using Submodule.span_induction generalizing q with
  | mem z hz =>
    rcases hz with ⟨a, ha, y, rfl⟩ | ⟨b, hb, y, rfl⟩
    · exact capProj_envMk_one_smul_mem G d hd ℒ hbal hℒ ha y q
    · exact capProj_envMk_smul_one_mem G d hd ℒ hbal hℒ hb y q
  | zero => rw [map_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [map_add]; exact add_mem (hz q) (hz' q)
  | smul c z _ hz =>
    change 𝐏 q (toEnv (ofEnv c) • z) ∈ _
    induction ofEnv c using Decomposition.inductionOn (𝓔) with
    | zero =>
      rw [show toEnv (0 : Tt ⊗[k] Tbᵐᵒᵖ) = 0 from rfl, zero_smul, map_zero]; exact zero_mem _
    | @homogeneous p c =>
      rw [capProj_smul G d hd ℒ hbal hℒ q c.2]; exact Submodule.smul_mem _ _ (hz _)
    | add x y hx hy =>
      rw [show toEnv (x + y) = toEnv x + toEnv y from rfl, add_smul, map_add]
      exact add_mem hx hy

/-- **The degree `q` projection of `K^{λ⁺}_λ`**. -/
def capQuotProj (q : ℤ) : Cap k Q Λ Λc j hj ν ν₀ L →+ Cap k Q Λ Λc j hj ν ν₀ L :=
  QuotientAddGroup.lift (violated k Q Λ Λc j hj ν ν₀ L).toAddSubgroup
    ((violated k Q Λ Λc j hj ν ν₀ L).mkQ.toAddMonoidHom.comp (𝐏 q)) fun _ hz =>
      (Submodule.Quotient.mk_eq_zero _).2 (capProj_mem_violated G d hd ℒ hbal hℒ hz q)

set_option hygiene false in
local notation "𝐐" => capQuotProj (Λ := Λ) (j := j) (hj := hj) (ν := ν) G d hd ℒ hbal hℒ

theorem capQuotProj_mk (q : ℤ) (x : CapTilde k Q Λ Λc j hj ν ν₀ L) :
    𝐐 q (Submodule.Quotient.mk x) = Submodule.Quotient.mk (𝐏 q x) := rfl

theorem capQuotProj_capQuotProj (q q' : ℤ) (x : Cap k Q Λ Λc j hj ν ν₀ L) :
    𝐐 q (𝐐 q' x) = if q = q' then 𝐐 q' x else 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [capQuotProj_mk, capQuotProj_mk, capProj_capProj]
    split_ifs
    · rfl
    · exact Submodule.Quotient.mk_zero _

theorem mem_iSup_capQuotProj_range (x : Cap k Q Λ Λc j hj ν ν₀ L) :
    x ∈ ⨆ q, (𝐐 q).range := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    have h := AddSubgroup.map_le_iff_le_comap.2 (iSup_le fun q => ?_ :
      (⨆ q, (𝐏 q).range) ≤ (⨆ q, (𝐐 q).range).comap
        (violated k Q Λ Λc j hj ν ν₀ L).mkQ.toAddMonoidHom)
    · exact h ⟨x, mem_iSup_capProj_range G d hd ℒ hbal hℒ x, rfl⟩
    · rintro _ ⟨y, rfl⟩
      exact AddSubgroup.mem_iSup_of_mem q ⟨Submodule.Quotient.mk y, rfl⟩

variable (Λ j hj ν) in
/-- **The grading of `K^{λ⁺}_λ`**, induced by that of `K̃^{λ⁺}_λ`. -/
def capGrade (q : ℤ) : AddSubgroup (Cap k Q Λ Λc j hj ν ν₀ L) := (𝐐 q).range

set_option hygiene false in
local notation "𝒦'" => capGrade Λ j hj ν G d hd ℒ hbal hℒ

theorem isInternal_capGrade : IsInternal (𝒦') :=
  isInternal_range_of_projections _ (capQuotProj_capQuotProj G d hd ℒ hbal hℒ)
    (mem_iSup_capQuotProj_range G d hd ℒ hbal hℒ)

noncomputable instance capDecomposition : Decomposition (𝒦') :=
  (isInternal_capGrade (Λ := Λ) (j := j) (hj := hj) (ν := ν) G d hd ℒ hbal hℒ).chooseDecomposition _

theorem mk_mem_capGrade {q : ℤ} {x : CapTilde k Q Λ Λc j hj ν ν₀ L} (hx : x ∈ 𝒦 q) :
    (Submodule.Quotient.mk x : Cap k Q Λ Λc j hj ν ν₀ L) ∈ 𝒦' q := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem smul_mem_capGrade {p r : ℤ} {c : Tt ⊗[k] Tbᵐᵒᵖ} (hc : c ∈ 𝓔 p)
    {x : Cap k Q Λ Λc j hj ν ν₀ L} (hx : x ∈ 𝒦' r) : toEnv c • x ∈ 𝒦' (p + r) := by
  obtain ⟨y, rfl⟩ := hx
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    rw [capQuotProj_mk, ← Submodule.Quotient.mk_smul]
    exact mk_mem_capGrade G d hd ℒ hbal hℒ (smul_mem_capTildeGrade (Λ := Λ) (j := j) (hj := hj)
      (ν := ν) G d hd ℒ hbal hℒ hc ⟨y, rfl⟩)

theorem envMk_smul_mem_capGrade {p r e : ℤ} {a : Tt} {b : Tb}
    (ha : a ∈ stendhalGrade (Gt) ν p) (hb : b ∈ stendhalGrade (Gb) (ν + ν₀) r)
    {x : Cap k Q Λ Λc j hj ν ν₀ L} (hx : x ∈ 𝒦' e) : Env.mk a b • x ∈ 𝒦' (p + r + e) :=
  smul_mem_capGrade G d hd ℒ hbal hℒ (envMk_mem_envGrade G d hd ha hb) hx

end Projection

end Grading

end Categorification.Stendhal.CupCap
