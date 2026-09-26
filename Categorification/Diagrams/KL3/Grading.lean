/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Presentation

/-!
# The grading of `U`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.1,
Definition 3.1: the 2-morphisms of `U` are graded, with the degrees of the generators listed in
item ii) (`deg`, `Categorification.Diagrams.KL3.Basic`), and the relations are homogeneous.

This file checks that every defining relation of `pres RD k` is homogeneous for `deg`
(`pres_isHomogeneous`), so that the library's grading theory applies: every Hom-space of `U`
is the direct sum of its homogeneous components (`Presentation.isInternal_homDeg`), i.e. the
2-morphisms of degree `t - t'` are KL III's `Hom_U(x{t}, y{t'})`. The degrees of the relations
are:

* zigzags, cyclicity of dots and crossings, sideways double crossings: `0`, `i·i`, `-i·j`, `0`;
* bubbles: a clockwise (counterclockwise) bubble with `m` dots has degree `2 d_i (m + 1 ∓ n)`;
* curls: `∓2 d_i n` (right/left curl); decompositions of `1_{EF}`, `1_{FE}`: `0`;
* `R(ν)`-relations: the degrees of the KLR relations with `deg x = i·i`, `deg ψ = -i·j`.

The homogeneity of the relations involving fake bubbles checks that the infinite Grassmannian
recursion (`grassInv`) produces bubbles of the degrees predicted by KL III.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-- The degree of the generator of shape `g` with rightmost region `ν`. -/
def sdeg (ν : X) : Shape I → ℤ
  | .dot l => C.dot l.2 l.2
  | .cross _ i j => -C.dot i j
  | .cup l => di C l.2 * (1 - sgn l.1 * RD.pair (RD.iY l.2) ν)
  | .cap l => di C l.2 * (1 + sgn l.1 * RD.pair (RD.iY l.2) ν)

theorem deg_gen (ν : X) (g : Shape I) : deg RD (g.gen RD ν) = sdeg RD ν g := by
  cases g with
  | dot l => rfl
  | cross ε i j => rfl
  | cap l => rfl
  | cup l =>
    show di C l.2 * (1 - sgn l.1 * RD.pair (RD.iY l.2) (sh RD l + (sh RD l.dual + ν))) = _
    rw [← add_assoc, sh_add_sh_dual, zero_add]; rfl

theorem degree_mkD (μ : X) {t t' : List (Letter I)} (ls : List (LayerData I))
    (h : SChain t ls t') :
    Diagram.degree (deg RD) (mkD RD μ ls h) = (ls.map fun x => sdeg RD (wt RD μ x.2.2) x.2.1).sum := by
  simp only [mkD, Diagram.degree_mk, layList, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  exact deg_gen RD _ _

@[simp] theorem pair_sh (i : I) (l : Letter I) (x : X) :
    RD.pair (RD.iY i) (sh RD l + x) = sgn l.1 * A C i l.2 + RD.pair (RD.iY i) x := by
  simp [sh, map_add, map_zsmul, RD.pair_iY_iX_eq_A]

/-- `c_{±i,λ} = (i·i/2)(1 ± ⟨i,λ⟩)` (KL III eq. (2.19), label `eq_cpm_lambda`); `ε = true` is `+`. -/
def cpm (ε : Bool) (i : I) (lam : X) : ℤ := di C i * (1 + sgn ε * RD.pair (RD.iY i) lam)

/-- KL III Definition 3.1 ii): the cup `1_λ → F E 1_λ` has degree `c_{+i,λ}`. -/
theorem deg_cup_FE (i : I) (lam : X) :
    deg RD (.cup ⟨dn i, sh RD (up i) + lam⟩) = cpm RD true i lam := by
  simp only [deg, cpm, pair_sh, A_self, sgn_true, sgn_false, Letter.dual_mk]; ring

/-- KL III Definition 3.1 ii): the cup `1_λ → E F 1_λ` has degree `c_{-i,λ}`. -/
theorem deg_cup_EF (i : I) (lam : X) :
    deg RD (.cup ⟨up i, sh RD (dn i) + lam⟩) = cpm RD false i lam := by
  simp only [deg, cpm, pair_sh, A_self, sgn_true, sgn_false, Letter.dual_mk]; ring

/-- KL III Definition 3.1 ii): the cap `F E 1_λ → 1_λ` has degree `c_{+i,λ}`. -/
theorem deg_cap_FE (i : I) (lam : X) : deg RD (.cap ⟨up i, lam⟩) = cpm RD true i lam := rfl

/-- KL III Definition 3.1 ii): the cap `E F 1_λ → 1_λ` has degree `c_{-i,λ}`. -/
theorem deg_cap_EF (i : I) (lam : X) : deg RD (.cap ⟨dn i, lam⟩) = cpm RD false i lam := rfl

/-- The facts about the Cartan datum used to compute degrees. -/
theorem cartan_facts (i j : I) :
    di C i * A C i j = C.dot i j ∧ C.dot j i = C.dot i j ∧ 2 * di C i = C.dot i i ∧ A C i i = 2 :=
  ⟨di_mul_A C i j, C.symm j i, two_mul_di C i, A_self C i⟩

/-- Unfold the degree of a normal-form diagram into integer arithmetic. -/
macro "degree_tac" : tactic => `(tactic| (
  simp only [degree_mkD, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sdeg, wt_cons,
    wt_nil, pair_sh, Letter.dual_mk, sgn_true, sgn_false, List.map_append, List.sum_append,
    List.map_replicate, List.sum_replicate, smul_eq_mul, nsmul_eq_mul, A_self, ip]))

variable {RD}

theorem degree_downDot (i : I) (μ : X) : Diagram.degree (deg RD) (downDot RD i μ) = C.dot i i := by
  simp [downDot, degree_mkD, sdeg]

theorem degree_rotDotR (i : I) (μ : X) : Diagram.degree (deg RD) (rotDotR RD i μ) = C.dot i i := by
  unfold rotDotR; degree_tac
  rw [← two_mul_di C i]; ring

theorem degree_rotDotL (i : I) (μ : X) : Diagram.degree (deg RD) (rotDotL RD i μ) = C.dot i i := by
  unfold rotDotL; degree_tac
  rw [← two_mul_di C i]; ring

theorem degree_downCross (j i : I) (μ : X) :
    Diagram.degree (deg RD) (downCross RD j i μ) = -C.dot j i := by
  simp [downCross, degree_mkD, sdeg]

theorem degree_rotCrossR (j i : I) (μ : X) :
    Diagram.degree (deg RD) (rotCrossR RD j i μ) = -C.dot j i := by
  unfold rotCrossR; degree_tac
  obtain ⟨h₁, h₂, -, h₄⟩ := cartan_facts (C := C) i j
  obtain ⟨h₁', -, -, h₄'⟩ := cartan_facts (C := C) j i
  linarith

theorem degree_rotCrossL (j i : I) (μ : X) :
    Diagram.degree (deg RD) (rotCrossL RD j i μ) = -C.dot j i := by
  unfold rotCrossL; degree_tac
  obtain ⟨h₁, h₂, -, h₄⟩ := cartan_facts (C := C) i j
  obtain ⟨h₁', -, -, h₄'⟩ := cartan_facts (C := C) j i
  linarith

theorem degree_crossl (i j : I) (μ : X) : Diagram.degree (deg RD) (crossl RD i j μ) = 0 := by
  unfold crossl; degree_tac
  obtain ⟨h₁, -, -, h₄⟩ := cartan_facts (C := C) j i
  linarith

theorem degree_crossr (i j : I) (μ : X) : Diagram.degree (deg RD) (crossr RD i j μ) = 0 := by
  unfold crossr; degree_tac
  obtain ⟨h₁, h₂, -, h₄⟩ := cartan_facts (C := C) j i
  linarith

theorem degree_dots (μ : X) (u : List (Letter I)) (l : Letter I) (v : List (Letter I)) (m : ℕ) :
    Diagram.degree (deg RD) (dots RD μ u l v m) = m * C.dot l.2 l.2 := by
  unfold dots; degree_tac

theorem degree_cwReal (lam : X) (i : I) (m : ℕ) :
    Diagram.degree (deg RD) (cwReal RD lam i m) = 2 * di C i * (m + 1 - ip RD i lam) := by
  unfold cwReal; degree_tac
  rw [← two_mul_di C i]; ring

theorem degree_ccwReal (lam : X) (i : I) (m : ℕ) :
    Diagram.degree (deg RD) (ccwReal RD lam i m) = 2 * di C i * (m + 1 + ip RD i lam) := by
  unfold ccwReal; degree_tac
  rw [← two_mul_di C i]; ring

theorem degree_curlR (i : I) (lam : X) :
    Diagram.degree (deg RD) (curlR RD i lam) = -(2 * di C i * ip RD i lam) := by
  unfold curlR; degree_tac
  rw [← two_mul_di C i]; ring

theorem degree_curlL (i : I) (μ : X) :
    Diagram.degree (deg RD) (curlL RD i μ) = 2 * di C i * ip RD i (wt RD μ [up i]) := by
  unfold curlL; degree_tac
  rw [← two_mul_di C i]; ring

theorem degree_dotCapEF (lam : X) (i : I) (m : ℕ) :
    Diagram.degree (deg RD) (dotCapEF RD lam i m) =
      m * C.dot i i + di C i * (1 - ip RD i lam) := by
  unfold dotCapEF; degree_tac; ring

theorem degree_cupDotEF (lam : X) (i : I) (m : ℕ) :
    Diagram.degree (deg RD) (cupDotEF RD lam i m) =
      di C i * (1 - ip RD i lam) + m * C.dot i i := by
  unfold cupDotEF; degree_tac; ring

theorem degree_dotCapFE (lam : X) (i : I) (m : ℕ) :
    Diagram.degree (deg RD) (dotCapFE RD lam i m) =
      m * C.dot i i + di C i * (1 + ip RD i lam) := by
  unfold dotCapFE; degree_tac; ring

theorem degree_cupDotFE (lam : X) (i : I) (m : ℕ) :
    Diagram.degree (deg RD) (cupDotFE RD lam i m) =
      di C i * (1 + ip RD i lam) + m * C.dot i i := by
  unfold cupDotFE; degree_tac; ring

/-! ### Homogeneous linear combinations -/

variable {k}

local notation "HD" => LinDiagram.homDeg k (deg RD)

theorem end_mul_mem {a : Obj (psig RD)} {f g : End (Free.of k a)} {d e : ℤ} (hf : f ∈ HD a a d)
    (hg : g ∈ HD a a e) : f * g ∈ HD a a (d + e) := by
  rw [add_comm]; exact LinDiagram.comp_mem_homDeg hg hf

theorem grassInv_mem {a : Obj (psig RD)} (c : ℕ → End (Free.of k a)) (e : ℤ)
    (hc : ∀ n : ℕ, c n ∈ HD a a (e * n)) : ∀ n : ℕ, grassInv c n ∈ HD a a (e * n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [grassInv_zero]; simpa using LinDiagram.id_mem_homDeg (R := k) (deg := deg RD) a
    | succ n =>
      rw [grassInv_succ]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun t _ => ?_)
      have h := end_mul_mem (hc (t.1 + 1)) (ih (n - t.1) (by omega))
      have ht : t.1 ≤ n := Nat.lt_succ_iff.mp t.2
      convert h using 2
      push_cast [Nat.cast_sub ht]
      ring

theorem cwR_mem (lam : X) (i : I) (m : ℤ) :
    cwR RD k lam i m ∈ HD _ _ (2 * di C i * (m + 1 - ip RD i lam)) := by
  unfold cwR
  split_ifs with h
  · exact LinDiagram.of_mem_homDeg' (by rw [degree_cwReal, Int.toNat_of_nonneg h])
  · exact Submodule.zero_mem _

theorem ccwR_mem (lam : X) (i : I) (m : ℤ) :
    ccwR RD k lam i m ∈ HD _ _ (2 * di C i * (m + 1 + ip RD i lam)) := by
  unfold ccwR
  split_ifs with h
  · exact LinDiagram.of_mem_homDeg' (by rw [degree_ccwReal, Int.toNat_of_nonneg h])
  · exact Submodule.zero_mem _

/-- The fake clockwise bubbles have the degree predicted by KL III. -/
theorem cwL_mem (lam : X) (i : I) (m : ℤ) :
    cwL RD k lam i m ∈ HD _ _ (2 * di C i * (m + 1 - ip RD i lam)) := by
  unfold cwL
  split_ifs with h h'
  · exact LinDiagram.of_mem_homDeg' (by rw [degree_cwReal, Int.toNat_of_nonneg h])
  · have := grassInv_mem (fun a => ccwR RD k lam i (-ip RD i lam - 1 + a)) (2 * di C i)
      (fun a => by
        convert ccwR_mem (k := k) lam i (-ip RD i lam - 1 + a) using 2
        ring) (m + 1 - ip RD i lam).toNat
    rwa [Int.toNat_of_nonneg h'] at this
  · exact Submodule.zero_mem _

/-- The fake counterclockwise bubbles have the degree predicted by KL III. -/
theorem ccwL_mem (lam : X) (i : I) (m : ℤ) :
    ccwL RD k lam i m ∈ HD _ _ (2 * di C i * (m + 1 + ip RD i lam)) := by
  unfold ccwL
  split_ifs with h h'
  · exact LinDiagram.of_mem_homDeg' (by rw [degree_ccwReal, Int.toNat_of_nonneg h])
  · have := grassInv_mem (fun b => cwR RD k lam i (ip RD i lam - 1 + b)) (2 * di C i)
      (fun b => by
        convert cwR_mem (k := k) lam i (ip RD i lam - 1 + b) using 2
        ring) (m + 1 + ip RD i lam).toNat
    rwa [Int.toNat_of_nonneg h'] at this
  · exact Submodule.zero_mem _

theorem bubR_mem (lam : X) (t : List (Letter I)) {b : LEnd RD k (ob RD lam [])} {d : ℤ}
    (hb : b ∈ HD _ _ d) : bubR RD k lam t b ∈ HD _ _ d :=
  LinDiagram.cast_mem_homDeg (LinDiagram.whisker_mem_homDeg hb _ _ _) _ _

theorem bubL_mem (μ : X) (t : List (Letter I)) {b : LEnd RD k (ob RD (wt RD μ t) [])} {d : ℤ}
    (hb : b ∈ HD _ _ d) : bubL RD k μ t b ∈ HD _ _ d :=
  LinDiagram.cast_mem_homDeg (LinDiagram.whisker_mem_homDeg hb _ _ _) _ _

theorem curlRHS_mem (i : I) (lam : X) :
    curlRHS RD k i lam ∈ HD _ _ (-(2 * di C i * ip RD i lam)) := by
  unfold curlRHS
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun f hf => ?_)
  have hf' : (f : ℤ) ≤ -ip RD i lam := by
    have := Finset.mem_range.mp hf; omega
  have h := LinDiagram.comp_mem_homDeg (bubR_mem lam [up i] (cwL_mem (k := k) lam i (ip RD i lam - 1 + f)))
    (LinDiagram.of_mem_homDeg (R := k) (deg := deg RD) (dots RD lam [] (up i) [] (-ip RD i lam - f).toNat))
  have e : 2 * di C i * (ip RD i lam - 1 + f + 1 - ip RD i lam) +
      Diagram.degree (deg RD) (dots RD lam [] (up i) [] (-ip RD i lam - f).toNat) =
      -(2 * di C i * ip RD i lam) := by
    rw [degree_dots, Int.toNat_of_nonneg (by omega), ← two_mul_di C i]; ring
  rw [e] at h; exact h

theorem curlLHS_mem (i : I) (μ : X) :
    curlLHS RD k i μ ∈ HD _ _ (2 * di C i * ip RD i (wt RD μ [up i])) := by
  unfold curlLHS
  refine Submodule.sum_mem _ fun g hg => ?_
  have hg' : (g : ℤ) ≤ ip RD i (wt RD μ [up i]) := by
    have := Finset.mem_range.mp hg; omega
  have h := LinDiagram.comp_mem_homDeg
    (bubL_mem μ [up i] (ccwL_mem (k := k) (wt RD μ [up i]) i (-ip RD i (wt RD μ [up i]) - 1 + g)))
    (LinDiagram.of_mem_homDeg (R := k) (deg := deg RD)
      (dots RD μ [] (up i) [] (ip RD i (wt RD μ [up i]) - g).toNat))
  have e : 2 * di C i * (-ip RD i (wt RD μ [up i]) - 1 + g + 1 + ip RD i (wt RD μ [up i])) +
      Diagram.degree (deg RD) (dots RD μ [] (up i) [] (ip RD i (wt RD μ [up i]) - g).toNat) =
      2 * di C i * ip RD i (wt RD μ [up i]) := by
    rw [degree_dots, Int.toNat_of_nonneg (by omega), ← two_mul_di C i]; ring
  rw [e] at h; exact h

theorem decompEFSum_mem (i : I) (lam : X) : decompEFSum RD k i lam ∈ HD _ _ 0 := by
  unfold decompEFSum
  refine Submodule.sum_mem _ fun f hf => Submodule.sum_mem _ fun g hg => ?_
  have hf' := Finset.mem_range.mp hf
  have hg' := Finset.mem_range.mp hg
  have h := LinDiagram.comp_mem_homDeg
    (LinDiagram.of_mem_homDeg (R := k) (deg := deg RD) (dotCapEF RD lam i (f - g)))
    (LinDiagram.comp_mem_homDeg (ccwL_mem (k := k) lam i (-ip RD i lam - 1 + g))
      (LinDiagram.of_mem_homDeg (R := k) (deg := deg RD)
        (cupDotEF RD lam i ((ip RD i lam).toNat - 1 - f))))
  have e : Diagram.degree (deg RD) (dotCapEF RD lam i (f - g)) +
      (2 * di C i * (-ip RD i lam - 1 + g + 1 + ip RD i lam) +
        Diagram.degree (deg RD) (cupDotEF RD lam i ((ip RD i lam).toNat - 1 - f))) = 0 := by
    have hn : (0 : ℤ) ≤ ip RD i lam := by omega
    rw [degree_dotCapEF, degree_cupDotEF, ← two_mul_di C i]
    push_cast [Nat.cast_sub (show g ≤ f by omega),
      Nat.cast_sub (show f ≤ (ip RD i lam).toNat - 1 by omega),
      Nat.cast_sub (show 1 ≤ (ip RD i lam).toNat by omega), Int.toNat_of_nonneg hn]
    ring
  rw [e] at h; exact h

theorem decompFESum_mem (i : I) (lam : X) : decompFESum RD k i lam ∈ HD _ _ 0 := by
  unfold decompFESum
  refine Submodule.sum_mem _ fun f hf => Submodule.sum_mem _ fun g hg => ?_
  have hf' := Finset.mem_range.mp hf
  have hg' := Finset.mem_range.mp hg
  have h := LinDiagram.comp_mem_homDeg
    (LinDiagram.of_mem_homDeg (R := k) (deg := deg RD) (dotCapFE RD lam i (f - g)))
    (LinDiagram.comp_mem_homDeg (cwL_mem (k := k) lam i (ip RD i lam - 1 + g))
      (LinDiagram.of_mem_homDeg (R := k) (deg := deg RD)
        (cupDotFE RD lam i ((-ip RD i lam).toNat - 1 - f))))
  have e : Diagram.degree (deg RD) (dotCapFE RD lam i (f - g)) +
      (2 * di C i * (ip RD i lam - 1 + g + 1 - ip RD i lam) +
        Diagram.degree (deg RD) (cupDotFE RD lam i ((-ip RD i lam).toNat - 1 - f))) = 0 := by
    have hn : (0 : ℤ) ≤ -ip RD i lam := by omega
    rw [degree_dotCapFE, degree_cupDotFE, ← two_mul_di C i]
    push_cast [Nat.cast_sub (show g ≤ f by omega),
      Nat.cast_sub (show f ≤ (-ip RD i lam).toNat - 1 by omega),
      Nat.cast_sub (show 1 ≤ (-ip RD i lam).toNat by omega), Int.toNat_of_nonneg hn]
    ring
  rw [e] at h; exact h

/-! ### The `R(ν)`-relations -/

section KLR

open KLR.Diagram MvPolynomial

variable {S : Signature} (deg' : S.Gen → ℤ)

local notation "HD'" => LinDiagram.homDeg k deg'

theorem end_mul_mem' {a : Obj S} {f g : End (Free.of k a)} {d e : ℤ} (hf : f ∈ HD' a a d)
    (hg : g ∈ HD' a a e) : f * g ∈ HD' a a (d + e) := by
  rw [add_comm]; exact LinDiagram.comp_mem_homDeg hg hf

theorem pow_mem' {a : Obj S} {f : End (Free.of k a)} {d : ℤ} (hf : f ∈ HD' a a d) :
    ∀ m : ℕ, f ^ m ∈ HD' a a (m * d)
  | 0 => by simpa using LinDiagram.id_mem_homDeg (R := k) (deg := deg') a
  | m + 1 => by
    rw [pow_succ]
    convert end_mul_mem' deg' (pow_mem' hf m) hf using 2
    push_cast; ring

theorem prod_ofFn_mem' {a : Obj S} : ∀ {n : ℕ} (f : Fin n → End (Free.of k a)) (d : Fin n → ℤ),
    (∀ i, f i ∈ HD' a a (d i)) → (List.ofFn f).prod ∈ HD' a a (∑ i, d i)
  | 0, f, d, _ => by simpa using LinDiagram.id_mem_homDeg (R := k) (deg := deg') a
  | n + 1, f, d, hf => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact end_mul_mem' deg' (hf 0) (prod_ofFn_mem' _ _ fun i => hf i.succ)

/-- A weighted homogeneous polynomial evaluated at homogeneous endomorphisms is homogeneous. -/
theorem ncEval_mem_homDeg {a : Obj S} {n : ℕ} (y : Fin n → End (Free.of k a)) (w : Fin n → ℤ)
    (hy : ∀ i, y i ∈ HD' a a (w i)) (p : MvPolynomial (Fin n) k) (e : ℤ)
    (hp : p.IsWeightedHomogeneous w e) : KLR.ncEval y p ∈ HD' a a e := by
  unfold KLR.ncEval Finsupp.sum
  refine Submodule.sum_mem _ fun s hs => ?_
  have hw : Finsupp.weight w s = e := hp (Finsupp.mem_support_iff.mp hs)
  beta_reduce
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have := prod_ofFn_mem' deg' (fun t => y t ^ s t) (fun t => s t * w t)
    (fun t => pow_mem' deg' (hy t) (s t))
  convert this using 1
  rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [smul_eq_mul]

/-- The KLR degree: `x` on a strand `i` has degree `i·i`, a crossing of `i`, `j` degree
`-i·j`. -/
def degK : (sig I).Gen → ℤ
  | .dot c => C.dot c c
  | .cross c d => -C.dot c d

local notation "HK" => LinDiagram.homDeg k (degK (I := I) (C := C))

theorem degK_mem {a b : Obj (sig I)} (f : a ⟶ b) {d : ℤ}
    (h : Diagram.degree (degK (I := I) (C := C)) f = d) :
    (LinDiagram.of f : LinDiagram k a b) ∈ HK a b d :=
  LinDiagram.of_mem_homDeg' h

/-- Unfold the KLR degree of an explicit KLR diagram. -/
macro "degK_tac" : tactic => `(tactic| (
  simp [Diagram.degree, Diagram.layers_comp, KLR.Diagram.layers_dl, KLR.Diagram.lay, degK]))

theorem klQ2_isWeightedHomogeneous {c d : I} (h : c ≠ d) :
    (KLR.klQ2 k C c d).IsWeightedHomogeneous ![C.dot c c, C.dot d d] (-2 * C.dot c d) := by
  unfold KLR.klQ2
  split_ifs with h0
  · rw [h0, mul_zero]; exact isWeightedHomogeneous_one (R := k) ![C.dot c c, C.dot d d]
  · have h₁ := C.dij_mul h
    have h₂ := C.dij_mul (Ne.symm h)
    refine IsWeightedHomogeneous.add ?_ ?_
    · convert (isWeightedHomogeneous_X k ![C.dot c c, C.dot d d] 0).pow (C.dij c d) using 1
      simp [h₁]
    · convert (isWeightedHomogeneous_X k ![C.dot c c, C.dot d d] 1).pow (C.dij d c) using 1
      simp [h₂, C.symm d c]

theorem qbar_klQ2_isWeightedHomogeneous {c d : I} (h : c ≠ d) :
    (KLR.qbar (KLR.klQ2 k C c d)).IsWeightedHomogeneous ![C.dot c c, C.dot d d, C.dot c c]
      (-2 * C.dot c d - C.dot c c) := by
  unfold KLR.klQ2
  split_ifs with h0
  · rw [KLR.qbar_one]; exact isWeightedHomogeneous_zero _ _ _
  · rw [KLR.qbar_X_pow_add_X_pow]
    have h₁ := C.dij_mul h
    have hpos := C.dij_pos h h0
    refine IsWeightedHomogeneous.sum _ _ _ fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    convert ((isWeightedHomogeneous_X k ![C.dot c c, C.dot d d, C.dot c c] 0).pow t).mul
      ((isWeightedHomogeneous_X k ![C.dot c c, C.dot d d, C.dot c c] 2).pow (C.dij c d - 1 - t))
      using 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      smul_eq_mul, nsmul_eq_mul]
    push_cast [Nat.cast_sub (show t ≤ C.dij c d - 1 by omega),
      Nat.cast_sub (show 1 ≤ C.dij c d by omega)]
    linear_combination -h₁

/-- The KLR relations with the KL II polynomials are homogeneous for the KLR degree. -/
theorem klr_relation_mem (r : KLR.Diagram.Rel I) :
    ∃ d, KLR.Diagram.relation k (KLR.klQ2 k C) r ∈ HK r.dom r.cod d := by
  cases r with
  | sqEq c => exact ⟨_, LinDiagram.of_mem_homDeg _⟩
  | sqNe c d h =>
    refine ⟨-2 * C.dot c d, Submodule.sub_mem _ (degK_mem _ ?_)
      (ncEval_mem_homDeg _ _ ![C.dot c c, C.dot d d] ?_ _ _ (klQ2_isWeightedHomogeneous (k := k) h))⟩
    · degK_tac; try (rw [C.symm d c]; ring)
    · intro t; fin_cases t <;> exact degK_mem _ (by degK_tac)
  | slideLEq c =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (degK_mem _ ?_) (degK_mem _ ?_))
      (degK_mem _ rfl)⟩ <;> (degK_tac; try ring)
  | slideLNe c d h =>
    refine ⟨C.dot d d - C.dot c d, Submodule.sub_mem _ (degK_mem _ ?_) (degK_mem _ ?_)⟩ <;>
      (degK_tac; try ring)
  | slideREq c =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (degK_mem _ ?_) (degK_mem _ ?_))
      (degK_mem _ rfl)⟩ <;> (degK_tac; try ring)
  | slideRNe c d h =>
    refine ⟨C.dot c c - C.dot c d, Submodule.sub_mem _ (degK_mem _ ?_) (degK_mem _ ?_)⟩ <;>
      (degK_tac; try ring)
  | braid c d e h =>
    refine ⟨-C.dot c d - C.dot c e - C.dot d e, Submodule.sub_mem _ (degK_mem _ ?_)
      (degK_mem _ ?_)⟩ <;> (degK_tac; try ring)
  | braidQ c d h =>
    refine ⟨-2 * C.dot c d - C.dot c c, Submodule.sub_mem _ (Submodule.sub_mem _ (degK_mem _ ?_)
      (degK_mem _ ?_)) (ncEval_mem_homDeg _ _ ![C.dot c c, C.dot d d, C.dot c c] ?_ _ _
      (qbar_klQ2_isWeightedHomogeneous (k := k) h))⟩
    · degK_tac; try (rw [C.symm d c]; ring)
    · degK_tac; try (rw [C.symm d c]; ring)
    · intro t; fin_cases t <;> exact degK_mem _ (by degK_tac)

end KLR

/-! ### All relations -/

section All

theorem degree_upDiag (μ : X) {a b : Obj (KLR.Diagram.sig I)} (g : a ⟶ b) :
    Diagram.degree (deg RD) (upDiag RD μ g) = Diagram.degree (degK (I := I) (C := C)) g := by
  simp only [Diagram.degree, layers_upDiag, List.map_map]
  congr 1
  refine List.map_congr_left fun L _ => ?_
  show deg RD ((upShape L.gen).gen RD _) = degK L.gen
  rw [deg_gen]
  cases h : L.gen <;> rfl

theorem upLin_mem (μ : X) {a b : Obj (KLR.Diagram.sig I)} {f : LinDiagram k a b} {d : ℤ}
    (hf : f ∈ LinDiagram.homDeg k (degK (I := I) (C := C)) a b d) :
    upLin RD k μ f ∈ HD _ _ d := by
  classical
  rw [LinDiagram.homDeg, Finsupp.mem_supported] at hf ⊢
  intro g hg
  obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
  show Diagram.degree (deg RD) (upDiag RD μ g') = d
  rw [degree_upDiag]; exact hf hg'

theorem deg_cup_add_deg_cap (c : Col I X) : deg RD (.cup c) + deg RD (.cap c) = 0 := by
  obtain ⟨⟨s, i⟩, r⟩ := c
  simp only [deg, pair_sh, RD.pair_iY_iX_eq_A, A_self]
  cases s <;> simp <;> ring

/-- **The relations of `U` are homogeneous** for the degrees of Definition 3.1. -/
theorem pres_isHomogeneous : (pres RD k).IsHomogeneous (deg RD) := by
  rintro ((e | c | c) | r)
  · exact e.elim
  · refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.id_mem_homDeg _)⟩
    simp only [Diagram.degree, Pivotal.zigL, Diagram.layers_leftZigzag, Pivotal.cupD, Pivotal.capD,
      Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.sum_cons, List.sum_nil, Layer.wr, Layer.wl]
    rw [← add_assoc, add_zero]; exact deg_cup_add_deg_cap c
  · refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.id_mem_homDeg _)⟩
    simp only [Diagram.degree, Pivotal.zigR, Diagram.layers_rightZigzag, Pivotal.cupD, Pivotal.capD,
      Diagram.layers_layer, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.sum_cons, List.sum_nil, Layer.wr, Layer.wl]
    rw [← add_assoc, add_zero]; exact deg_cup_add_deg_cap c
  · cases r with
    | cycDotR i μ => exact ⟨C.dot i i, Submodule.sub_mem _
        (LinDiagram.of_mem_homDeg' (degree_rotDotR i μ)) (LinDiagram.of_mem_homDeg' (degree_downDot i μ))⟩
    | cycDotL i μ => exact ⟨C.dot i i, Submodule.sub_mem _
        (LinDiagram.of_mem_homDeg' (degree_rotDotL i μ)) (LinDiagram.of_mem_homDeg' (degree_downDot i μ))⟩
    | cwNeg i lam α h => exact ⟨_, LinDiagram.of_mem_homDeg _⟩
    | ccwNeg i lam α h => exact ⟨_, LinDiagram.of_mem_homDeg _⟩
    | cwOne i lam h =>
      refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.id_mem_homDeg _)⟩
      rw [degree_cwReal, Int.toNat_of_nonneg (by omega)]; ring
    | ccwOne i lam h =>
      refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.id_mem_homDeg _)⟩
      rw [degree_ccwReal, Int.toNat_of_nonneg (by omega)]; ring
    | curlR i lam => exact ⟨_, Submodule.sub_mem _
        (LinDiagram.of_mem_homDeg' (degree_curlR i lam)) (curlRHS_mem i lam)⟩
    | curlL i μ => exact ⟨_, Submodule.sub_mem _
        (LinDiagram.of_mem_homDeg' (degree_curlL i μ)) (curlLHS_mem i μ)⟩
    | decompEF i lam =>
      refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (LinDiagram.id_mem_homDeg _)
        (LinDiagram.of_mem_homDeg' ?_)) (decompEFSum_mem i lam)⟩
      rw [Diagram.degree_comp, degree_crossl, degree_crossr, add_zero]
    | decompFE i lam =>
      refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (LinDiagram.id_mem_homDeg _)
        (LinDiagram.of_mem_homDeg' ?_)) (decompFESum_mem i lam)⟩
      rw [Diagram.degree_comp, degree_crossl, degree_crossr, add_zero]
    | cycCrossR j i μ => exact ⟨_, Submodule.sub_mem _
        (LinDiagram.of_mem_homDeg' (degree_rotCrossR j i μ))
        (LinDiagram.of_mem_homDeg' (degree_downCross j i μ))⟩
    | cycCrossL j i μ => exact ⟨_, Submodule.sub_mem _
        (LinDiagram.of_mem_homDeg' (degree_rotCrossL j i μ))
        (LinDiagram.of_mem_homDeg' (degree_downCross j i μ))⟩
    | downupEF i j h μ =>
      refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.id_mem_homDeg _)⟩
      rw [Diagram.degree_comp, degree_crossl, degree_crossr, add_zero]
    | downupFE i j h μ =>
      refine ⟨0, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.id_mem_homDeg _)⟩
      rw [Diagram.degree_comp, degree_crossl, degree_crossr, add_zero]
    | klr μ r =>
      obtain ⟨d, hd⟩ := klr_relation_mem (k := k) (C := C) r
      exact ⟨d, upLin_mem μ hd⟩

/-- Every Hom-space of `U` is the direct sum of its homogeneous components: the grading of
KL III's 2-morphisms. -/
theorem isInternal_homDeg (a b : Obj (psig RD)) :
    DirectSum.IsInternal ((pres RD k).homDeg (deg RD) a b) :=
  Presentation.isInternal_homDeg (pres_isHomogeneous (RD := RD) (k := k)) a b

end All

end Categorification.KL3.Diagram
