/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.K0Serre
import Categorification.QuantumGroup.UDotOmega
import Categorification.QuantumGroup.UDotSerre
import Categorification.QuantumGroup.KLSpecialization

/-!
# The homomorphism `γ : U̇ → K₀(U̇)` (KL III Proposition 3.27, over `ℚ(q)`)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.6,
Proposition 3.27 (TeX label `prop_gamma`): "The assignment `E_i 1_λ ↦ [E_i 1_λ]` extends to a
`ℤ[q, q⁻¹]`-algebra homomorphism `γ : _A U̇ → K₀(U̇)`." KL III's proof: "`K₀(U̇)` is a free
`ℤ[q, q⁻¹]`-module, so it is enough to check that the assignment above extends to a homomorphism
of `ℚ(q)`-algebras `γ_{ℚ(q)} : U̇ → K₀(U̇) ⊗_{ℤ[q,q⁻¹]} ℚ(q)`. Propositions 3.24, 3.25, and 3.26
show that defining relations of `U̇` lift to 2-isomorphisms […] and, therefore, descend to
relations in the Grothendieck group."

## What is formalized

We work with a block `U̇ 1_λ = UDot.U1 RD vQ λ` of the algebraic `U̇` over `ℚ(q)`
(`Categorification.QuantumGroup.UDotBlock`; KL III's `q` is the indeterminate `vQ`) and an
arbitrary `ℚ(q)`-vector space `V` receiving `K₀(U̇(λ, ρ))` for all `ρ` by additive maps `φ_ρ`
compatible with `q` (`QTarget`: `φ(q^n x) = q^n φ(x)`). The universal example is
`K₀(U̇ 1_λ) ⊗_{ℤ[q,q⁻¹]} ℚ(q)`; phrasing the statement for every such `φ` is equivalent to
phrasing it for the tensor product, by its universal property.

* `gammaFree φ : 'U 1_λ → V`, `E_w 1_λ ↦ φ([E_w 1_λ])` on the free algebra (basis the signed
  sequences).
* `gammaFree_commRel`: it kills the commutation relators `E_a (E_iF_j - F_jE_i -
  δ_{ij}[⟨i, λ + b_X⟩]_i) E_b 1_λ` (KL III (2.4)) — by Propositions 3.25 and 3.26 in `K₀`
  (`eC_EF`, `eC_FE`, `eC_ij`).
* `gammaFree_serre`: it kills the Serre relators `E_a (∑_n (-1)^n E_{εi}^{(n)} E_{εj}
  E_{εi}^{(N-n)}) E_b 1_λ` of orientation `ε`, given the Serre relation in `K₀` for this
  orientation (`SerreK0 RD k ε`). For `ε = +` this is `serreK0_up`, from Proposition 3.24
  (upward) and the divided-power decompositions in `K₀` (`eC_serre`); for `ε = -` it is
  taken as a hypothesis here (`DownSerreK0`, the `K₀`-shadow of the second display of KL III
  Proposition 3.24); it is proved in `Categorification.Diagrams.KL3.DownwardDecomp`
  (`downSerreK0`, via the symmetry `ω̃`), which also gives the unconditional `gammaQ'`.
* `Lrel_le_ker`: hence `γ` kills all defining relations of `U̇ 1_λ` (given `DownSerreK0`).
* `gammaQ φ hF : U̇ 1_λ →ₗ[ℚ(q)] V`: **KL III Proposition 3.27 over `ℚ(q)`, block form**, with
  `gammaQ_mk_ew : γ(E_w 1_λ) = φ([E_w 1_λ])`.
* `eC_mul`: multiplicativity on generators, `[E_s 1_μ] · [E_t 1_λ] = [E_{st} 1_λ]` for the
  product `K0U.mul` of `K₀(U̇)` induced by composition (KL III (3.68)); `K0U.mul` is
  `ℤ[q, q⁻¹]`-bilinear (`K0U.mul_shift_left`, `K0U.mul_shift_right`).

## Later developments

* The `F`-Serre relation in `K₀` is `downSerreK0` (`Categorification.Diagrams.KL3.DownwardDecomp`).
* The integral form: `Categorification.Diagrams.KL3.GammaIntegral` and `GammaAUD` (the relations
  of `_A U̇` hold in `K₀(U̇)` up to `ℤ[q, q⁻¹]`-torsion; exactly if `K₀(U̇)` is torsion free,
  which KL III deduce from the Krull–Schmidt property of `U̇(λ, μ)` — not formalized).
* Associativity of `K0U.mul`: `Categorification.Diagrams.KL3.KaroubiAssoc`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  Categorification.GradedBicat KLR KLR.KLRAlgebra KLR.Diagram KLR.KL2 LaurentPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k] [DecidableEq I]

/-! ## Multiplicativity on generators -/

section Mul

variable {RD k}

omit [DecidableEq I] in
theorem nfHom_comp {ρ μ lam : X} {s t : List (Letter I)} (hs : wt RD μ s = ρ)
    (ht : wt RD lam t = μ) (h : wt RD lam (s ++ t) = ρ) :
    (nfHom RD k ρ μ s hs).comp (nfHom RD k μ lam t ht) = nfHom RD k ρ lam (s ++ t) h := by
  subst ht hs
  apply Bicat.Hom.ext
  simp only [Bicat.Hom.comp_obj]
  apply Obj.ext
  · simp [wt_append]
  · simp [ob, wd_append, wt_append]

omit [DecidableEq I] in
/-- **Multiplicativity of `γ` on generators**: `[E_s 1_μ] · [E_t 1_λ] = [E_{st} 1_λ]` in `K₀(U̇)`
(for `μ = λ + t_X`; the product is induced by composition, KL III (3.68)). -/
theorem eC_mul {ρ μ lam : X} (s t : List (Letter I)) (hs : wt RD μ s = ρ) (ht : wt RD lam t = μ)
    (h : wt RD lam (s ++ t) = ρ) :
    K0U.mul (eC RD k ρ μ s hs) (eC RD k μ lam t ht) = eC RD k ρ lam (s ++ t) h := by
  rw [K0U.mul_objOf, nfHom_comp hs ht h, add_zero]

end Mul

/-! ## Evaluation at `q ∈ ℚ(q)` -/

/-- The evaluation `ℤ[q, q⁻¹] → ℚ(q)`, `q ↦ q`. -/
def lpToQ : LaurentPolynomial ℤ →+* RatFunc ℚ := LaurentPolynomial.eval₂ (Int.castRingHom _) vQ

theorem lpToQ_T (n : ℤ) : lpToQ (T n) = ((vQ ^ n : (RatFunc ℚ)ˣ) : RatFunc ℚ) := by
  rw [lpToQ, eval₂_T]

theorem lpToQ_qn (d : ℤ) (n : ℕ) : lpToQ (qn d n) = qint (vQ ^ d) n := by
  rw [qn, map_sum, qint_eq_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lpToQ_T, ← zpow_mul]

theorem lpToQ_qfac (d : ℤ) (m : ℕ) : lpToQ (qfac d m) = qfact (vQ ^ d) m := by
  rw [qfac, qfact, map_prod]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [map_sum, qint_eq_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [lpToQ_T, ← zpow_mul]
  congr 2
  push_cast [Nat.cast_sub (by omega : r ≤ n)]
  ring

/-- `[n]_t = (t^n - t^{-n})/(t - t⁻¹)` agrees with `∑_{k<n} t^{n-1-2k}` for `n ≥ 0`. -/
theorem qbr_eq_qint {K : Type*} [Field K] (t : Kˣ) (ht : (t : K) - ((t⁻¹ : Kˣ) : K) ≠ 0)
    (n : ℕ) : qbr t n = qint t n := by
  rw [qbr, div_eq_iff ht, qint]
  have hg := geom_sum_mul ((t : K) ^ 2) n
  have key : ((t ^ (1 - (n : ℤ)) : Kˣ) : K) * ((t : K) - ((t⁻¹ : Kˣ) : K)) =
      ((t ^ (-(n : ℤ)) : Kˣ) : K) * ((t : K) ^ 2 - 1) := by
    rw [show (1 - (n : ℤ)) = -(n : ℤ) + 1 by ring, zpow_add, zpow_one, Units.val_mul]
    rw [Units.val_inv_eq_inv_val]
    field_simp
    ring
  calc ((t ^ (n : ℤ) : Kˣ) : K) - ((t ^ (-(n : ℤ)) : Kˣ) : K)
      = ((t ^ (-(n : ℤ)) : Kˣ) : K) * ((t : K) ^ 2) ^ n - ((t ^ (-(n : ℤ)) : Kˣ) : K) := by
        congr 1
        rw [← pow_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
        congr 2; push_cast; ring
    _ = ((t ^ (-(n : ℤ)) : Kˣ) : K) * ((t : K) ^ 2 - 1) *
          ∑ k ∈ Finset.range n, ((t : K) ^ 2) ^ k := by rw [mul_assoc, mul_comm _ (∑ k ∈ _, _), hg]; ring
    _ = _ := by rw [← key]; ring

theorem vQ_zpow_sub_inv_ne_zero {d : ℤ} (hd : d ≠ 0) :
    (((vQ ^ d : (RatFunc ℚ)ˣ)) : RatFunc ℚ) - (((vQ ^ d)⁻¹ : (RatFunc ℚ)ˣ) : RatFunc ℚ) ≠ 0 := by
  intro h
  have h2 : ((vQ ^ (2 * d) : (RatFunc ℚ)ˣ) : RatFunc ℚ) = 1 := by
    rw [sub_eq_zero] at h
    have : (vQ ^ d : (RatFunc ℚ)ˣ) = (vQ ^ d)⁻¹ := Units.ext h
    have h3 : (vQ ^ d * vQ ^ d : (RatFunc ℚ)ˣ) = 1 := by
      nth_rewrite 2 [this]; exact mul_inv_cancel _
    rw [two_mul, zpow_add, h3, Units.val_one]
  exact vQ_zpow_ne_one (mul_ne_zero two_ne_zero hd) (Units.ext (by rw [h2, Units.val_one]))

/-! ## Targets: `ℚ(q)`-vector spaces receiving `K₀(U̇ 1_λ)` -/

section Gamma

variable {RD k} (lam : X) (V : Type*) [AddCommGroup V] [Module (RatFunc ℚ) V]

variable (RD k) in
/-- A `ℚ(q)`-vector space `V` with additive maps `φ_ρ : K₀(U̇(λ, ρ)) → V` (for all `ρ`)
compatible with `q`: `φ(q^n x) = q^n φ(x)`. (Equivalently, a `ℚ(q)`-linear map
`K₀(U̇ 1_λ) ⊗_{ℤ[q, q⁻¹]} ℚ(q) → V`.) -/
structure QTarget where
  /-- The maps `φ_ρ`. -/
  φ : ∀ ρ : X, K0Kar RD k ρ lam →+ V
  map_T : ∀ (ρ : X) (n : ℤ) (x : K0Kar RD k ρ lam),
    φ ρ ((T n : LaurentPolynomial ℤ) • x) = ((vQ ^ n : (RatFunc ℚ)ˣ) : RatFunc ℚ) • φ ρ x

namespace QTarget

variable {lam V} (Φ : QTarget RD k lam V)

omit [DecidableEq I] in
/-- `φ(p x) = p(q) φ(x)` for all `p ∈ ℤ[q, q⁻¹]`. -/
theorem map_smul (ρ : X) (p : LaurentPolynomial ℤ) (x : K0Kar RD k ρ lam) :
    Φ.φ ρ (p • x) = lpToQ p • Φ.φ ρ x := by
  induction p using LaurentPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, map_add, hp, hp', map_add, add_smul]
  | C_mul_T n a =>
    have hC : lpToQ (LaurentPolynomial.C a) = (a : RatFunc ℚ) := by
      rw [lpToQ, eval₂_C, eq_intCast]
    rw [mul_smul, SplitK0.C_smul, map_zsmul, Φ.map_T, map_mul, lpToQ_T, mul_smul, hC,
      Int.cast_smul_eq_zsmul]

end QTarget

variable {lam V} (Φ : QTarget RD k lam V)

/-- **`γ` on the free algebra `'U 1_λ`**: `E_w 1_λ ↦ φ([E_w 1_λ])`. -/
def gammaFree : UDot.Free (RatFunc ℚ) I →ₗ[RatFunc ℚ] V :=
  PreF.linLift fun u => Φ.φ (wt RD lam u.toList) (eC RD k _ lam u.toList rfl)

omit [DecidableEq I] in
theorem gammaFree_ew (w : List (Letter I)) :
    gammaFree Φ (ew w) = Φ.φ (wt RD lam w) (eC RD k _ lam w rfl) := by
  rw [gammaFree, ew, PreF.linLift_word]
  rfl

omit [DecidableEq I] in
theorem phi_eC {ρ : X} {w w' : List (Letter I)} (hw : w = w') (h : wt RD lam w' = ρ) :
    Φ.φ (wt RD lam w) (eC RD k _ lam w rfl) = Φ.φ ρ (eC RD k ρ lam w' h) := by
  subst hw h; rfl

omit [DecidableEq I] in
theorem wl_ellOf_eq (b : List (Letter I)) (i : I) :
    wl C (RD.ellOf lam) b i = ip RD i (wt RD lam b) := by
  rw [RD.wl_ellOf, wt_eq_add_wX, add_comm]

/-- **`γ` kills the commutation relators** `E_a (E_iF_j - F_jE_i - δ_{ij}[⟨i, λ + b_X⟩]_i) E_b 1_λ`
(KL III (2.4)), by KL III Propositions 3.25 and 3.26 in `K₀`. -/
theorem gammaFree_commRel (a b : List (Letter I)) (i j : I) :
    gammaFree Φ (ew a * commRel C vQ (RD.ellOf lam) b i j * ew b) = 0 := by
  rw [ew_mul_commRel_mul, map_sub, map_sub, map_smul, gammaFree_ew, gammaFree_ew, gammaFree_ew]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, wl_ellOf_eq]
    set μ := wt RD lam b
    set ρ := wt RD lam (a ++ b)
    have hμ : wt RD lam b = μ := rfl
    have ha : wt RD μ a = ρ := by simp only [ρ, μ, wt_append]
    have h1 : wt RD lam (a ++ [up j, dn j] ++ b) = ρ := by
      simp only [ρ, wt_append, wt_up_dn]
    have h2 : wt RD lam (a ++ [dn j, up j] ++ b) = ρ := by
      simp only [ρ, wt_append, wt_dn_up]
    have h3 : wt RD lam (a ++ [] ++ b) = ρ := by simp [ρ]
    rw [phi_eC Φ (by simp) h1, phi_eC Φ (by simp) h2, phi_eC Φ (by simp) h3]
    have hd : di C j ≠ 0 := (di_pos C j).ne'
    have hq := vQ_zpow_sub_inv_ne_zero hd
    by_cases hn : 0 ≤ ip RD j μ
    · rw [eC_EF a b ha hμ j hn h1 h2 h3, map_add, Φ.map_smul, lpToQ_qn, ← qbr_eq_qint _ hq,
        Int.toNat_of_nonneg hn]
      simp only [qi]
      abel
    · rw [eC_FE a b ha hμ j (by omega) h1 h2 h3, map_add, Φ.map_smul, lpToQ_qn,
        ← qbr_eq_qint _ hq, Int.toNat_of_nonneg (by omega), qbr_neg]
      simp only [qi, neg_neg, neg_smul]
      abel
  · rw [if_neg hji, zero_smul, sub_zero]
    have ha : wt RD (wt RD (wt RD lam b) [up i, dn j]) a = wt RD lam (a ++ [up i, dn j] ++ b) := by
      rw [wt_append, wt_append]
    have h2 : wt RD lam (a ++ [dn j, up i] ++ b) = wt RD lam (a ++ [up i, dn j] ++ b) := by
      rw [wt_append, wt_append, wt_append, wt_append, wt_dn_up_eq]
    rw [phi_eC Φ (w := a ++ (true, i) :: (false, j) :: b) (w' := a ++ [up i, dn j] ++ b)
        (by simp) rfl,
      phi_eC Φ (w := a ++ (false, j) :: (true, i) :: b) (w' := a ++ [dn j, up i] ++ b) (by simp) h2,
      eC_ij a b i j (Ne.symm hji) ha rfl rfl rfl h2, sub_self]

end Gamma

/-! ## The Serre relations -/

section SerreWords

variable {RD k}

/-- The sequence `i^n j i^{N-n}`. -/
def serreW (i j : I) (N n : ℕ) : List I := List.replicate n i ++ j :: List.replicate (N - n) i

omit [DecidableEq I] in
theorem serreN_eq_dij {i j : I} (hij : i ≠ j) : C.serreN i j = C.dij i j + 1 := by
  have h1 := C.two_mul_dot_eq hij
  have h2 := C.dij_mul hij
  have hpos := C.dot_self_pos i
  have h3 := C.one_le_serreN hij
  have : ((C.dij i j : ℕ) : ℤ) = (C.serreN i j : ℤ) - 1 := by
    apply mul_right_cancel₀ hpos.ne'
    linear_combination h2 - h1
  omega

omit [DecidableEq I] in
/-- All words `a (ε i)^n (ε j) (ε i)^{N-n} b` have the same weight. -/
theorem wt_serreW (ε : Bool) (i j : I) {N n : ℕ} (hn : n ≤ N) (lam : X)
    (a b : List (Letter I)) :
    wt RD lam (a ++ (serreW i j N n).map (fun l => (ε, l)) ++ b) =
      wt RD lam (a ++ (serreW i j N 0).map (fun l => (ε, l)) ++ b) := by
  simp only [wt_eq_add_wX, RootDatum.wX, List.map_append, List.sum_append, serreW,
    List.map_cons, List.sum_cons, List.map_replicate, List.sum_replicate, Nat.sub_zero,
    List.replicate_zero, List.nil_append, List.map_nil, List.sum_nil, zero_smul, zero_add]
  have : n • (sgn ε • RD.iX i) + (N - n) • (sgn ε • RD.iX i) = N • (sgn ε • RD.iX i) := by
    rw [← add_nsmul, Nat.add_sub_cancel' hn]
  rw [← this]
  abel

omit [DecidableEq I] in
theorem length_serreW (i j : I) {N n : ℕ} (hn : n ≤ N) : (serreW i j N n).length = N + 1 := by
  simp [serreW]; omega

end SerreWords

/-- **The Serre relation in `K₀(U̇)` for strands of orientation `ε`** (`true`: upward, `false`:
downward), in every context: for `i ≠ j`, `N = d_ij + 1` and signed sequences `a`, `b`, there are
classes `Y_n` with `[E_{a (εi)^n (εj) (εi)^{N-n} b} 1_λ] = [n]_i! [N-n]_i! Y_n` and
`∑_{n even} Y_n = ∑_{n odd} Y_n`. For `ε = true` this is `serreK0_up` (KL III Proposition 3.24,
first display, and the divided-power decompositions); for `ε = false` it is the corresponding
consequence of the second display of Proposition 3.24 (proved as `downSerreK0` in
`Categorification.Diagrams.KL3.DownwardDecomp`). -/
def SerreK0 (ε : Bool) : Prop :=
  ∀ (i j : I), i ≠ j → ∀ (lam ρ : X) (a b : List (Letter I))
    (hρ : ∀ n, n ≤ C.dij i j + 1 →
      wt RD lam (a ++ (serreW i j (C.dij i j + 1) n).map (fun l => (ε, l)) ++ b) = ρ),
    ∃ Y : ℕ → K0Kar RD k ρ lam,
      (∀ n (hn : n ≤ C.dij i j + 1),
        eC RD k ρ lam (a ++ (serreW i j (C.dij i j + 1) n).map (fun l => (ε, l)) ++ b) (hρ n hn) =
          (qfac (di C i) n * qfac (di C i) (C.dij i j + 1 - n)) • Y n) ∧
      ∑ n ∈ serreEvens (C.dij i j + 1), Y n = ∑ n ∈ serreOdds (C.dij i j + 1), Y n

section SerreUp

variable {RD k}

/-- The sequence `j i^N`, the base of the Serre sequences `serreSeq _ 0 n = i^n j i^{N-n}`. -/
def serreBase (i j : I) (N : ℕ) : Seq ((j :: List.replicate N i : List I) : Multiset I) :=
  Seq.ofList (j :: List.replicate N i) rfl

omit [DecidableEq I] in
theorem card_serreBase (i j : I) (N : ℕ) :
    Multiset.card ((j :: List.replicate N i : List I) : Multiset I) = N + 1 := by simp

omit [DecidableEq I] in
theorem serreBase_lbl (i j : I) (N : ℕ) (r : Fin (Multiset.card
    ((j :: List.replicate N i : List I) : Multiset I))) :
    (serreBase i j N).lbl r = if (r : ℕ) = 0 then j else i := by
  rw [serreBase, Seq.ofList_lbl, List.getElem_cons]
  split_ifs with h
  · rfl
  · exact List.getElem_replicate _

theorem word_serreSeq_base (i j : I) {N n : ℕ} (hn : n ≤ N) :
    word (serreSeq (serreBase i j N) 0 n) = serreW i j N n := by
  have hpN : 0 + N < Multiset.card ((j :: List.replicate N i : List I) : Multiset I) := by
    rw [card_serreBase]; omega
  have ht₀ : ∀ r : Fin (Multiset.card ((j :: List.replicate N i : List I) : Multiset I)),
      (r : ℕ) = 0 → (serreBase i j N).lbl r = j := fun r h => by rw [serreBase_lbl, if_pos h]
  have ht : ∀ r : Fin (Multiset.card ((j :: List.replicate N i : List I) : Multiset I)),
      0 < (r : ℕ) → (r : ℕ) ≤ 0 + N → (serreBase i j N).lbl r = i := fun r h _ => by
    rw [serreBase_lbl, if_neg (by omega)]
  apply List.ext_getElem
  · rw [length_word, card_serreBase, length_serreW i j hn]
  · intro r h₁ h₂
    rw [getElem_word]
    have hl := lbl_serreSeq hpN ht₀ ht hn ⟨r, by simpa using h₁⟩
    simp only [zero_add] at hl
    show (serreSeq (serreBase i j N) 0 n).lbl _ = _
    rw [hl]
    show _ = (List.replicate n i ++ j :: List.replicate (N - n) i)[r]
    have hlen : r < N + 1 := by rw [length_serreW i j hn] at h₂; exact h₂
    rw [List.getElem_append]
    by_cases hrn : r < n
    · rw [dif_pos (by simpa using hrn), if_neg (by omega),
        if_pos ⟨by omega, by omega⟩, List.getElem_replicate]
    · rw [dif_neg (by simpa using hrn), List.getElem_cons]
      by_cases hr : r = n
      · rw [if_pos (by omega), dif_pos (by simp; omega)]
      · rw [if_neg (by omega), dif_neg (by simp; omega), List.getElem_replicate,
          if_pos ⟨by omega, by omega⟩]

omit [DecidableEq I] in
theorem eC_congr {ρ lam : X} {w w' : List (Letter I)} (hw : w = w') (h : wt RD lam w = ρ)
    (h' : wt RD lam w' = ρ) : eC RD k ρ lam w h = eC RD k ρ lam w' h' := by
  subst hw; rfl

/-- **KL III Proposition 3.24 (first display) in `K₀`**: the upward Serre relation
`SerreK0 RD k true` holds. -/
theorem serreK0_up : SerreK0 RD k true := by
  intro i j hij lam ρ a b hρ
  set N := C.dij i j + 1 with hNdef
  have hpN : 0 + N < Multiset.card ((j :: List.replicate N i : List I) : Multiset I) := by
    rw [card_serreBase]; omega
  have ht₀ : ∀ r : Fin (Multiset.card ((j :: List.replicate N i : List I) : Multiset I)),
      (r : ℕ) = 0 → (serreBase i j N).lbl r = j := fun r h => by rw [serreBase_lbl, if_pos h]
  have ht : ∀ r : Fin (Multiset.card ((j :: List.replicate N i : List I) : Multiset I)),
      0 < (r : ℕ) → (r : ℕ) ≤ 0 + N → (serreBase i j N).lbl r = i := fun r h _ => by
    rw [serreBase_lbl, if_neg (by omega)]
  have hw : ∀ n, n ≤ N → ups (word (serreSeq (serreBase i j N) 0 n)) =
      (serreW i j N n).map (fun l => (true, l)) := fun n hn => by
    rw [word_serreSeq_base i j hn]
  have ha : wt RD (wν RD ((j :: List.replicate N i : List I) : Multiset I) + wt RD lam b) a = ρ := by
    have := hρ 0 (Nat.zero_le _)
    rw [wt_append, wt_append, ← hw 0 (Nat.zero_le _), wt_ups_word] at this
    exact this
  obtain ⟨Yc, hY, hsum⟩ := eC_serre (RD := RD) (k := k) hpN ht₀ ht hij rfl a b ha rfl
  refine ⟨Yc, fun n hn => ?_, hsum⟩
  have h' : wt RD lam (a ++ ups (word (serreSeq (serreBase i j N) 0 n)) ++ b) = ρ := by
    rw [hw n hn]; exact hρ n hn
  rw [eC_congr (by rw [hw n hn]) (hρ n hn) h', hY n hn h']

end SerreUp

/-- The downward Serre relation in `K₀` (the `K₀`-shadow of KL III Proposition 3.24, second
display), **not proved here**. -/
abbrev DownSerreK0 : Prop := SerreK0 RD k false

/-! ## `γ` kills the Serre relators -/

section GammaSerre

variable {RD k} {lam : X} {V : Type*} [AddCommGroup V] [Module (RatFunc ℚ) V]
  (Φ : QTarget RD k lam V)

omit [DecidableEq I] in
theorem θ_pow_eq_word (i : I) (n : ℕ) :
    (PreF.θ i : PreF (RatFunc ℚ) I) ^ n = PreF.word (FreeMonoid.ofList (List.replicate n i)) := by
  induction n with
  | zero => simp [PreF.word_one]
  | succ n ih =>
    rw [pow_succ, ih, PreF.θ, ← PreF.word_mul, List.replicate_succ', FreeMonoid.ofList_append,
      FreeMonoid.ofList_singleton]

omit [DecidableEq I] in
/-- The terms of the Serre element: `F(θ_i^{(n)} θ_j θ_i^{(m)}) = ([n]_i! [m]_i!)⁻¹ E_{(εi)^n (εj) (εi)^m}`. -/
theorem F_serreTerm (ε : Bool) (F : PreF (RatFunc ℚ) I →ₐ[RatFunc ℚ] UDot.Free (RatFunc ℚ) I)
    (hF : ∀ u, F (PreF.word u) = ew (u.toList.map (fun l => (ε, l)))) (i j : I) (n m : ℕ) :
    F (PreF.dpow C.dot vQ i n * PreF.θ j * PreF.dpow C.dot vQ i m) =
      ((qfact (PreF.vi C.dot vQ i) n)⁻¹ * (qfact (PreF.vi C.dot vQ i) m)⁻¹) •
        ew ((List.replicate n i ++ j :: List.replicate m i).map (fun l => (ε, l))) := by
  rw [PreF.dpow, PreF.dpow, θ_pow_eq_word, θ_pow_eq_word, smul_mul_assoc, smul_mul_assoc,
    mul_smul_comm, smul_smul, map_smul, PreF.θ, ← PreF.word_mul, ← PreF.word_mul, hF]
  simp only [FreeMonoid.toList_mul, FreeMonoid.toList_ofList, FreeMonoid.toList_of,
    List.append_assoc, List.singleton_append]

omit [DecidableEq I] in
theorem sum_range_neg_one_pow (N : ℕ) (v : ℕ → V) :
    ∑ n ∈ Finset.range (N + 1), ((-1 : RatFunc ℚ) ^ n) • v n =
      ∑ n ∈ serreEvens N, v n - ∑ n ∈ serreOdds N, v n := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1)) Even, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [(Finset.mem_filter.1 hn).2.neg_one_pow, one_smul]
  · have : (Finset.range (N + 1)).filter (fun n => ¬Even n) = serreOdds N := by
      rw [serreOdds]; exact Finset.filter_congr fun n _ => Nat.not_even_iff_odd
    rw [this]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [((Finset.mem_filter.1 hn).2).neg_one_pow, neg_one_smul]

omit [DecidableEq I] in
/-- **`γ` kills the Serre relators** `E_a F(∑_n (-1)^n θ_i^{(n)} θ_j θ_i^{(N-n)}) E_b 1_λ` for
strands of orientation `ε` (`F = posF` for `ε = +`, `negF` for `ε = -`), given the Serre relation
in `K₀` for this orientation. -/
theorem gammaFree_serre (ε : Bool) (hS : SerreK0 RD k ε)
    (F : PreF (RatFunc ℚ) I →ₐ[RatFunc ℚ] UDot.Free (RatFunc ℚ) I)
    (hF : ∀ u, F (PreF.word u) = ew (u.toList.map (fun l => (ε, l))))
    (a b : List (Letter I)) {i j : I} (hij : i ≠ j) :
    gammaFree Φ (ew a * F (serreKL C vQ i j) * ew b) = 0 := by
  set N := C.dij i j + 1 with hN
  have hρ : ∀ n, n ≤ N → wt RD lam (a ++ (serreW i j N n).map (fun l => (ε, l)) ++ b) =
      wt RD lam (a ++ (serreW i j N 0).map (fun l => (ε, l)) ++ b) :=
    fun n hn => wt_serreW ε i j hn lam a b
  obtain ⟨Y, hY, hsum⟩ := hS i j hij lam _ a b hρ
  rw [serreKL, serreN_eq_dij hij, map_sum, Finset.mul_sum, Finset.sum_mul, map_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm : ∀ n ∈ Finset.range (N + 1),
      gammaFree Φ (ew a * F (((-1 : RatFunc ℚ) ^ (n, N - n).1) •
        (PreF.dpow C.dot vQ i (n, N - n).1 * PreF.θ j * PreF.dpow C.dot vQ i (n, N - n).2)) *
        ew b) = ((-1 : RatFunc ℚ) ^ n) • Φ.φ _ (Y n) := fun n hn => by
    have hn' : n ≤ N := by rw [Finset.mem_range] at hn; omega
    rw [map_smul, F_serreTerm ε F hF, smul_smul, mul_smul_comm, smul_mul_assoc, ← ew_append,
      ← ew_append, map_smul, gammaFree_ew]
    rw [phi_eC Φ (w' := a ++ (serreW i j N n).map (fun l => (ε, l)) ++ b)
      (by simp [serreW]) (hρ n hn'), hY n hn', Φ.map_smul, map_mul, lpToQ_qfac, lpToQ_qfac,
      smul_smul]
    congr 1
    have h1 := C.qfact_ne_zero i n
    have h2 := C.qfact_ne_zero i (N - n)
    have hdi : (C.dot i i / 2) = di C i := rfl
    simp only [PreF.vi, hdi] at h1 h2 ⊢
    rw [← hN]
    field_simp
  rw [Finset.sum_congr rfl hterm, sum_range_neg_one_pow, ← map_sum, ← map_sum, hsum, sub_self]

end GammaSerre

/-! ## `γ` on `U̇ 1_λ` -/

section GammaQ

variable {RD k} {lam : X} {V : Type*} [AddCommGroup V] [Module (RatFunc ℚ) V]
  (Φ : QTarget RD k lam V)

/-- `γ` kills all defining relations of `U̇ 1_λ`, given the downward Serre relation in `K₀`. -/
theorem Lrel_le_ker (hD : DownSerreK0 RD k) :
    Lrel C vQ (RD.ellOf lam) ≤ LinearMap.ker (gammaFree Φ) := by
  rw [Lrel, Submodule.span_le]
  rintro z (⟨a, b, i, j, rfl⟩ | ⟨a, b, i, j, hij, rfl | rfl⟩)
  · exact gammaFree_commRel Φ a b i j
  · exact gammaFree_serre Φ true serreK0_up posF (fun u => by rw [posF_word]; rfl) a b hij
  · exact gammaFree_serre Φ false hD negF (fun u => by rw [negF_word]; rfl) a b hij

/-- **KL III Proposition 3.27 over `ℚ(q)`** (block `U̇ 1_λ`, conditional on the downward Serre
relation in `K₀`): the assignment `E_w 1_λ ↦ [E_w 1_λ]` extends to a `ℚ(q)`-linear map
`γ : U̇ 1_λ → V` for every `ℚ(q)`-vector space `V` receiving `K₀(U̇ 1_λ)` compatibly with `q`
(in particular `V = K₀(U̇ 1_λ) ⊗_{ℤ[q,q⁻¹]} ℚ(q)`). -/
def gammaQ (hD : DownSerreK0 RD k) : U1 RD vQ lam →ₗ[RatFunc ℚ] V :=
  (Lrel C vQ (RD.ellOf lam)).liftQ (gammaFree Φ) (Lrel_le_ker Φ hD)

/-- `γ(E_w 1_λ) = φ([E_w 1_λ])`. -/
theorem gammaQ_mk_ew (hD : DownSerreK0 RD k) (w : List (Letter I)) :
    gammaQ Φ hD (UDot.mk RD vQ lam (ew w)) = Φ.φ (wt RD lam w) (eC RD k _ lam w rfl) := by
  rw [gammaQ, UDot.mk, Submodule.mkQ_apply, Submodule.liftQ_apply, gammaFree_ew]

end GammaQ

end Categorification.KL3.Diagram
