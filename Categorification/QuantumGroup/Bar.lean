/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.QuantumGroup.CoproductF
import Categorification.QuantumGroup.Serre

/-!
# The bar involution on `'f` and `f`

Lusztig, *Introduction to quantum groups*, 1.2.12–1.2.15: there is a unique ring homomorphism
`¯ : 'f → 'f` with `θ_i ↦ θ_i` and `v^n ↦ v^{-n}`; it preserves the radical `ℐ`, hence
induces `¯ : f → f`; and it fixes the divided powers, so it preserves `_𝒜 f`.
Khovanov–Lauda, arXiv:0803.4121v2, §3.1: "`'f` and `f` come with a `ℚ(q)`-antilinear
involution `¯` that takes `q^n` to `q^{-n}` and `θ_i` to `θ_i`".

We work over a field `K` with a ring endomorphism `σ` of `K` satisfying `σ v = v⁻¹`
(for `K = ℚ(v)` this is `v ↦ v⁻¹`, `barQ`; see `CartanDatum.barF`).

## Method (Lusztig 1.2.13–1.2.15)

* `PreF.rev` is the reversal anti-automorphism of `'f` and `PreF.dR k = rev ∘ d k ∘ rev` the
  right twisted derivation; it is adjoint to right multiplication by `θ_k`:
  `(z θ_k, y) = (θ_k, θ_k) (z, dR_k y)` (`PreF.form_mul_θ`; this uses that `d j` and `dR k`
  commute for symmetric `dot`).
* Hence an element with no constant term all of whose `dR_k` lie in `ℐ` lies in `ℐ`
  (`PreF.mem_radical_of_dR`), and `ℐ` is stable under each `d_k` when `(θ_k, θ_k) ≠ 0`.
* `bar (d_k x) = T_k (dR_k (bar x))` for a weight twist `T_k` (`PreF.bar_d`), and induction on
  word length gives `bar(ℐ) ⊆ ℐ` (`PreF.bar_mem_radical`).

## Main results

* `PreF.bar` — the `σ`-semilinear ring endomorphism of `'f` fixing each `θ_i`;
* `PreF.bar_mem_radical`, `PreF.barF` — the induced ring endomorphism of `f`;
* `PreF.barF_barF` — it is an involution when `σ` is;
* `PreF.barF_dpowF`, `PreF.barF_mem_Af` — it fixes the divided powers and preserves `_𝒜 f`.
-/

noncomputable section

namespace Categorification.QuantumGroup

open Finset
open scoped Classical

namespace PreF

section CommRing

variable {I : Type*} {K : Type*} [CommRing K] {dot : I → I → ℤ} {v : Kˣ}

/-! ### Reversal -/

/-- The reversal anti-automorphism `θ_{i₁} ⋯ θ_{iₙ} ↦ θ_{iₙ} ⋯ θ_{i₁}` of `'f`. -/
def rev : PreF K I →ₗ[K] PreF K I := linLift fun w => word (FreeMonoid.reverse w)

theorem rev_word (w : FreeMonoid I) : rev (word w : PreF K I) = word (FreeMonoid.reverse w) :=
  linLift_word _ _

theorem rev_rev (x : PreF K I) : rev (rev x) = x := by
  have : (rev : PreF K I →ₗ[K] PreF K I) ∘ₗ rev = LinearMap.id :=
    lhom_ext fun w => by simp [rev_word, FreeMonoid.reverse_reverse]
  exact LinearMap.congr_fun this x

theorem rev_mul (x y : PreF K I) : rev (x * y) = rev y * rev x := by
  induction x using induction_linear with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, hx, hx', map_add, mul_add]
  | smul_word u r =>
    induction y using induction_linear with
    | zero => simp
    | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, add_mul]
    | smul_word w s =>
      rw [smul_mul_smul_comm, map_smul, map_smul, map_smul, ← word_mul, rev_word, rev_word,
        rev_word, FreeMonoid.reverse_mul, word_mul, smul_mul_smul_comm, mul_comm r s]

theorem rev_θ (i : I) : rev (θ i : PreF K I) = θ i := by
  rw [θ, rev_word, FreeMonoid.reverse_of]

theorem rev_one : rev (1 : PreF K I) = 1 := by
  rw [← word_one, rev_word]; rfl

theorem wt_reverse (w : FreeMonoid I) : wt (FreeMonoid.reverse w) = wt w :=
  Multiset.coe_reverse (FreeMonoid.toList w)

theorem rev_mem_supp {P : Multiset I → Prop} {x : PreF K I}
    (hx : x ∈ (supp {w | P (wt w)} : Submodule K (PreF K I))) :
    rev x ∈ (supp {w | P (wt w)} : Submodule K (PreF K I)) := by
  refine map_supp_le rev (fun w hw => ?_) x hx
  rw [rev_word]
  exact word_mem_supp (by simpa [wt_reverse] using hw)

theorem counit_rev (x : PreF K I) : counit (rev x) = counit x := by
  have : counit ∘ₗ (rev : PreF K I →ₗ[K] PreF K I) = counit := by
    refine lhom_ext fun w => ?_
    simp only [LinearMap.comp_apply, rev_word, counit_word]
    congr 1
    apply propext
    constructor
    · intro h; rw [← FreeMonoid.reverse_reverse (a := w), h]; rfl
    · rintro rfl; rfl
  exact LinearMap.congr_fun this x

/-! ### The right twisted derivations -/

variable (dot v) in
/-- The right twisted derivation `dR k = rev ∘ d k ∘ rev` (compare Lusztig's `_i r`, 1.2.13):
it removes a letter `k` with weight `v^{(letters to its right)·k}`. -/
def dR (k : I) : PreF K I →ₗ[K] PreF K I := rev ∘ₗ d dot v k ∘ₗ rev

theorem dR_apply (k : I) (x : PreF K I) : dR dot v k x = rev (d dot v k (rev x)) := rfl

@[simp] theorem dR_one (k : I) : dR dot v k (1 : PreF K I) = 0 := by
  rw [dR_apply, rev_one, d_one, map_zero]

/-- `d_k (y θ_i) = d_k(y) θ_i + δ_{ik} v^n y` if every word `w` of `y` has `|w|·k = n`. -/
theorem d_mul_θ (i k : I) (n : ℤ) {y : PreF K I}
    (hy : y ∈ (supp {w | wdot dot (wt w) {k} = n} : Submodule K (PreF K I))) :
    d dot v k (y * θ i) = d dot v k y * θ i + (if i = k then ((v ^ n : Kˣ) : K) • y else 0) := by
  by_cases hik : i = k
  · rw [if_pos hik]
    have := eqOn_supp ((d dot v k) ∘ₗ LinearMap.mulRight K (θ i))
      (LinearMap.mulRight K (θ i) ∘ₗ d dot v k + ((v ^ n : Kˣ) : K) • LinearMap.id) ?_ y hy
    · simpa using this
    · intro w hw
      simp only [Set.mem_setOf_eq] at hw
      simp [d_word_mul, hw, d_θ, hik]
  · rw [if_neg hik, add_zero]
    have := eqOn_supp ((d dot v k) ∘ₗ LinearMap.mulRight K (θ i))
      (LinearMap.mulRight K (θ i) ∘ₗ d dot v k) ?_ y hy
    · simpa using this
    · intro w _
      simp [d_word_mul, d_θ, hik]

theorem dR_θ_mul (i k : I) (n : ℤ) {x : PreF K I}
    (hx : x ∈ (supp {w | wdot dot (wt w) {k} = n} : Submodule K (PreF K I))) :
    dR dot v k (θ i * x) =
      θ i * dR dot v k x + (if i = k then ((v ^ n : Kˣ) : K) • x else 0) := by
  have hx' := rev_mem_supp (P := fun μ => wdot dot μ {k} = n) hx
  rw [dR_apply, rev_mul, rev_θ, d_mul_θ i k n hx', map_add, rev_mul, rev_θ, dR_apply]
  split_ifs <;> simp [rev_rev]

theorem counit_d_word (k : I) (w : FreeMonoid I) :
    counit (d dot v k (word w : PreF K I)) = if w = FreeMonoid.of k then 1 else 0 := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    rw [word_one, d_one, map_zero, if_neg]
    intro h
    have := congrArg FreeMonoid.length h
    simp at this
  | mul_of j w _ =>
    rw [d_word_of_mul, map_add, map_smul, counit_θ_mul, smul_zero, add_zero]
    have e : (FreeMonoid.of j * w = FreeMonoid.of k) ↔ (j = k ∧ w = 1) := by
      constructor
      · intro h
        have h' := congrArg FreeMonoid.toList h
        simp only [FreeMonoid.toList_of_mul, FreeMonoid.toList_of, List.cons.injEq] at h'
        exact ⟨h'.1, FreeMonoid.toList.injective (by simpa using h'.2)⟩
      · rintro ⟨rfl, rfl⟩; rfl
    by_cases hj : j = k
    · subst hj
      rw [if_pos rfl, counit_word]
      by_cases hw : w = 1
      · rw [if_pos hw, if_pos (e.2 ⟨rfl, hw⟩)]
      · rw [if_neg hw, if_neg (fun h => hw (e.1 h).2)]
    · rw [if_neg hj, map_zero, if_neg (fun h => hj (e.1 h).1)]

theorem counit_dR (k : I) (y : PreF K I) :
    counit (dR dot v k y) = counit (d dot v k y) := by
  have : counit ∘ₗ dR dot v k = (counit ∘ₗ d dot v k : PreF K I →ₗ[K] K) := by
    refine lhom_ext fun w => ?_
    simp only [LinearMap.comp_apply, dR_apply, counit_rev, rev_word, counit_d_word]
    congr 1
    apply propext
    constructor
    · intro h; rw [← FreeMonoid.reverse_reverse (a := w), h]; rfl
    · rintro rfl; rfl
  exact LinearMap.congr_fun this y

theorem d_word_mem_supp_wdot (j k : I) (w : FreeMonoid I) :
    d dot v j (word w : PreF K I) ∈ (supp {w' | wdot dot (wt w') {k} =
      wdot dot (wt w) {k} - dot j k} : Submodule K (PreF K I)) := by
  refine supp_mono ?_ (d_word_mem_supp j w)
  intro w' hw'
  simp only [Set.mem_setOf_eq] at hw' ⊢
  rw [← hw', wdot_cons_left, wdot_singleton]
  ring

/-- The left and right twisted derivations commute (for a symmetric pairing). -/
theorem d_dR_comm (hdot : ∀ i j, dot i j = dot j i) (j k : I) (x : PreF K I) :
    d dot v j (dR dot v k x) = dR dot v k (d dot v j x) := by
  have : d dot v j ∘ₗ dR dot v k = (dR dot v k ∘ₗ d dot v j : PreF K I →ₗ[K] PreF K I) := by
    refine lhom_ext fun w => ?_
    simp only [LinearMap.comp_apply]
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | mul_of i w ih =>
      have hw : (word w : PreF K I) ∈ (supp {w' | wdot dot (wt w') {k} = wdot dot (wt w) {k}} :
          Submodule K (PreF K I)) := word_mem_supp rfl
      rw [word_of_mul, dR_θ_mul i k _ hw, map_add, d_θ_mul, ih, d_θ_mul, map_add, map_smul,
        dR_θ_mul i k _ (d_word_mem_supp_wdot j k w)]
      by_cases hik : i = k
      · have e : ((v ^ dot k j : Kˣ) : K) * ((v ^ (wdot dot (wt w) {k} - dot j k) : Kˣ) : K) =
            ((v ^ wdot dot (wt w) {k} : Kˣ) : K) := by
          rw [← Units.val_mul, ← zpow_add, hdot k j]; congr 2; ring
        simp only [hik, if_true, map_smul, smul_add, smul_smul, e]
        split_ifs <;> simp only [map_zero, zero_add, add_assoc]
      · simp only [hik, if_false, map_zero, add_zero, smul_zero]
        split_ifs <;> simp
  exact LinearMap.congr_fun this x

/-- Right multiplication by `θ_k` is adjoint to `dR_k`:
`(z θ_k, y) = c_k (z, dR_k y)` (compare Lusztig 1.2.13). -/
theorem form_mul_θ (hdot : ∀ i j, dot i j = dot j i) (c : I → K) (k : I) (z y : PreF K I) :
    form dot v c (z * θ k) y = c k * form dot v c z (dR dot v k y) := by
  induction z using induction_linear generalizing y with
  | zero => simp
  | add z z' hz hz' => rw [add_mul, map_add, LinearMap.add_apply, hz, hz', map_add,
      LinearMap.add_apply, mul_add]
  | smul_word u r =>
    rw [smul_mul_assoc, map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, mul_left_comm]
    congr 1
    induction u using FreeMonoid.inductionOn' generalizing y with
    | one => rw [word_one, one_mul, form_θ, form_one, counit_dR]
    | mul_of j u ih =>
      rw [word_of_mul, mul_assoc, form_θ_mul, ih, form_θ_mul, d_dR_comm hdot]
      ring

/-- An element with no constant term all of whose right derivatives `dR k x` lie in the
radical lies in the radical. -/
theorem mem_radical_of_dR (hdot : ∀ i j, dot i j = dot j i) {c : I → K} {x : PreF K I}
    (h0 : counit x = 0) (hd : ∀ k, dR dot v k x ∈ radical dot v c) : x ∈ radical dot v c := by
  rw [mem_radical_iff' hdot]
  suffices (form dot v c).flip x = 0 from fun y => LinearMap.congr_fun this y
  refine lhom_ext fun w => ?_
  rw [LinearMap.flip_apply, LinearMap.zero_apply]
  obtain ⟨l, rfl⟩ : ∃ l : List I, FreeMonoid.ofList l = w := ⟨w.toList, rfl⟩
  induction l using List.reverseRecOn with
  | nil => rw [FreeMonoid.ofList_nil, word_one, form_one, h0]
  | append_singleton l k _ =>
    rw [FreeMonoid.ofList_append, FreeMonoid.ofList_singleton, word_mul, ← θ, form_mul_θ hdot,
      form_symm hdot, hd k, mul_zero]

/-! ### Word length -/

/-- The words of length `< n`. -/
def lenLt (n : ℕ) : Set (FreeMonoid I) := {w | w.length < n}

theorem length_eq_card_wt (w : FreeMonoid I) : w.length = Multiset.card (wt w) := by
  simp [wt, FreeMonoid.length]

theorem d_mem_lenLt (k : I) (n : ℕ) {x : PreF K I}
    (hx : x ∈ (supp (lenLt (n + 1)) : Submodule K (PreF K I))) :
    d dot v k x ∈ (supp (lenLt n) : Submodule K (PreF K I)) := by
  refine map_supp_le (d dot v k) (fun w hw => supp_mono ?_ (d_word_mem_supp k w)) x hx
  intro w' hw'
  simp only [lenLt, Set.mem_setOf_eq] at hw hw' ⊢
  have := congrArg Multiset.card hw'
  rw [Multiset.card_cons, ← length_eq_card_wt, ← length_eq_card_wt] at this
  omega

theorem exists_mem_lenLt (x : PreF K I) :
    ∃ n, x ∈ (supp (lenLt n) : Submodule K (PreF K I)) := by
  refine ⟨x.support.sup FreeMonoid.length + 1, ?_⟩
  rw [supp, Finsupp.mem_supported]
  intro w hw
  simp only [lenLt, Set.mem_setOf_eq]
  exact Nat.lt_succ_of_le (Finset.le_sup (f := FreeMonoid.length) hw)

theorem supp_lenLt_zero : (supp (lenLt 0) : Submodule K (PreF K I)) = ⊥ := by
  rw [supp, lenLt]
  simp

/-! ### The bar map -/

variable (σ : K →+* K)

/-- The `σ`-semilinear ring endomorphism of `'f` fixing every word (Lusztig 1.2.12 for
`σ : v ↦ v⁻¹`). -/
def bar : PreF K I →+* PreF K I :=
  MonoidAlgebra.liftNCRingHom ((algebraMap K (PreF K I)).comp σ) (MonoidAlgebra.of K _)
    fun a _ => Algebra.commute_algebraMap_left (σ a) _

theorem bar_single (w : FreeMonoid I) (a : K) :
    bar σ (MonoidAlgebra.single w a : PreF K I) = σ a • word w := by
  simp [bar, MonoidAlgebra.liftNCRingHom, MonoidAlgebra.liftNC_single, Algebra.smul_def, word]

theorem bar_word (w : FreeMonoid I) : bar σ (word w : PreF K I) = word w := by
  rw [word, bar_single, map_one, one_smul]; rfl

theorem bar_θ (i : I) : bar σ (θ i : PreF K I) = θ i := bar_word σ _

theorem bar_smul (a : K) (x : PreF K I) : bar σ (a • x) = σ a • bar σ x := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, bar_single]
  simp [Algebra.smul_def, word]

theorem bar_algebraMap (a : K) : bar σ (algebraMap K (PreF K I) a) = algebraMap K _ (σ a) := by
  rw [Algebra.algebraMap_eq_smul_one, bar_smul, map_one, ← Algebra.algebraMap_eq_smul_one]

theorem counit_bar (x : PreF K I) : counit (bar σ x) = σ (counit x) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | smul_word w r =>
    rw [bar_smul, bar_word, map_smul, map_smul, smul_eq_mul, smul_eq_mul, map_mul, counit_word]
    split_ifs <;> simp

theorem σ_zpow {σ : K →+* K} (hσ : σ (v : K) = ((v⁻¹ : Kˣ) : K)) (n : ℤ) :
    σ ((v ^ n : Kˣ) : K) = ((v ^ (-n) : Kˣ) : K) := by
  have hu : Units.map (σ : K →* K) v = v⁻¹ := Units.ext hσ
  have e : σ ((v ^ n : Kˣ) : K) = ((Units.map (σ : K →* K) (v ^ n) : Kˣ) : K) := rfl
  rw [e, map_zpow, hu, inv_zpow']

theorem twistBy_θ_mul (k j : I) (y : PreF K I) :
    twistBy v (fun μ => -wdot dot μ {k}) (θ j * y) =
      ((v ^ (-dot j k) : Kˣ) : K) • (θ j * twistBy v (fun μ => -wdot dot μ {k}) y) := by
  induction y using induction_linear with
  | zero => simp
  | add y y' hy hy' => rw [mul_add, map_add, hy, hy', map_add, mul_add, smul_add]
  | smul_word w r =>
    simp only [mul_smul_comm, map_smul, ← word_of_mul, twistBy_word, smul_smul, wt_of_mul,
      wdot_cons_left, wdot_singleton]
    congr 1
    rw [neg_add, zpow_add, Units.val_mul]
    ring

theorem twistBy_twistBy (χ χ' : Multiset I → ℤ) (x : PreF K I) :
    twistBy v χ (twistBy v χ' x) = twistBy v (χ + χ') x := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | smul_word w r =>
    simp only [map_smul, twistBy_word, smul_smul, Pi.add_apply]
    congr 1
    rw [zpow_add, Units.val_mul]
    ring

theorem twistBy_zero (x : PreF K I) : twistBy v (0 : Multiset I → ℤ) x = x := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy]
  | smul_word w r => rw [map_smul, twistBy_word, Pi.zero_apply, zpow_zero, Units.val_one,
      one_smul]

/-- `bar ∘ d_k = T_k ∘ dR_k ∘ bar` with the weight twist `T_k(w) = v^{-|w|·k} w`
(compare Lusztig 1.2.14). -/
theorem bar_d (hσ : σ (v : K) = ((v⁻¹ : Kˣ) : K)) (k : I) (x : PreF K I) :
    bar σ (d dot v k x) = twistBy v (fun μ => -wdot dot μ {k}) (dR dot v k (bar σ x)) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]
  | smul_word w r =>
    rw [map_smul, bar_smul, bar_smul, map_smul, map_smul, bar_word]
    congr 1
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | mul_of j w ih =>
      have hw : (word w : PreF K I) ∈ (supp {w' | wdot dot (wt w') {k} = wdot dot (wt w) {k}} :
          Submodule K (PreF K I)) := word_mem_supp rfl
      rw [d_word_of_mul, word_of_mul, dR_θ_mul j k _ hw, map_add, map_add, bar_smul, map_mul,
        bar_θ, ih, σ_zpow hσ, twistBy_θ_mul, add_comm]
      congr 1
      split_ifs
      · rw [bar_word, map_smul, twistBy_word, smul_smul, ← Units.val_mul, ← zpow_add,
          add_neg_cancel, zpow_zero, Units.val_one, one_smul]
      · simp

end CommRing

section Field

variable {I : Type*} {K : Type*} [Field K] {dot : I → I → ℤ} {v : Kˣ} {c : I → K}

/-- `ℐ` is stable under `d_k` when `(θ_k, θ_k) ≠ 0`. -/
theorem d_mem_radical (hdot : ∀ i j, dot i j = dot j i) {k : I} (hc : c k ≠ 0) {x : PreF K I}
    (hx : x ∈ radical dot v c) : d dot v k x ∈ radical dot v c := by
  rw [mem_radical_iff' hdot]
  intro z
  have h := form_θ_mul (dot := dot) (v := v) (c := c) k z x
  rw [form_symm hdot, hx, eq_comm, mul_eq_zero] at h
  exact h.resolve_left hc

variable (σ : K →+* K)

/-- **Lusztig 1.2.12–1.2.15**: `bar` preserves the radical `ℐ` (for a symmetric pairing and
nonzero values `c k = (θ_k, θ_k)`). -/
theorem bar_mem_radical (hdot : ∀ i j, dot i j = dot j i) (hc : ∀ k, c k ≠ 0)
    (hσ : σ (v : K) = ((v⁻¹ : Kˣ) : K)) {x : PreF K I} (hx : x ∈ radical dot v c) :
    bar σ x ∈ radical dot v c := by
  obtain ⟨n, hn⟩ := exists_mem_lenLt x
  induction n generalizing x with
  | zero =>
    rw [supp_lenLt_zero, Submodule.mem_bot] at hn
    rw [hn, map_zero]
    exact Submodule.zero_mem _
  | succ n ih =>
    refine mem_radical_of_dR hdot ?_ fun k => ?_
    · rw [counit_bar, ← form_one, form_symm hdot, hx, map_zero]
    · have h1 := ih (d_mem_radical hdot (hc k) hx) (d_mem_lenLt k n hn)
      rw [bar_d σ hσ] at h1
      have h2 := twistBy_mem_radical (v := v) (c := c) (fun μ => wdot dot μ {k}) h1
      rwa [twistBy_twistBy, show ((fun μ => wdot dot μ {k}) + fun μ => -wdot dot μ {k}) = 0 by
        funext μ; simp, twistBy_zero] at h2

variable (dot v c) in
/-- **The bar map on `f`** (Lusztig 1.2.12; KL I §3.1): the ring endomorphism of `f` induced
by `bar σ`. -/
def barF (hdot : ∀ i j, dot i j = dot j i) (hc : ∀ k, c k ≠ 0)
    (hσ : σ (v : K) = ((v⁻¹ : Kˣ) : K)) : F dot v c →+* F dot v c :=
  Ideal.Quotient.lift (radical dot v c) ((π dot v c : PreF K I →+* F dot v c).comp (bar σ))
    fun _ hx => π_eq_zero_iff.2 (bar_mem_radical σ hdot hc hσ hx)

variable {hdot : ∀ i j, dot i j = dot j i} {hc : ∀ k, c k ≠ 0}
  {hσ : σ (v : K) = ((v⁻¹ : Kˣ) : K)}

theorem barF_π (x : PreF K I) :
    barF dot v c σ hdot hc hσ (π dot v c x) = π dot v c (bar σ x) := rfl

theorem barF_θ (i : I) :
    barF dot v c σ hdot hc hσ (π dot v c (θ i)) = π dot v c (θ i) := by
  rw [barF_π, bar_θ]

theorem barF_smul (a : K) (z : F dot v c) :
    barF dot v c σ hdot hc hσ (a • z) = σ a • barF dot v c σ hdot hc hσ z := by
  obtain ⟨x, rfl⟩ := π_surjective (dot := dot) (v := v) (c := c) z
  rw [← map_smul, barF_π, barF_π, bar_smul, map_smul]

theorem barF_algebraMap (a : K) :
    barF dot v c σ hdot hc hσ (algebraMap K (F dot v c) a) = algebraMap K _ (σ a) := by
  rw [← AlgHom.commutes (π dot v c), barF_π, bar_algebraMap, AlgHom.commutes]

theorem bar_bar (hσ2 : ∀ a, σ (σ a) = a) (x : PreF K I) : bar σ (bar σ x) = x := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul_word w r => rw [bar_smul, bar_smul, bar_word, bar_word, hσ2]

/-- The bar map on `f` is an involution when `σ` is. -/
theorem barF_barF (hσ2 : ∀ a, σ (σ a) = a) (z : F dot v c) :
    barF dot v c σ hdot hc hσ (barF dot v c σ hdot hc hσ z) = z := by
  obtain ⟨x, rfl⟩ := π_surjective (dot := dot) (v := v) (c := c) z
  rw [barF_π, barF_π, bar_bar σ hσ2]

/-! ### Divided powers and `_𝒜 f` -/

theorem σ_qint (hσ : σ (v : K) = ((v⁻¹ : Kˣ) : K)) (h : ℤ) (n : ℕ) :
    σ (qint (v ^ h) n) = qint (v ^ h) n := by
  rw [qint_eq_sum, map_sum]
  simp only [← zpow_mul, σ_zpow hσ]
  rw [← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  congr 2
  push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + k ≤ n)]
  ring

theorem σ_qfact (hσ : σ (v : K) = ((v⁻¹ : Kˣ) : K)) (h : ℤ) (n : ℕ) :
    σ (qfact (v ^ h) n) = qfact (v ^ h) n := by
  rw [qfact, map_prod]
  exact prod_congr rfl fun m _ => σ_qint σ hσ h (m + 1)

theorem bar_dpow (hσ : σ (v : K) = ((v⁻¹ : Kˣ) : K)) (i : I) (a : ℕ) :
    bar σ (dpow dot v i a) = dpow dot v i a := by
  rw [dpow, bar_smul, map_pow, bar_θ, map_inv₀, vi, σ_qfact σ hσ]

/-- **The bar map fixes the divided powers** (Lusztig 1.4.1). -/
theorem barF_dpowF (i : I) (a : ℕ) :
    barF dot v c σ hdot hc hσ (dpowF dot v c i a) = dpowF dot v c i a := by
  rw [dpowF, barF_π, bar_dpow σ hσ]

/-- **The bar map preserves `_𝒜 f`** (Lusztig 1.4.7; KL I §3.1). -/
theorem barF_mem_Af {z : F dot v c} (hz : z ∈ Af dot v c) :
    barF dot v c σ hdot hc hσ z ∈ Af dot v c := by
  have : Af dot v c ≤ (Af dot v c).comap (barF dot v c σ hdot hc hσ) := by
    rw [Af, Subring.closure_le]
    rintro _ (⟨⟨i, a⟩, rfl⟩ | rfl | rfl)
    · show barF dot v c σ hdot hc hσ (dpowF dot v c i a) ∈ Af dot v c
      rw [barF_dpowF]
      exact dpowF_mem_Af i a
    · show barF dot v c σ hdot hc hσ (algebraMap K (F dot v c) (v : K)) ∈ Af dot v c
      rw [barF_algebraMap, hσ, ← zpow_neg_one]
      exact algebraMap_zpow_mem_Af (-1)
    · show barF dot v c σ hdot hc hσ (algebraMap K (F dot v c) ((v⁻¹ : Kˣ) : K)) ∈ Af dot v c
      rw [barF_algebraMap, ← zpow_neg_one, σ_zpow hσ, neg_neg]
      exact algebraMap_zpow_mem_Af 1
  exact this hz

end Field

end PreF

/-! ### `ℚ(v)` and Cartan data -/

theorem aeval_X_inv_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) :
    Polynomial.aeval (RatFunc.X⁻¹ : RatFunc ℚ) p ≠ 0 := by
  have hX : Transcendental ℚ (RatFunc.X : RatFunc ℚ) := by
    rw [← RatFunc.algebraMap_X]
    exact (transcendental_algebraMap_iff (RatFunc.algebraMap_injective ℚ)).2
      (Polynomial.transcendental_X ℚ)
  intro h0
  exact hX (IsAlgebraic.inv_iff.1 ⟨p, hp, h0⟩)

/-- The ring involution `v ↦ v⁻¹` of `ℚ(v)` (KL I: `q^n ↦ q^{-n}`). -/
def barQ : RatFunc ℚ →+* RatFunc ℚ :=
  RatFunc.liftRingHom (Polynomial.aeval (RatFunc.X⁻¹ : RatFunc ℚ)).toRingHom fun _ hp =>
    mem_nonZeroDivisors_of_ne_zero (aeval_X_inv_ne_zero (nonZeroDivisors.ne_zero hp))

theorem barQ_algebraMap (p : Polynomial ℚ) :
    barQ (algebraMap (Polynomial ℚ) (RatFunc ℚ) p) =
      Polynomial.aeval (RatFunc.X⁻¹ : RatFunc ℚ) p := by
  have := RatFunc.liftRingHom_apply_div
    (Polynomial.aeval (RatFunc.X⁻¹ : RatFunc ℚ)).toRingHom
    (fun _ hp => mem_nonZeroDivisors_of_ne_zero (aeval_X_inv_ne_zero (nonZeroDivisors.ne_zero hp)))
    p 1
  rw [map_one, div_one, map_one, div_one] at this
  exact this

theorem barQ_X : barQ (RatFunc.X : RatFunc ℚ) = RatFunc.X⁻¹ := by
  rw [← RatFunc.algebraMap_X, barQ_algebraMap, Polynomial.aeval_X, RatFunc.algebraMap_X]

theorem barQ_vQ : barQ (vQ : RatFunc ℚ) = ((vQ⁻¹ : (RatFunc ℚ)ˣ) : RatFunc ℚ) := by
  rw [vQ_val, barQ_X, Units.val_inv_eq_inv_val, vQ_val]

theorem barQ_barQ (a : RatFunc ℚ) : barQ (barQ a) = a := by
  have : barQ.comp barQ = RingHom.id (RatFunc ℚ) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℚ)) ?_
    refine Polynomial.ringHom_ext (fun q => ?_) ?_
    · have hq : ∀ f : RatFunc ℚ →+* RatFunc ℚ,
          f (algebraMap ℚ (RatFunc ℚ) q) = algebraMap ℚ (RatFunc ℚ) q := fun f =>
        RingHom.congr_fun (Subsingleton.elim (f.comp (algebraMap ℚ (RatFunc ℚ)))
          (algebraMap ℚ (RatFunc ℚ))) q
      have e : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C q) =
          algebraMap ℚ (RatFunc ℚ) q := by
        rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [e, hq, hq]
    · simp only [RingHom.comp_apply, RingHom.id_apply, RatFunc.algebraMap_X, barQ_X, map_inv₀,
        inv_inv]
  exact RingHom.congr_fun this a

namespace CartanDatum

variable {I : Type*} (C : CartanDatum I)

theorem c_ne_zero (i : I) : C.c i ≠ 0 :=
  inv_ne_zero (one_sub_vQ_zpow_ne_zero (by have := C.dot_self_pos i; omega))

/-- **The bar involution of `f` over `ℚ(v)`** for a Cartan datum (Lusztig 1.2.12; KL I §3.1):
the ring involution of `f` fixing every `θ_i` and semilinear for `v ↦ v⁻¹`. -/
def barF : C.F →+* C.F := PreF.barF C.dot vQ C.c barQ C.symm C.c_ne_zero barQ_vQ

theorem barF_θ (i : I) :
    C.barF (PreF.π C.dot vQ C.c (PreF.θ i)) = PreF.π C.dot vQ C.c (PreF.θ i) :=
  PreF.barF_θ barQ i

theorem barF_smul (a : RatFunc ℚ) (z : C.F) : C.barF (a • z) = barQ a • C.barF z :=
  PreF.barF_smul barQ a z

theorem barF_barF (z : C.F) : C.barF (C.barF z) = z := PreF.barF_barF barQ barQ_barQ z

theorem barF_dpowF (i : I) (a : ℕ) :
    C.barF (PreF.dpowF C.dot vQ C.c i a) = PreF.dpowF C.dot vQ C.c i a :=
  PreF.barF_dpowF barQ i a

/-- The bar involution preserves `_𝒜 f` (KL I §3.1). -/
theorem barF_mem_Af {z : C.F} (hz : z ∈ C.Af) : C.barF z ∈ C.Af := PreF.barF_mem_Af barQ hz

end CartanDatum

end Categorification.QuantumGroup


end
