/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicEF

/-!
# First-strand coordinates and the map B

The first-strand decomposition underlying Kang–Kashiwara, arXiv:1102.4677v4,
Proposition 3.7 and Corollary 3.8. Its final coordinate gives the coordinate form of
the map `B` in §5.2, in the library's crossing convention.

Here the basis word is `ψ_{a-1} ⋯ ψ_0`. Under `ψ = -τ`, the final coordinate
is `(-1)^n` times the coefficient of the paper's `τ_n ⋯ τ_1`, where `n = |β|`.
The kernel statements below use the lower-coordinate submodule; they do not yet
identify it with the image of the balanced tensor-product map `E`.
-/

namespace Categorification.KLR

open Equiv TypeA

section ShuffleFirst

/-- The code of the word `[0, …, a-1]` in `S_{n+1}`. -/
def firstCode : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, a => (if n < a then n else n + 1) :: firstCode n a

@[simp] theorem length_firstCode (n a : ℕ) : (firstCode n a).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [firstCode, ih]

theorem isCode_firstCode (n a : ℕ) : IsCode (firstCode n a) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    exact ⟨by simp only [length_firstCode]; split_ifs <;> omega, ih⟩

theorem codeWord_firstCode (n a : ℕ) :
    codeWord (firstCode n a) = List.range' 0 (min n a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [firstCode, codeWord_cons, ih, length_firstCode]
    by_cases h : n < a
    · rw [ite_eq_left h, show n + 1 - n = 1 by omega, descRun_one,
        Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), List.range'_concat]
      simp
    · rw [ite_eq_right h, Nat.sub_self, descRun_zero, List.append_nil,
        Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

/-- The ascending first-strand word is the canonical word. -/
theorem canWord_range' {m n a : ℕ} (hm : n + 1 = m) (ha : a ≤ n) :
    canWord m (wordProd m (List.range' 0 a)) = List.range' 0 a := by
  have hc := codeWord_firstCode n a
  rw [Nat.min_eq_right ha] at hc
  rw [← hc, canWord_wordProd_codeWord (isCode_firstCode n a) (by simp; omega)]

theorem wordProd_descRun_zero_val {m a : ℕ} (ha : a < m) (y : Fin m) :
    (wordProd m (descRun 0 a) y).val =
      if y.val = 0 then a else if y.val ≤ a then y.val - 1 else y.val := by
  have h := wordProd_descRun_symm_val (b := 0) (l := a) (by omega)
    (wordProd m (descRun 0 a) y)
  rw [Equiv.symm_apply_apply] at h
  have hy := y.2
  have hz := (wordProd m (descRun 0 a) y).2
  split_ifs at h ⊢ <;> omega

variable {n n' m : ℕ} (h : n + 1 = m) (hb : n' + n = m) (h1 : n' = 1)

/-- The singleton first block. -/
def firstB : Fin m := blockEquiv hb (Sum.inl ⟨0, h1 ▸ Nat.one_pos⟩)

include h1 in
theorem mem_range_inr_iff (w : Perm (Fin m)) (z : Fin m) :
    (∃ x, w⁻¹ (blockEquiv hb (Sum.inr x)) = z) ↔ z ≠ w⁻¹ (firstB hb h1) := by
  constructor
  · rintro ⟨x, rfl⟩ hx
    exact Sum.inr_ne_inl ((blockEquiv hb).injective (w⁻¹.injective hx))
  · intro hz
    rcases hs : (blockEquiv hb).symm (w z) with x | y
    · exfalso
      apply hz
      have hx : x = ⟨0, by omega⟩ := Fin.ext (by have := x.2; omega)
      rw [firstB, ← hx, ← hs, Equiv.apply_symm_apply]
      exact (w.symm_apply_apply z).symm
    · refine ⟨y, ?_⟩
      rw [← hs, Equiv.apply_symm_apply]
      exact w.symm_apply_apply z

include h1 in
theorem eq_of_isShuffle_first {u v : Perm (Fin m)} (hu : IsShuffle hb u)
    (hv : IsShuffle hb v) (he : u⁻¹ (firstB hb h1) = v⁻¹ (firstB hb h1)) : u = v := by
  have hf : (fun x => u⁻¹ (blockEquiv hb (Sum.inr x))) =
      (fun x => v⁻¹ (blockEquiv hb (Sum.inr x))) := by
    rw [← StrictMono.range_inj_of_wellFoundedLT hu.2 hv.2]
    ext z
    simp only [Set.mem_range]
    rw [mem_range_inr_iff hb h1, mem_range_inr_iff hb h1, he]
  have hinv : u⁻¹ = v⁻¹ := by
    ext1 z
    obtain ⟨s, rfl⟩ := (blockEquiv hb).surjective z
    rcases s with x | y
    · have hx : x = ⟨0, by omega⟩ := Fin.ext (by have := x.2; omega)
      rw [hx]; exact he
    · exact congrFun hf y
  exact inv_injective hinv

/-- The shuffle whose inverse moves the first strand to position `a`. -/
def cycFirst (a : ℕ) : Perm (Fin m) := wordProd m (List.range' 0 a)

theorem cycFirst_inv (a : ℕ) :
    (cycFirst (m := m) a)⁻¹ = wordProd m (descRun 0 a) := by
  rw [cycFirst, descRun, wordProd_reverse]

include h in
theorem cycFirst_inv_val {a : ℕ} (ha : a ≤ n) (y : Fin m) :
    ((cycFirst a)⁻¹ y).val =
      if y.val = 0 then a else if y.val ≤ a then y.val - 1 else y.val := by
  rw [cycFirst_inv, wordProd_descRun_zero_val (by omega)]

include h in
theorem isShuffle_cycFirst {a : ℕ} (ha : a ≤ n) : IsShuffle hb (cycFirst a) := by
  refine ⟨fun x x' hxx' => ?_, fun y y' hyy' => ?_⟩
  · exfalso
    rw [Fin.lt_def] at hxx'
    have := x'.2
    omega
  · rw [Fin.lt_def] at hyy' ⊢
    rw [cycFirst_inv_val h ha, cycFirst_inv_val h ha,
      blockEquiv_inr_val, blockEquiv_inr_val]
    split_ifs <;> omega

include h in
theorem cycFirst_inv_firstB {a : ℕ} (ha : a ≤ n) :
    ((cycFirst a)⁻¹ (firstB hb h1)).val = a := by
  rw [cycFirst_inv_val h ha, firstB, blockEquiv_inl_val]
  simp

/-- The first-strand shuffles, indexed by the destination of the first strand. -/
def shFirst : Fin (n + 1) ≃ Shuffle hb where
  toFun a := ⟨cycFirst a.val, isShuffle_cycFirst h hb (by omega)⟩
  invFun u := ⟨(u.1⁻¹ (firstB hb h1)).val, by have := (u.1⁻¹ (firstB hb h1)).2; omega⟩
  left_inv a := Fin.ext (cycFirst_inv_firstB h hb h1 (by omega))
  right_inv u := Subtype.ext (eq_of_isShuffle_first hb h1
    (isShuffle_cycFirst h hb (by have := (u.1⁻¹ (firstB hb h1)).2; omega)) u.2
    (Fin.ext (by rw [cycFirst_inv_firstB h hb h1 (by
      have := (u.1⁻¹ (firstB hb h1)).2; omega)])))

end ShuffleFirst

section FirstFree

open MvPolynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

namespace KLRAlgebra

variable (i : I) (β : Multiset I)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "N" => Fin (Multiset.card β + 1)

omit [DecidableEq I] in
theorem card_single_add_eq : Multiset.card β + 1 = Multiset.card (Si + β) := by simp

/-- The right free basis element moving the first strand to `a`. -/
theorem rW_shFirst (a : N) :
    (rW (shFirst (card_single_add_eq i β) (Seq.card_add' Si β) (card_single' i) a) : R) =
      ψw (descRun 0 a.val) * oneConcat Q Si β := by
  rw [rW, hatW, hflip_mul, hflip_oneConcat_eq, hflip_ψw]
  congr 2
  change (canWord _ (wordProd _ (List.range' 0 a.val))).reverse = _
  rw [canWord_range' (card_single_add_eq i β) (by omega)]
  rfl

/-- The first-strand free expansion `∑_{a≤n} ψ_{a-1}⋯ψ_0 ι(t_a)`. -/
noncomputable def firstFree (t : N → T) : R :=
  ∑ a, ψw (descRun 0 a.val) * concat Q Si β (t a)

theorem rFree_first_comp_symm (t : N → T) :
    rFree (t ∘ (shFirst (card_single_add_eq i β) (Seq.card_add' Si β)
      (card_single' i)).symm) = firstFree i β t := by
  refine Fintype.sum_equiv
    (shFirst (card_single_add_eq i β) (Seq.card_add' Si β) (card_single' i)).symm _ _
    fun u => ?_
  conv_lhs => rw [← Equiv.apply_symm_apply
    (shFirst (card_single_add_eq i β) (Seq.card_add' Si β) (card_single' i)) u]
  rw [Function.comp_apply, rW_shFirst, mul_assoc, oneConcat_mul_concat,
    Equiv.symm_apply_apply]

theorem firstFree_add (s t : N → T) :
    firstFree i β (s + t) = firstFree i β s + firstFree i β t := by
  simp only [firstFree, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem firstFree_sub (s t : N → T) :
    firstFree i β (s - t) = firstFree i β s - firstFree i β t := by
  simp only [firstFree, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem firstFree_smul (c : k) (t : N → T) :
    firstFree i β (c • t) = c • firstFree i β t := by
  simp only [firstFree, Pi.smul_apply, map_smul, mul_smul_comm, Finset.smul_sum]

@[simp] theorem firstFree_zero : firstFree (Q := Q) i β (0 : N → T) = 0 := by
  simp only [firstFree, Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]

theorem firstFree_mul_oneConcat (t : N → T) :
    firstFree i β t * oneConcat Q Si β = firstFree i β t := by
  simp only [firstFree, Finset.sum_mul, mul_assoc, concat_mul_oneConcat]

theorem firstFree_mul_concat (t : N → T) (c : T) :
    firstFree i β (fun a => t a * c) = firstFree i β t * concat Q Si β c := by
  simp only [firstFree, concat_mul, Finset.sum_mul, mul_assoc]

theorem firstFree_single (a : N) (c : T) :
    firstFree i β (Pi.single a c) = ψw (descRun 0 a.val) * concat Q Si β c := by
  rw [firstFree, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, mul_zero]
  · simp

variable
  (hsym : KLRSymm Q)

include hsym in
/-- Uniqueness of the explicit first-strand coordinates. -/
theorem firstFree_injective : Function.Injective (firstFree (Q := Q) i β) := by
  intro s t h
  have hz : firstFree i β (s - t) = 0 := by rw [firstFree_sub, h, sub_self]
  rw [← rFree_first_comp_symm] at hz
  funext a
  have ha := rfree_injective hsym hz
    (shFirst (card_single_add_eq i β) (Seq.card_add' Si β) (card_single' i) a)
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, Pi.sub_apply, sub_eq_zero] using ha

include hsym in
/-- Existence of the explicit first-strand coordinates. -/
theorem firstFree_span (r : R) :
    ∃ t : N → T, r * oneConcat Q Si β = firstFree i β t := by
  obtain ⟨t, ht⟩ := rfree_span hsym r
  refine ⟨t ∘ shFirst (card_single_add_eq i β) (Seq.card_add' Si β) (card_single' i), ?_⟩
  rw [← rFree_first_comp_symm, ht]
  congr 1
  funext u
  simp only [Function.comp_apply, Equiv.apply_symm_apply]

include hsym in
/-- The cyclotomic submodule is coordinatewise `R(i) ⊗ J`. -/
theorem firstFree_mem_cycL1_iff (a : I → Polynomial k)
    (h1 : 1 < Multiset.card (Si + β)) (hβ : 0 < Multiset.card β) (t : N → T) :
    firstFree i β t ∈ cycL1 a h1 ↔ ∀ b, t b ∈ tJ (Q := Q) i β a := by
  rw [← rFree_first_comp_symm, mem_cycL1_iff hsym i β a h1 hβ]
  constructor
  · intro ht b
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
      ht (shFirst (card_single_add_eq i β) (Seq.card_add' Si β) (card_single' i) b)
  · intro ht u
    exact ht _

/-- Coordinates of the right projection `r e(i,β)`. -/
noncomputable def firstCoord : R →ₗ[k] (N → T) where
  toFun r := (firstFree_span i β hsym r).choose
  map_add' r s := firstFree_injective i β hsym (by
    rw [← (firstFree_span i β hsym (r + s)).choose_spec, firstFree_add,
      ← (firstFree_span i β hsym r).choose_spec,
      ← (firstFree_span i β hsym s).choose_spec, add_mul])
  map_smul' c r := firstFree_injective i β hsym (by
    rw [← (firstFree_span i β hsym (c • r)).choose_spec, firstFree_smul,
      ← (firstFree_span i β hsym r).choose_spec, smul_mul_assoc, RingHom.id_apply])

theorem firstFree_firstCoord (r : R) :
    firstFree i β (firstCoord i β hsym r) = r * oneConcat Q Si β :=
  (firstFree_span i β hsym r).choose_spec.symm

@[simp] theorem firstCoord_firstFree (t : N → T) :
    firstCoord i β hsym (firstFree i β t) = t := by
  apply firstFree_injective i β hsym
  rw [firstFree_firstCoord, firstFree_mul_oneConcat]

theorem firstCoord_mul_concat (r : R) (c : T) :
    firstCoord i β hsym (r * concat Q Si β c) =
      fun a => firstCoord i β hsym r a * c := by
  apply firstFree_injective i β hsym
  rw [firstFree_firstCoord, firstFree_mul_concat, firstFree_firstCoord,
    mul_assoc, concat_mul_oneConcat, mul_assoc, oneConcat_mul_concat]

/-- The final first-strand coordinate (the coordinate form of KK's map `B`). -/
noncomputable def bCoord : R →ₗ[k] T :=
  (LinearMap.proj (Fin.last (Multiset.card β))).comp (firstCoord i β hsym)

@[simp] theorem bCoord_firstFree (t : N → T) :
    bCoord i β hsym (firstFree i β t) = t (Fin.last (Multiset.card β)) := by
  change firstCoord i β hsym (firstFree i β t) _ = _
  rw [firstCoord_firstFree]

theorem bCoord_mul_concat (r : R) (c : T) :
    bCoord i β hsym (r * concat Q Si β c) = bCoord i β hsym r * c := by
  change firstCoord i β hsym (r * concat Q Si β c) _ = _
  rw [firstCoord_mul_concat]
  rfl

/-- A section of the final-coordinate map. -/
theorem bCoord_top (c : T) :
    bCoord i β hsym (ψw (descRun 0 (Multiset.card β)) * concat Q Si β c) = c := by
  have hs := firstFree_single (Q := Q) i β (Fin.last (Multiset.card β)) c
  simp only [Fin.val_last] at hs
  rw [← hs, bCoord_firstFree, Pi.single_eq_same]

/-- The final coordinate map is surjective. -/
theorem bCoord_surjective : Function.Surjective (bCoord i β hsym) :=
  fun c => ⟨_, bCoord_top i β hsym c⟩

/-- Its kernel consists of the lower first-strand summands. -/
theorem bCoord_eq_zero_iff (r : R) :
    bCoord i β hsym r = 0 ↔ ∃ t : N → T,
      t (Fin.last (Multiset.card β)) = 0 ∧ r * oneConcat Q Si β = firstFree i β t := by
  constructor
  · intro hr
    exact ⟨firstCoord i β hsym r, hr, (firstFree_firstCoord i β hsym r).symm⟩
  · rintro ⟨t, ht, hr⟩
    have hc : firstCoord i β hsym r = t :=
      firstFree_injective i β hsym ((firstFree_firstCoord i β hsym r).trans hr)
    change firstCoord i β hsym r _ = 0
    rw [hc, ht]

variable (a : I → Polynomial k)
  (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))
  (hβ : 0 < Multiset.card β)

/-- The final coordinate with coefficients reduced modulo the cyclotomic ideal. -/
noncomputable def bPoly : R →ₗ[k] Polynomial (CycKLR k Q a β) :=
  (thetaL Q i β a).toLinearMap.comp (bCoord i β hsym)

theorem bPoly_firstFree (t : N → T) :
    bPoly i β hsym a (firstFree i β t) =
      thetaL Q i β a (t (Fin.last (Multiset.card β))) := by
  change thetaL Q i β a (bCoord i β hsym (firstFree i β t)) = _
  rw [bCoord_firstFree]

include h1 hβ in
theorem bPoly_eq_zero {r : R} (hr : r ∈ cycL1 a h1) : bPoly i β hsym a r = 0 := by
  have hr' : r * oneConcat Q Si β ∈ cycL1 a h1 :=
    mul_mem_cycL1 a hr (oneConcat_mem_subR1 i β)
  rw [← firstFree_firstCoord i β hsym r,
    firstFree_mem_cycL1_iff i β hsym a h1 hβ] at hr'
  exact (thetaL_eq_zero_iff i β a _).2 (hr' (Fin.last (Multiset.card β)))

/-- The cyclotomic final-coordinate map, the `ψ`-normalized version of `B`.
It is expressed in `R^Λ(β)[t]` and includes right projection to
`e(i,β)`, so it is defined on all of `K_1` and restricts to the corner used in KK §5.2. -/
noncomputable def bMap : KOne Q (Si + β) a h1 →ₗ[k] Polynomial (CycKLR k Q a β) :=
  ((cycL1 a h1).restrictScalars k).liftQ (bPoly i β hsym a)
      (fun _ hr => LinearMap.mem_ker.2 (bPoly_eq_zero i β hsym a h1 hβ hr)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv k (cycL1 a h1)).symm.toLinearMap

@[simp] theorem bMap_mk (r : R) :
    bMap i β hsym a h1 hβ (Submodule.Quotient.mk r) = bPoly i β hsym a r := rfl

/-- The full first-strand crossing lifts each coefficient of `B`. -/
theorem bMap_top (c : T) :
    bMap i β hsym a h1 hβ (Submodule.Quotient.mk
      (ψw (descRun 0 (Multiset.card β)) * concat Q Si β c)) = thetaL Q i β a c := by
  rw [bMap_mk]
  change thetaL Q i β a (bCoord i β hsym _) = _
  rw [bCoord_top]

/-- Surjectivity of the cyclotomic final-coordinate map. -/
theorem bMap_surjective : Function.Surjective (bMap i β hsym a h1 hβ) := by
  intro p
  obtain ⟨c, rfl⟩ := thetaL_surjective i β a p
  exact ⟨_, bMap_top i β hsym a h1 hβ c⟩

/-- Right `R(β)`-linearity, with the target action through the cyclotomic quotient. -/
theorem bMap_act1 (b : KLRAlgebra k Q β) (w : KOne Q (Si + β) a h1) :
    bMap i β hsym a h1 hβ (act1 Q i β a h1 b w) =
      bMap i β hsym a h1 hβ w * Polynomial.C (CycKLR.mk k Q a β b) := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [act1_mk, bMap_mk, bMap_mk]
  change thetaL Q i β a (bCoord i β hsym (r * concat Q Si β (1 ⊗ₜ b))) = _
  rw [bCoord_mul_concat, map_mul, thetaL_one_tmul]
  rfl

/-- The coordinate form of exactness at `K_1`: the kernel of `B` is the sum of the
lower first-strand summands, modulo the cyclotomic submodule. -/
theorem bMap_mk_eq_zero_iff (r : R) :
    bMap i β hsym a h1 hβ (Submodule.Quotient.mk r) = 0 ↔
      ∃ t : N → T, t (Fin.last (Multiset.card β)) = 0 ∧
        r * oneConcat Q Si β - firstFree i β t ∈ cycL1 a h1 := by
  rw [bMap_mk]
  constructor
  · intro hr
    let s := firstCoord i β hsym r
    let t := s - Pi.single (Fin.last (Multiset.card β)) (s (Fin.last (Multiset.card β)))
    refine ⟨t, by simp only [t, Pi.sub_apply, Pi.single_eq_same, sub_self], ?_⟩
    rw [← firstFree_firstCoord i β hsym r, ← firstFree_sub,
      firstFree_mem_cycL1_iff i β hsym a h1 hβ]
    intro b
    change s b - (s b - (Pi.single (Fin.last (Multiset.card β))
      (s (Fin.last (Multiset.card β))) : N → T) b) ∈ _
    rw [sub_sub_cancel]
    by_cases hb : b = Fin.last (Multiset.card β)
    · subst b
      rw [Pi.single_eq_same]
      exact (thetaL_eq_zero_iff i β a _).1 hr
    · rw [Pi.single_eq_of_ne hb]
      exact Submodule.zero_mem _
  · rintro ⟨t, ht, hr⟩
    have hz := bPoly_eq_zero i β hsym a h1 hβ hr
    rw [map_sub, ← firstFree_firstCoord i β hsym r, bPoly_firstFree,
      bPoly_firstFree, ht, map_zero, sub_zero] at hz
    exact hz

end KLRAlgebra

end FirstFree

end Categorification.KLR
