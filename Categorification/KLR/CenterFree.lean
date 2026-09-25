/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Center
import Categorification.Algebra.ParabolicSymmetricFree

/-!
# `R(ν)` is free of rank `(m!)²` over its center, and Noetherian

KL I (arXiv:0803.4121v2), §2.4:

* **Corollary 2.10 (1)**: `R(ν)` is a free module of rank `(m!)²` over its center
  `Z(R(ν)) = Sym(ν)` (`KLRAlgebra.center_free`, `KLRAlgebra.finrank_center`);
* **Corollary 2.11 (1)**: if `k` is Noetherian, then `R(ν)` is left and right Noetherian
  (`KLRAlgebra.isNoetherianRing`, `KLRAlgebra.isNoetherianRing_mulOpposite`).

We work in the generality of the basis theorem (`KLRAlgebra.basis`): `k` an integral domain,
`Q i j (u, v) = P j i (u, v) P i j (v, u)` with all `P i j ≠ 0` (`i ≠ j`). The statements for
the rings of KL I are in the namespace `KL1`.

## Method

* `Sym(ν) ≅ k[x_1, …, x_m]^{G_i}` for any `i ∈ Seq ν`, where `G_i = {w // w • i = i}`, via
  `f ↦ f_i` (`symNuEquivLabelInvariants`); the inverse sends `s` to `(w_j(s))_j`, where
  `w_j • i = j` (`liftInv`; well defined because `S_m` acts transitively on `Seq ν`).
* By the parabolic Artin theorem (`Categorification.exists_isInvBasis_label`), `k[x]` has a
  basis `b_β` over `k[x]^{G_i}` with `|G_i|` elements, so `Pol(ν) = ∏_j k[x]` has the basis
  `1_j ⊗ w_j(b_β)` over `Sym(ν)`, of size `|Seq ν| · |G_i| = m!` (orbit–stabiliser).
* Combined with Proposition 2.7 (`R(ν) = ⊕_w ψ_{ρ w} Pol(ν)`) and centrality of `Sym(ν)`
  (Theorem 2.9) this gives a basis `ψ_{ρ w} · (1_j ⊗ w_j(b_β))` of `R(ν)` over its center.
* For Noetherianity we use the central subalgebra of *diagonal* symmetric polynomials
  `{∑_i f(x) 1_i | f ∈ k[x]^{S_m}} ≅ k[x]^{S_m} ≅ k[e_1, …, e_m]` (fundamental theorem of
  symmetric polynomials), which is Noetherian by the Hilbert basis theorem and over which
  `R(ν)` is finite (Proposition 2.7 and Artin's theorem); left and right ideals are submodules
  over it.

## Main results

* `KLRAlgebra.symNuEquivLabelInvariants` : `Sym(ν) ≃ₐ k[x]^{G_i}`.
* `KLRAlgebra.exists_symNuBasis`, `KLRAlgebra.finrank_symNu_pol` : `Pol(ν)` is free of rank
  `m!` over `Sym(ν)` (any commutative ring `k`).
* `KLRAlgebra.exists_centerBasis`, `KLRAlgebra.center_free`, `KLRAlgebra.finrank_center` :
  **Corollary 2.10 (1)**.
* `KLRAlgebra.isNoetherianRing`, `KLRAlgebra.isNoetherianRing_mulOpposite` :
  **Corollary 2.11 (1)**.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA PolyRep

universe uI uk

variable {I : Type uI} [DecidableEq I] {k : Type uk} [CommRing k] {ν : Multiset I}

local notation "m" => Multiset.card ν

namespace Seq

omit [DecidableEq I] in
theorem smul_eq_self_iff (w : Perm (Fin m)) (i : Seq ν) : w • i = i ↔ i.1 ∘ w = i.1 := by
  constructor
  · intro h
    funext a
    have := congrArg (fun j : Seq ν => j.1 (w a)) h
    simp only [smul_apply, Equiv.symm_apply_apply] at this
    exact this.symm
  · intro h
    apply Subtype.ext
    funext a
    rw [smul_apply]
    conv_rhs => rw [← w.apply_symm_apply a]
    exact (congrFun h (w.symm a)).symm

/-- A permutation carrying `i` to `j` (`S_m` acts transitively on `Seq ν`). -/
noncomputable def toPerm (i j : Seq ν) : Perm (Fin m) := (exists_smul_eq i j).choose

theorem toPerm_smul (i j : Seq ν) : toPerm i j • i = j := (exists_smul_eq i j).choose_spec

end Seq

namespace KLRAlgebra

/-! ### `Sym(ν)` and the invariants of a stabiliser -/

omit [DecidableEq I] in
theorem rename_eq_of_smul_eq {i : Seq ν} {s : MvPolynomial (Fin m) k}
    (hs : s ∈ labelInvariants k i.1) {a b : Perm (Fin m)} (h : a • i = b • i) :
    rename a s = rename b s := by
  have hab : (b⁻¹ * a) • i = i := by rw [mul_smul, h, inv_smul_smul]
  have := hs _ ((Seq.smul_eq_self_iff _ _).1 hab)
  calc rename a s = rename (b * (b⁻¹ * a)) s := by rw [mul_inv_cancel_left]
    _ = rename b (rename (b⁻¹ * a) s) := by rw [rename_rename, Perm.coe_mul]
    _ = rename b s := by rw [this]

omit [DecidableEq I] in
theorem apply_mem_labelInvariants {f : Pol k ν} (hf : f ∈ symNu k ν) (i : Seq ν) :
    f i ∈ labelInvariants k i.1 := fun g hg => by
  rw [← hf g i, (Seq.smul_eq_self_iff g i).2 hg]

/-- The element `(w_j(s))_j` of `Pol(ν)`, where `w_j • i = j`. -/
noncomputable def liftInv (i : Seq ν) (s : MvPolynomial (Fin m) k) : Pol k ν :=
  fun j => rename (Seq.toPerm i j) s

theorem liftInv_mem {i : Seq ν} {s : MvPolynomial (Fin m) k} (hs : s ∈ labelInvariants k i.1) :
    liftInv i s ∈ symNu k ν := by
  intro w j
  simp only [liftInv, rename_rename, ← Perm.coe_mul]
  exact rename_eq_of_smul_eq hs (by rw [Seq.toPerm_smul, mul_smul, Seq.toPerm_smul])

theorem liftInv_self {i : Seq ν} {s : MvPolynomial (Fin m) k} (hs : s ∈ labelInvariants k i.1) :
    liftInv i s i = s := by
  have := rename_eq_of_smul_eq hs (a := Seq.toPerm i i) (b := 1)
    (by rw [Seq.toPerm_smul, one_smul])
  rw [liftInv, this, Perm.coe_one, rename_id_apply]

theorem eq_liftInv {f : Pol k ν} (hf : f ∈ symNu k ν) (i : Seq ν) : f = liftInv i (f i) := by
  funext j
  conv_lhs => rw [← Seq.toPerm_smul i j]
  exact hf _ i

theorem liftInv_zero (i : Seq ν) : liftInv i (0 : MvPolynomial (Fin m) k) = 0 := by
  funext j; simp [liftInv]

/-- `Sym(ν) ≅ k[x_1, …, x_m]^{G_i}`, `f ↦ f_i`, for any `i ∈ Seq ν`, where
`G_i = {w // i ∘ w = i}` is the stabiliser of `i`. -/
noncomputable def symNuEquivLabelInvariants (i : Seq ν) :
    symNu k ν ≃ₐ[k] labelInvariants k i.1 :=
  AlgEquiv.ofBijective
    (((Pi.evalAlgHom k (fun _ : Seq ν => MvPolynomial (Fin m) k) i).comp
      (symNu k ν).val).codRestrict _ fun f => apply_mem_labelInvariants f.2 i)
    ⟨fun f g h => by
      have h' : (f : Pol k ν) i = (g : Pol k ν) i := congrArg Subtype.val h
      apply Subtype.ext
      rw [eq_liftInv f.2 i, eq_liftInv g.2 i, h'],
    fun s => ⟨⟨liftInv i s, liftInv_mem s.2⟩, Subtype.ext (liftInv_self s.2)⟩⟩

@[simp] theorem symNuEquivLabelInvariants_apply (i : Seq ν) (f : symNu k ν) :
    (symNuEquivLabelInvariants i f : MvPolynomial (Fin m) k) = (f : Pol k ν) i := rfl

/-! ### `Pol(ν)` over `Sym(ν)` -/

section PolBasis

variable (i : Seq ν) {ι : Type*} [Fintype ι] (b : ι → MvPolynomial (Fin (Multiset.card ν)) k)

/-- The element `1_j ⊗ w_j(b_β)` of `Pol(ν)`. -/
noncomputable def polElt (q : Seq ν × ι) : Pol k ν :=
  Pi.single q.1 (rename (Seq.toPerm i q.1) (b q.2))

theorem mul_single (f : Pol k ν) (j : Seq ν) (p : MvPolynomial (Fin m) k) :
    f * Pi.single j p = Pi.single j (f j * p) := by
  funext t
  by_cases h : t = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem single_sum {κ : Type*} [Fintype κ] (j : Seq ν) (x : κ → MvPolynomial (Fin m) k) :
    (Pi.single j (∑ β, x β) : Pol k ν) = ∑ β, Pi.single j (x β) := by
  funext t
  by_cases h : t = j
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem exists_polElt_expansion
    (hspan : ∀ p : MvPolynomial (Fin m) k, ∃ g : ι → MvPolynomial (Fin m) k,
      (∀ β, g β ∈ labelInvariants k i.1) ∧ ∑ β, g β * b β = p) (F : Pol k ν) :
    ∃ s : Seq ν × ι → MvPolynomial (Fin m) k, (∀ q, s q ∈ labelInvariants k i.1) ∧
      ∑ q, liftInv i (s q) * polElt i b q = F := by
  choose g hg hgp using fun j => hspan (rename ⇑(Seq.toPerm i j)⁻¹ (F j))
  refine ⟨fun q => g q.1 q.2, fun q => hg _ _, ?_⟩
  simp only [polElt, mul_single, liftInv]
  rw [Fintype.sum_prod_type]
  conv_rhs => rw [← Finset.univ_sum_single F]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← single_sum]
  simp only [← map_mul, ← map_sum, hgp j, rename_rename, ← Perm.coe_mul, mul_inv_cancel,
    Perm.coe_one, rename_id_apply]

theorem eq_zero_of_sum_polElt
    (hind : ∀ g : ι → MvPolynomial (Fin m) k, (∀ β, g β ∈ labelInvariants k i.1) →
      ∑ β, g β * b β = 0 → ∀ β, g β = 0)
    (f : Seq ν × ι → Pol k ν) (hf : ∀ q, f q ∈ symNu k ν)
    (h : ∑ q, f q * polElt i b q = 0) (q : Seq ν × ι) : f q = 0 := by
  obtain ⟨t, β⟩ := q
  have ht := congrFun h t
  simp only [polElt, mul_single, Finset.sum_apply, Pi.zero_apply, Fintype.sum_prod_type] at ht
  rw [Finset.sum_eq_single t (fun j _ hj => by simp [Pi.single_apply, Ne.symm hj])
    (by simp)] at ht
  simp only [Pi.single_eq_same] at ht
  have h2 : ∀ β, f (t, β) t = rename (Seq.toPerm i t) (f (t, β) i) := fun β => by
    have := hf (t, β) (Seq.toPerm i t) i
    rwa [Seq.toPerm_smul] at this
  simp only [h2, ← map_mul, ← map_sum] at ht
  have h3 := rename_injective _ (Seq.toPerm i t).injective (ht.trans (map_zero _).symm)
  have h4 := hind (fun β => f (t, β) i) (fun β => apply_mem_labelInvariants (hf _) i) h3 β
  rw [eq_liftInv (hf (t, β)) i, h4, liftInv_zero]

/-- The basis `1_j ⊗ w_j(b_β)` of `Pol(ν)` over `Sym(ν)`, built from a basis `b` of `k[x]`
over the invariants of the stabiliser of `i`. -/
noncomputable def polBasisOfInv
    (hind : ∀ g : ι → MvPolynomial (Fin m) k, (∀ β, g β ∈ labelInvariants k i.1) →
      ∑ β, g β * b β = 0 → ∀ β, g β = 0)
    (hspan : ∀ p : MvPolynomial (Fin m) k, ∃ g : ι → MvPolynomial (Fin m) k,
      (∀ β, g β ∈ labelInvariants k i.1) ∧ ∑ β, g β * b β = p) :
    Basis (Seq ν × ι) (symNu k ν) (Pol k ν) :=
  Basis.mk (v := polElt i b)
    (Fintype.linearIndependent_iff.2 fun c hc q => Subtype.ext <|
      eq_zero_of_sum_polElt i b hind (fun q => c q) (fun q => (c q).2)
        (by simpa [Subalgebra.smul_def] using hc) q)
    (fun F _ => by
      obtain ⟨s, hs, hsF⟩ := exists_polElt_expansion i b hspan F
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨fun q => ⟨liftInv i (s q), liftInv_mem (hs q)⟩,
        by simpa [Subalgebra.smul_def] using hsF⟩)

end PolBasis

/-- Orbit–stabiliser: `|Seq ν| · |G_i| = m!`. -/
theorem card_seq_mul_card_stab (i : Seq ν) :
    Fintype.card (Seq ν) * Fintype.card {g : Perm (Fin m) // i.1 ∘ g = i.1} =
      (Multiset.card ν).factorial := by
  have h1 := (MulAction.stabilizer (Perm (Fin m)) i).card_mul_index
  rw [MulAction.index_stabilizer_of_transitive] at h1
  have h2 : Nat.card (MulAction.stabilizer (Perm (Fin m)) i) =
      Fintype.card {g : Perm (Fin m) // i.1 ∘ g = i.1} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by
      rw [MulAction.mem_stabilizer_iff, Seq.smul_eq_self_iff])
  rw [← h2, ← Nat.card_eq_fintype_card (α := Seq ν), mul_comm, h1, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]

/-- `Pol(ν)` is a free `Sym(ν)`-module with a basis of `m!` elements (any commutative ring). -/
theorem exists_symNuBasis :
    ∃ (ι : Type uI) (_ : Fintype ι), Fintype.card ι = (Multiset.card ν).factorial ∧
      Nonempty (Basis ι (symNu k ν) (Pol k ν)) := by
  let i : Seq ν := Classical.arbitrary _
  obtain ⟨ι, _, b, hcard, hind, hspan⟩ := exists_isInvBasis_label k i.1
  refine ⟨Seq ν × ι, inferInstance, ?_, ⟨polBasisOfInv i b hind hspan⟩⟩
  rw [Fintype.card_prod, hcard, card_seq_mul_card_stab]

instance symNu_pol_free : Module.Free (symNu k ν) (Pol k ν) := by
  obtain ⟨ι, _, -, ⟨b⟩⟩ := exists_symNuBasis (k := k) (ν := ν)
  exact Module.Free.of_basis b

instance symNu_pol_finite : Module.Finite (symNu k ν) (Pol k ν) := by
  obtain ⟨ι, _, -, ⟨b⟩⟩ := exists_symNuBasis (k := k) (ν := ν)
  exact Module.Finite.of_basis b

/-- `Pol(ν)` has rank `m!` over `Sym(ν)`. -/
theorem finrank_symNu_pol [Nontrivial k] :
    Module.finrank (symNu k ν) (Pol k ν) = (Multiset.card ν).factorial := by
  obtain ⟨ι, _, hcard, ⟨b⟩⟩ := exists_symNuBasis (k := k) (ν := ν)
  rw [Module.finrank_eq_card_basis b, hcard]

/-! ### `R(ν)` over its center: Corollary 2.10 (1) -/

section Center

variable [IsDomain k] {Q : I → I → MvPolynomial (Fin 2) k}
  {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hPQ hP in
theorem polNu_mul_ψw_mul_polNu {g : Pol k ν} (hg : g ∈ symNu k ν) (σ : List ℕ) (E : Pol k ν) :
    (polNu g : KLRAlgebra k Q ν) * (ψw σ * polNu E) = ψw σ * polNu (g * E) := by
  rw [← mul_assoc, ← (Subalgebra.mem_center_iff.1 (polNu_mem_center hPQ hP hg) (ψw σ)),
    mul_assoc, ← map_mul]

variable (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)
  (i : Seq ν) {ι : Type*} [Fintype ι] (b : ι → MvPolynomial (Fin (Multiset.card ν)) k)

/-- The element `ψ_{ρ w} · (1_j ⊗ w_j(b_β))` of `R(ν)`. -/
noncomputable def centerElt (q : Perm (Fin m) × (Seq ν × ι)) : KLRAlgebra k Q ν :=
  ψw (ρ q.1) * polNu (polElt i b q.2)

/-- The basis of `R(ν)` over its center, built from a basis `b` of `k[x]` over the invariants
of the stabiliser of `i`. -/
noncomputable def centerBasisOfInv
    (hind : ∀ g : ι → MvPolynomial (Fin m) k, (∀ β, g β ∈ labelInvariants k i.1) →
      ∑ β, g β * b β = 0 → ∀ β, g β = 0)
    (hspan : ∀ p : MvPolynomial (Fin m) k, ∃ g : ι → MvPolynomial (Fin m) k,
      (∀ β, g β ∈ labelInvariants k i.1) ∧ ∑ β, g β * b β = p) :
    Basis (Perm (Fin m) × (Seq ν × ι)) (Subalgebra.center k (KLRAlgebra k Q ν))
      (KLRAlgebra k Q ν) :=
  Basis.mk (v := centerElt ρ i b)
    (Fintype.linearIndependent_iff.2 fun c hc q => by
      choose f hf hfc using fun q => (mem_center_iff hPQ hP).1 (c q).2
      have key : ∀ q, c q • centerElt (Q := Q) ρ i b q =
          ψw (ρ q.1) * polNu (f q * polElt i b q.2) := fun q => by
        rw [Subalgebra.smul_def, smul_eq_mul, centerElt, ← hfc q,
          polNu_mul_ψw_mul_polNu hPQ hP (hf q)]
      rw [Fintype.sum_prod_type] at hc
      simp only [key] at hc
      simp only [← Finset.mul_sum, ← map_sum] at hc
      have h0 := eq_zero_of_sum_ψw_mul_polNu_eq_zero hPQ hP ρ hρ _ hc
      have h1 : f q = 0 := eq_zero_of_sum_polElt i b hind (fun q' => f (q.1, q'))
        (fun q' => hf _) (congrFun h0 q.1) q.2
      apply Subtype.ext
      rw [← hfc q, h1, map_zero, ZeroMemClass.coe_zero])
    (fun r _ => by
      obtain ⟨c, hc⟩ := exists_sum_ψw_mul_polNu ρ hρ r
      choose s hs hsc using fun w => exists_polElt_expansion i b hspan (c w)
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun q => ⟨polNu (liftInv i (s q.1 q.2)),
        polNu_mem_center hPQ hP (liftInv_mem (hs _ _))⟩, ?_⟩
      simp only [Subalgebra.smul_def, smul_eq_mul, centerElt]
      rw [Fintype.sum_prod_type]
      simp only [polNu_mul_ψw_mul_polNu hPQ hP (liftInv_mem (hs _ _))]
      simp only [← Finset.mul_sum, ← map_sum, hsc, hc])

theorem centerBasisOfInv_apply (hind) (hspan) (q : Perm (Fin m) × (Seq ν × ι)) :
    centerBasisOfInv hPQ hP ρ hρ i b hind hspan q =
      ψw (ρ q.1) * polNu (Pi.single q.2.1 (rename (Seq.toPerm i q.2.1) (b q.2.2))) := by
  simp [centerBasisOfInv, centerElt, polElt]

omit hρ in
include hPQ hP in
/-- **KL I, Corollary 2.10 (1)**: `R(ν)` is a free module over its center with a basis of
`(m!)²` elements. -/
theorem exists_centerBasis :
    ∃ (ι : Type uI) (_ : Fintype ι), Fintype.card ι = (Multiset.card ν).factorial ^ 2 ∧
      Nonempty (Basis ι (Subalgebra.center k (KLRAlgebra k Q ν)) (KLRAlgebra k Q ν)) := by
  let i : Seq ν := Classical.arbitrary _
  obtain ⟨ι, _, b, hcard, hind, hspan⟩ := exists_isInvBasis_label k i.1
  refine ⟨Perm (Fin m) × (Seq ν × ι), inferInstance, ?_,
    ⟨centerBasisOfInv hPQ hP (fun w => canWord m w)
      (fun w => ⟨isReduced_canWord m w, wordProd_canWord m w⟩) i b hind hspan⟩⟩
  rw [Fintype.card_prod, Fintype.card_prod, hcard, card_seq_mul_card_stab, Fintype.card_perm,
    Fintype.card_fin, sq]

omit hρ in
include hPQ hP in
/-- **KL I, Corollary 2.10 (1)**: `R(ν)` is a free module over its center. -/
theorem center_free :
    Module.Free (Subalgebra.center k (KLRAlgebra k Q ν)) (KLRAlgebra k Q ν) := by
  obtain ⟨ι, _, -, ⟨b⟩⟩ := exists_centerBasis (ν := ν) hPQ hP
  exact Module.Free.of_basis b

omit hρ in
include hPQ hP in
/-- `R(ν)` is a finite module over its center. -/
theorem center_finite :
    Module.Finite (Subalgebra.center k (KLRAlgebra k Q ν)) (KLRAlgebra k Q ν) := by
  obtain ⟨ι, _, -, ⟨b⟩⟩ := exists_centerBasis (ν := ν) hPQ hP
  exact Module.Finite.of_basis b

omit hρ in
include hPQ hP in
/-- **KL I, Corollary 2.10 (1)**: the rank of `R(ν)` over its center is `(m!)²`. -/
theorem finrank_center :
    Module.finrank (Subalgebra.center k (KLRAlgebra k Q ν)) (KLRAlgebra k Q ν) =
      (Multiset.card ν).factorial ^ 2 := by
  obtain ⟨ι, _, hcard, ⟨b⟩⟩ := exists_centerBasis (ν := ν) hPQ hP
  haveI : Nontrivial (KLRAlgebra k Q ν) := (polNu_injective (ν := ν) hPQ).nontrivial
  rw [Module.finrank_eq_card_basis b, hcard]

end Center

/-! ### Noetherianity: Corollary 2.11 (1) -/

section Noetherian

variable (Q : I → I → MvPolynomial (Fin 2) k)

variable (k ν) in
/-- The diagonal embedding `k[x_1, …, x_m] → R(ν)`, `f ↦ ∑_i f(x) 1_i`. -/
noncomputable def diagHom : MvPolynomial (Fin m) k →ₐ[k] KLRAlgebra k Q ν :=
  polNu.comp (Pi.constAlgHom k (Seq ν) (MvPolynomial (Fin m) k))

variable (k ν) in
/-- The subalgebra of diagonal symmetric polynomials `{∑_i f(x) 1_i | f ∈ k[x]^{S_m}}`. -/
noncomputable def diagSym : Subalgebra k (KLRAlgebra k Q ν) :=
  (symmetricSubalgebra (Fin m) k).map (diagHom k ν Q)

omit [DecidableEq I] in
theorem const_mem_symNu {s : MvPolynomial (Fin m) k} (hs : s.IsSymmetric) :
    (Function.const (Seq ν) s) ∈ symNu k ν := fun w _ => (hs w).symm

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hPQ hP in
theorem diagSym_le_center : diagSym k ν Q ≤ Subalgebra.center k (KLRAlgebra k Q ν) := by
  rintro _ ⟨s, hs, rfl⟩
  exact polNu_mem_center hPQ hP (const_mem_symNu ((mem_symmetricSubalgebra _).1 hs))

omit [IsDomain k] in
include hPQ in
theorem diagHom_injective : Function.Injective (diagHom k ν Q) :=
  (polNu_injective hPQ).comp Function.const_injective

/-- `diagSym ≅ k[x]^{S_m} ≅ k[e_1, …, e_m]`. -/
noncomputable def diagSymEquiv : MvPolynomial (Fin m) k ≃ₐ[k] diagSym k ν Q :=
  (AlgEquiv.ofBijective (esymmAlgHom (Fin m) k m) (esymmAlgHom_fin_bijective k m)).trans
    (Subalgebra.equivMapOfInjective _ _ (diagHom_injective Q hPQ))

omit [IsDomain k] in
theorem diagHom_apply (s : MvPolynomial (Fin m) k) :
    diagHom k ν Q s = polNu (Function.const (Seq ν) s) := rfl

include hPQ hP in
/-- `R(ν)` is a finite module over the diagonal symmetric polynomials: it is spanned by the
elements `ψ_{w} · x^u 1_j` with `x^u` a staircase monomial (Proposition 2.7 and Artin's
theorem). -/
theorem diagSym_finite : Module.Finite (diagSym k ν Q) (KLRAlgebra k Q ν) := by
  let ρ : Perm (Fin m) → List ℕ := fun w => canWord m w
  have hρ : ∀ w, IsReduced m (ρ w) ∧ wordProd m (ρ w) = w :=
    fun w => ⟨isReduced_canWord m w, wordProd_canWord m w⟩
  let gen : Perm (Fin m) × Seq ν × {u : Fin m → ℕ // ∀ a, u a ≤ a} → KLRAlgebra k Q ν :=
    fun q => ψw (ρ q.1) * polNu (Pi.single q.2.1 (stairMonomial k q.2.2.1))
  refine ⟨(Submodule.fg_def).2 ⟨Set.range gen, Set.finite_range gen, ?_⟩⟩
  rw [eq_top_iff]
  intro r _
  obtain ⟨c, hc⟩ := exists_sum_ψw_mul_polNu ρ hρ r
  choose g hg hgc using fun w j => (staircase_indep_and_span m k).2 (c w j)
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun q => ⟨diagHom k ν Q (g q.1 q.2.1 q.2.2),
    Subalgebra.mem_map.2 ⟨_, (mem_symmetricSubalgebra _).2 (hg _ _ _), rfl⟩⟩, ?_⟩
  simp only [Subalgebra.smul_def, smul_eq_mul, diagHom_apply, gen,
    polNu_mul_ψw_mul_polNu hPQ hP (const_mem_symNu (hg _ _ _)), Fintype.sum_prod_type,
    mul_single, Function.const_apply]
  simp only [← Finset.mul_sum, ← map_sum, ← single_sum, hgc, Finset.univ_sum_single, hc]

include hPQ hP in
/-- `R(ν)` is a Noetherian module over the diagonal symmetric polynomials if `k` is
Noetherian (Hilbert basis theorem). -/
theorem isNoetherian_diagSym [IsNoetherianRing k] :
    IsNoetherian (diagSym k ν Q) (KLRAlgebra k Q ν) := by
  haveI : IsNoetherianRing (diagSym k ν Q) :=
    isNoetherianRing_of_ringEquiv _ (diagSymEquiv Q hPQ).toRingEquiv
  haveI := diagSym_finite (ν := ν) Q hPQ hP
  infer_instance

include hPQ hP in
/-- **KL I, Corollary 2.11 (1)**, left ideals: if `k` is Noetherian, `R(ν)` is left
Noetherian. -/
theorem isNoetherianRing [IsNoetherianRing k] : IsNoetherianRing (KLRAlgebra k Q ν) :=
  isNoetherian_of_tower (diagSym k ν Q) (isNoetherian_diagSym (ν := ν) Q hPQ hP)

include hPQ hP in
/-- **KL I, Corollary 2.11 (1)**, right ideals: if `k` is Noetherian, `R(ν)` is right
Noetherian (its opposite ring is left Noetherian). -/
theorem isNoetherianRing_mulOpposite [IsNoetherianRing k] :
    IsNoetherianRing (KLRAlgebra k Q ν)ᵐᵒᵖ := by
  haveI : IsScalarTower (diagSym k ν Q) (KLRAlgebra k Q ν)ᵐᵒᵖ (KLRAlgebra k Q ν)ᵐᵒᵖ :=
    ⟨fun a x y => by
      show (a • x) * y = a • (x * y)
      apply MulOpposite.unop_injective
      rw [MulOpposite.unop_mul, MulOpposite.unop_smul, MulOpposite.unop_smul,
        MulOpposite.unop_mul, Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul,
        smul_eq_mul, ← mul_assoc, ← mul_assoc,
        Subalgebra.mem_center_iff.1 (diagSym_le_center (ν := ν) Q hPQ hP a.2)]⟩
  haveI := isNoetherian_diagSym (ν := ν) Q hPQ hP
  exact isNoetherian_of_tower (diagSym k ν Q)
    (isNoetherian_of_linearEquiv (MulOpposite.opLinearEquiv (diagSym k ν Q)))

end Noetherian

end KLRAlgebra

/-! ### The rings of KL I -/

namespace KL1

open KLRAlgebra

variable {Γ : SimpleGraph I} [DecidableRel Γ.Adj] [IsDomain k]

/-- **KL I, Corollary 2.10 (1)** for the rings `R(ν)` of KL I (over `ℤ`, or any integral
domain): `R(ν)` is a free module over its center with a basis of `(m!)²` elements. -/
theorem exists_centerBasis :
    ∃ (ι : Type uI) (_ : Fintype ι), Fintype.card ι = (Multiset.card ν).factorial ^ 2 ∧
      Nonempty (Basis ι (Subalgebra.center k (R1 k Γ ν)) (R1 k Γ ν)) :=
  KLRAlgebra.exists_centerBasis (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b)

/-- **KL I, Corollary 2.10 (1)**: `R(ν)` is a free module over its center. -/
theorem center_free : Module.Free (Subalgebra.center k (R1 k Γ ν)) (R1 k Γ ν) :=
  KLRAlgebra.center_free (klQ_eq_klP (Γ := Γ) stdOrient_spec) (fun a b _ => klP_ne_zero _ a b)

/-- **KL I, Corollary 2.10 (1)**: the rank of `R(ν)` over its center is `(m!)²`. -/
theorem finrank_center :
    Module.finrank (Subalgebra.center k (R1 k Γ ν)) (R1 k Γ ν) =
      (Multiset.card ν).factorial ^ 2 :=
  KLRAlgebra.finrank_center (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b)

/-- **KL I, Corollary 2.11 (1)**: if `k` is Noetherian (e.g. `ℤ` or a field), `R(ν)` is left
Noetherian. -/
theorem isNoetherianRing [IsNoetherianRing k] : IsNoetherianRing (R1 k Γ ν) :=
  KLRAlgebra.isNoetherianRing _ (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b)

/-- **KL I, Corollary 2.11 (1)**: if `k` is Noetherian, `R(ν)` is right Noetherian. -/
theorem isNoetherianRing_mulOpposite [IsNoetherianRing k] : IsNoetherianRing (R1 k Γ ν)ᵐᵒᵖ :=
  KLRAlgebra.isNoetherianRing_mulOpposite _ (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b)

end KL1

end Categorification.KLR
