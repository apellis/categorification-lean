/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.PolNu

/-!
# The center of `R(ν)`

KL I (arXiv:0803.4121v2), §2.4: the symmetric group `S_m` acts on
`Pol(ν) = ∏_{i ∈ Seq(ν)} k[x_1, …, x_m]` by permuting strands together with their labels
and dots, `(w · f)_{w • i} = w(f_i)` (`w(x_a) = x_{w a}`), and

* **Theorem 2.9**: the center of `R(ν)` is `Sym(ν) = Pol(ν)^{S_m}` (`center_eq`);
* **Corollary 2.11 (2)**: `R(ν)` is indecomposable: `0` and `1` are its only central
  idempotents (`eq_zero_or_one_of_mem_center`).

We work in the generality of the basis theorem (`KLRAlgebra.basis`): `k` an integral domain,
`Q i j (u, v) = P j i (u, v) P i j (v, u)` with all `P i j ≠ 0` (`i ≠ j`); the statements for
the rings of KL I are `KL1.center_eq` and `KL1.eq_zero_or_one_of_mem_center`.

## Method

The proof differs from the paper's (which reduces to centers of nilHecke rings). It uses the
faithful polynomial representation (`polyRep_injective`) and the expansions of operators in
the skew group ring `Frac(k[x]) ⋊ S_m` (`Categorification.PermExpansion`):

* `Sym(ν)` is central: `polNu f` commutes with `e i` and `x a`, and — through the faithful
  representation — with `ψ j`, because `∂_j(f g) = f ∂_j g` for `s_j`-invariant `f`.
* Conversely, the operator of a central `z` from `Pol_i` to `Pol_t` has an expansion
  `∑_v G v · v`; commuting with the dots forces `G v (x_{v a} - x_a) = 0`, so `G` is supported
  at `v = 1` and the operator is multiplication by a polynomial. Commuting with the `e i` kills
  the off-diagonal components, so `z = polNu g`. Finally, commuting with `ψ_j` applied to `1_i`
  gives `g_{s_j • i} = s_j(g_i)`, and adjacent transpositions generate `S_m`.

## Main definitions

* `KLRAlgebra.symNu k ν` : the subalgebra `Sym(ν)` of `S_m`-invariants of `Pol(ν)`.

## Main results

* `KLRAlgebra.polNu_mem_center` : `Sym(ν) ⊆ Z(R(ν))`.
* `KLRAlgebra.mem_center_iff`, `KLRAlgebra.center_eq` : **Theorem 2.9**.
* `KLRAlgebra.symNuEquivCenter` : `Sym(ν) ≃ₐ Z(R(ν))`.
* `KLRAlgebra.eq_zero_or_one_of_mem_center` : **Corollary 2.11 (2)**.
-/

namespace Categorification.KLR

open Equiv MvPolynomial TypeA PolyRep PermExpansion

variable {I : Type*} {k : Type*} [CommRing k] {ν : Multiset I}

local notation "m" => Multiset.card ν

namespace KLRAlgebra

/-! ### The invariants `Sym(ν)` -/

variable (k ν) in
/-- `Sym(ν) = Pol(ν)^{S_m}`: the families `f = (f_i)_{i ∈ Seq ν}` with
`f_{w • i} = w(f_i)` for all `w ∈ S_m` and all `i`, where `w` acts on `k[x_1, …, x_m]` by
`x_a ↦ x_{w a}`. -/
noncomputable def symNu : Subalgebra k (Pol k ν) where
  carrier := {f | ∀ (w : Perm (Fin m)) (i : Seq ν), f (w • i) = rename w (f i)}
  mul_mem' {f g} hf hg w i := by
    simp only [Set.mem_setOf_eq, Pi.mul_apply] at hf hg ⊢
    rw [hf w i, hg w i, map_mul]
  add_mem' {f g} hf hg w i := by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at hf hg ⊢
    rw [hf w i, hg w i, map_add]
  algebraMap_mem' c w i := by
    simp only [Pi.algebraMap_apply, AlgHom.commutes]

theorem mem_symNu {f : Pol k ν} :
    f ∈ symNu k ν ↔ ∀ (w : Perm (Fin m)) (i : Seq ν), f (w • i) = rename w (f i) := Iff.rfl

/-- Invariance under all of `S_m` follows from invariance under the adjacent transpositions. -/
theorem mem_symNu_of_sadj {f : Pol k ν}
    (h : ∀ (j : ℕ) (i : Seq ν), f (sadj m j • i) = rename (sadj m j) (f i)) :
    f ∈ symNu k ν := by
  have key : ∀ (ρ : List ℕ) (i : Seq ν), f (wordProd m ρ • i) = rename (wordProd m ρ) (f i) := by
    intro ρ
    induction ρ with
    | nil => intro i; simp
    | cons j ρ ih =>
      intro i
      rw [wordProd_cons, mul_smul, h, ih, rename_rename, Perm.coe_mul]
  intro w i
  obtain ⟨ρ, -, rfl⟩ := exists_validWord m w
  exact key ρ i

/-! ### Commutation -/

variable [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}

/-- An element commuting with all generators is central. -/
theorem commute_of_forall_gen {z : KLRAlgebra k Q ν} (he : ∀ i, Commute (e i) z)
    (hx : ∀ a, Commute (x a) z) (hψ : ∀ j, Commute (ψ j) z) (r : KLRAlgebra k Q ν) :
    Commute r z := by
  obtain ⟨F, rfl⟩ := mk_surjective r
  induction F using FreeAlgebra.induction with
  | grade0 c => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_left c z
  | grade1 g =>
    cases g with
    | idem i => exact he i
    | dot a => exact hx a
    | cross j => exact hψ j
  | mul a b ha hb => rw [map_mul]; exact ha.mul_left hb
  | add a b ha hb => rw [map_add]; exact ha.add_left hb

theorem x_commute_polNu (a : Fin m) (f : Pol k ν) : Commute (x a : KLRAlgebra k Q ν) (polNu f) := by
  rw [polNu_apply]
  refine Commute.sum_right _ _ _ fun i _ => ?_
  refine Commute.mul_right ?_ (x_mul_e a i)
  rw [← pol_X]
  exact pol_commute _ _

section Faithful

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

include hPQ hP in
/-- The crossings commute with `Sym(ν)`. -/
theorem ψ_commute_polNu (j : ℕ) {f : Pol k ν} (hf : f ∈ symNu k ν) :
    Commute (ψ j : KLRAlgebra k Q ν) (polNu f) := by
  by_cases h : j + 1 < m
  swap
  · rw [ψ_eq_zero j (by omega)]; exact Commute.zero_left _
  apply polyRep_injective hPQ hP
  rw [map_mul, map_mul, polyRep_ψ]
  refine LinearMap.ext fun g => funext fun t => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, opΨ_apply P j h, polyRep_polNu_apply,
    polyRep_polNu_apply, opΨ_apply P j h]
  set t' := sadj m j • t
  have ht : t = sadj m j • t' := (sadj_smul_smul j t).symm
  rw [ht, hf (sadj m j) t']
  have hab : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ := by simp [Fin.ext_iff]
  unfold crossComp
  split_ifs with hl
  · have hs : sadj m j • t' = t' := by
      rw [sadj_eq h]; exact swap_smul_eq_self hl
    have hF : rename (sadj m j) (f t') = f t' := by rw [← hf (sadj m j) t', hs]
    rw [hF]
    rw [sadj_eq h] at hF
    exact ddiff_mul_of_rename_eq hab hF _
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, map_mul]
    ring

include hPQ hP in
/-- **Sym(ν) is central** (KL I, §2.4). -/
theorem polNu_mem_center {f : Pol k ν} (hf : f ∈ symNu k ν) :
    (polNu f : KLRAlgebra k Q ν) ∈ Subalgebra.center k (KLRAlgebra k Q ν) := by
  rw [Subalgebra.mem_center_iff]
  intro r
  exact (commute_of_forall_gen (fun i => e_commute_polNu f i) (fun a => x_commute_polNu a f)
    (fun j => ψ_commute_polNu hPQ hP j hf) r).eq

/-! ### Central elements lie in `Sym(ν)` -/

omit [IsDomain k] hP in
/-- The operator of any `r ∈ R(ν)` from `Pol_i` to `Pol_t` has an expansion in
`Frac(k[x]) ⋊ S_m`. -/
theorem exists_hasExp_polyRep [IsDomain k] (r : KLRAlgebra k Q ν) (i t : Seq ν) :
    ∃ G : Perm (Fin m) → FractionRing (MvPolynomial (Fin m) k),
      HasExp (fun g => polyRep hPQ r (Pi.single i g) t) G := by
  have hr : r ∈ Submodule.span k (Set.range (stdElt (k := k) (Q := Q) (fun w => canWord m w))) := by
    rw [span_stdElt _ (fun w => ⟨isReduced_canWord m w, wordProd_canWord m w⟩)]; trivial
  induction hr using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact ⟨_, (hasExp_family P (canWord m b.2.1) b.1 i t b.2.2).congr fun g => by
      rw [polyRep_stdElt]⟩
  | zero => exact ⟨0, HasExp.zero.congr fun g => by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨G, hG⟩ := hy
    obtain ⟨G', hG'⟩ := hy'
    exact ⟨_, (hG.add hG').congr fun g => by simp⟩
  | smul a y _ hy =>
    obtain ⟨G, hG⟩ := hy
    exact ⟨_, (hG.smul a).congr fun g => by simp⟩

omit hP in
/-- If `z` commutes with all dots, its operator from `Pol_i` to `Pol_t` is multiplication by
a polynomial. -/
theorem polyRep_single_eq_mul {z : KLRAlgebra k Q ν} (hx : ∀ a, Commute (x a) z)
    (i t : Seq ν) (g : MvPolynomial (Fin m) k) :
    polyRep hPQ z (Pi.single i g) t = polyRep hPQ z (Pi.single i 1) t * g := by
  obtain ⟨G, hG⟩ := exists_hasExp_polyRep hPQ z i t
  set T := fun g => polyRep hPQ z (Pi.single i g) t
  have hX : ∀ a g, T (X a * g) = X a * T g := by
    intro a g
    have h1 : opX a (Pi.single i g : Pol k ν) = Pi.single i (X a * g) := by
      funext s; rw [opX_apply]; by_cases hs : s = i
      · subst hs; simp
      · simp [hs]
    have := congrArg (fun r => polyRep hPQ r (Pi.single i g) t) (hx a).eq
    simp only [map_mul, polyRep_x, Module.End.mul_apply, h1, opX_apply] at this
    exact this.symm
  have hsupp : ∀ v, v ≠ 1 → G v = 0 := by
    intro v hv
    obtain ⟨a, ha⟩ : ∃ a, v a ≠ a := by
      by_contra hc
      push_neg at hc
      exact hv (Equiv.ext hc)
    have h1 := hG.comp_mul (X a)
    have h2 := hG.mulLeft (X a)
    have h12 := h1.unique (h2.congr fun g => hX a g)
    have := congrFun h12 v
    simp only [act_algebraMap, rename_X] at this
    have hne : algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (X (v a) - X a) ≠ 0 :=
      algebraMap_ne_zero (sub_ne_zero.2 fun h => ha (X_injective h))
    rw [map_sub] at hne
    have : G v * (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (X (v a)) - algebraMap (MvPolynomial (Fin m) k) _ (X a)) = 0 := by
      rw [mul_sub, this, mul_comm, sub_self]
    exact (mul_eq_zero.1 this).resolve_right hne
  have hval : ∀ g, algebraMap _ (FractionRing (MvPolynomial (Fin m) k)) (T g) =
      G 1 * algebraMap _ _ g := by
    intro g
    rw [hG g, Finset.sum_eq_single 1 (fun v _ hv => by rw [hsupp v hv, zero_mul])
      (by simp), act_one]
  have h1 := hval 1
  rw [map_one, mul_one] at h1
  apply IsFractionRing.injective (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
  rw [map_mul]
  exact (hval g).trans (by rw [← h1])

omit [IsDomain k] hP in
/-- If `z` commutes with all idempotents, its operator has no off-diagonal components. -/
theorem polyRep_single_eq_zero {z : KLRAlgebra k Q ν} (he : ∀ i, Commute (e i) z)
    {i t : Seq ν} (hit : t ≠ i) (g : MvPolynomial (Fin m) k) :
    polyRep hPQ z (Pi.single i g) t = 0 := by
  have h1 : opE i (Pi.single i g : Pol k ν) = Pi.single i g := by
    funext s; rw [opE_apply]; by_cases hs : s = i
    · subst hs; simp
    · simp [hs]
  have := congrArg (fun r => polyRep hPQ r (Pi.single i g) t) (he i).eq
  simp only [map_mul, polyRep_e, Module.End.mul_apply, h1, opE_apply, if_neg hit] at this
  exact this.symm

include hP in
/-- An element commuting with all idempotents and dots lies in `Pol(ν)`. -/
theorem exists_polNu_eq_of_commute {z : KLRAlgebra k Q ν} (he : ∀ i, Commute (e i) z)
    (hx : ∀ a, Commute (x a) z) :
    polNu (fun i => polyRep hPQ z (Pi.single i 1) i) = z := by
  apply polyRep_injective hPQ hP
  refine LinearMap.pi_ext fun i g => funext fun t => ?_
  rw [polyRep_polNu_apply]
  by_cases hit : t = i
  · subst hit
    rw [Pi.single_eq_same]
    exact (polyRep_single_eq_mul hPQ hx t t g).symm
  · rw [Pi.single_eq_of_ne hit, mul_zero, polyRep_single_eq_zero hPQ he hit]

include hPQ hP in
/-- If `polNu g` commutes with `ψ j`, then `g_{s_j • i} = s_j(g_i)`. -/
theorem sadj_invariant_of_commute {g : Pol k ν} (j : ℕ)
    (hψ : Commute (ψ j : KLRAlgebra k Q ν) (polNu g)) (i : Seq ν) :
    g (sadj m j • i) = rename (sadj m j) (g i) := by
  by_cases h : j + 1 < m
  swap
  · rw [sadj_of_not_lt h, one_smul, Perm.coe_one, rename_id_apply]
  have := congrArg (fun r => polyRep hPQ r (Pi.single i 1) (sadj m j • i)) hψ.eq
  simp only [map_mul, polyRep_ψ, Module.End.mul_apply] at this
  rw [opΨ_apply P j h, polyRep_polNu_apply, polyRep_polNu_apply, opΨ_apply P j h,
    sadj_smul_smul, Pi.single_eq_same, mul_one] at this
  have hab : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ := by simp [Fin.ext_iff]
  unfold crossComp at this
  split_ifs at this with hl
  · have hs : sadj m j • i = i := by
      rw [sadj_eq h]; exact swap_smul_eq_self hl
    have h0 : ddiff (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩ (1 : MvPolynomial (Fin m) k) = 0 := by
      simpa using ddiff_C hab (1 : k)
    rw [h0, mul_zero] at this
    have hspec := ddiff_spec hab (g i)
    rw [this, mul_zero, eq_comm, sub_eq_zero] at hspec
    rw [hs, sadj_eq h, ← hspec]
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, map_one, mul_one] at this
    have hinj : Function.Injective ![(⟨j, by omega⟩ : Fin m), ⟨j + 1, h⟩] := by
      intro a b hab'
      fin_cases a <;> fin_cases b <;> simp_all
    have hPne : rename ![(⟨j, by omega⟩ : Fin m), ⟨j + 1, h⟩]
        (P (i.lbl ⟨j, by omega⟩) (i.lbl ⟨j + 1, h⟩)) ≠ 0 := fun e =>
      hP _ _ hl (rename_injective _ hinj (by rw [e, map_zero]))
    rw [mul_comm (g _)] at this
    exact (mul_left_cancel₀ hPne this).symm

include hPQ hP in
/-- **KL I, Theorem 2.9**: an element of `R(ν)` is central iff it is `polNu f` for some
`f ∈ Sym(ν)`. -/
theorem mem_center_iff {z : KLRAlgebra k Q ν} :
    z ∈ Subalgebra.center k (KLRAlgebra k Q ν) ↔ ∃ f ∈ symNu k ν, polNu f = z := by
  constructor
  · intro hz
    rw [Subalgebra.mem_center_iff] at hz
    have hc : ∀ r, Commute r z := fun r => hz r
    refine ⟨_, ?_, exists_polNu_eq_of_commute hPQ hP (fun i => hc _) (fun a => hc _)⟩
    refine mem_symNu_of_sadj fun j i =>
      sadj_invariant_of_commute (g := fun i => polyRep hPQ z (Pi.single i 1) i) hPQ hP j ?_ i
    rw [exists_polNu_eq_of_commute hPQ hP (fun i => hc _) (fun a => hc _)]
    exact hc _
  · rintro ⟨f, hf, rfl⟩
    exact polNu_mem_center hPQ hP hf

include hPQ hP in
/-- **KL I, Theorem 2.9**: the center of `R(ν)` is `Sym(ν)`. -/
theorem center_eq :
    Subalgebra.center k (KLRAlgebra k Q ν) = (symNu k ν).map polNu := by
  ext z
  rw [mem_center_iff hPQ hP, Subalgebra.mem_map]

/-- **KL I, Theorem 2.9**: `Sym(ν) ≅ Z(R(ν))` via `polNu`. -/
noncomputable def symNuEquivCenter :
    symNu k ν ≃ₐ[k] Subalgebra.center k (KLRAlgebra k Q ν) :=
  (Subalgebra.equivMapOfInjective (symNu k ν) polNu (polNu_injective hPQ)).trans
    (Subalgebra.equivOfEq _ _ (center_eq hPQ hP).symm)

@[simp] theorem symNuEquivCenter_apply (f : symNu k ν) :
    (symNuEquivCenter hPQ hP f : KLRAlgebra k Q ν) = polNu (f : Pol k ν) := rfl

include hPQ hP in
/-- **KL I, Corollary 2.11 (2)**: `R(ν)` is indecomposable: its only central idempotents
are `0` and `1`. -/
theorem eq_zero_or_one_of_mem_center {z : KLRAlgebra k Q ν}
    (hz : z ∈ Subalgebra.center k (KLRAlgebra k Q ν)) (hzz : IsIdempotentElem z) :
    z = 0 ∨ z = 1 := by
  obtain ⟨f, hf, rfl⟩ := (mem_center_iff hPQ hP).1 hz
  have hff : f * f = f := polNu_injective hPQ (by rw [map_mul]; exact hzz)
  have hi : ∀ i, f i = 0 ∨ f i = 1 := fun i =>
    IsIdempotentElem.iff_eq_zero_or_one.1 (congrFun hff i)
  by_cases h0 : ∃ i, f i = 0
  · obtain ⟨i, hi0⟩ := h0
    left
    have : f = 0 := funext fun j => by
      obtain ⟨w, rfl⟩ := Seq.exists_smul_eq i j
      rw [hf w i, hi0, map_zero, Pi.zero_apply]
    rw [this, map_zero]
  · push_neg at h0
    right
    have : f = 1 := funext fun j => (hi j).resolve_left (h0 j)
    rw [this, map_one]

end Faithful

end KLRAlgebra

/-! ### The rings of KL I -/

namespace KL1

open KLRAlgebra

variable [DecidableEq I] {Γ : SimpleGraph I} [DecidableRel Γ.Adj] [IsDomain k]

/-- **KL I, Theorem 2.9** for the rings `R(ν)` of KL I (over `ℤ`, or any integral domain):
the center of `R(ν)` is `Sym(ν)`. -/
theorem center_eq :
    Subalgebra.center k (R1 k Γ ν) = (symNu k ν).map polNu :=
  KLRAlgebra.center_eq (klQ_eq_klP (Γ := Γ) stdOrient_spec) (fun a b _ => klP_ne_zero _ a b)

/-- **KL I, Theorem 2.9**, elementwise. -/
theorem mem_center_iff {z : R1 k Γ ν} :
    z ∈ Subalgebra.center k (R1 k Γ ν) ↔ ∃ f ∈ symNu k ν, polNu f = z :=
  KLRAlgebra.mem_center_iff (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b)

/-- **KL I, Theorem 2.9**: `Sym(ν) ≅ Z(R(ν))`. -/
noncomputable def symNuEquivCenter : symNu k ν ≃ₐ[k] Subalgebra.center k (R1 k Γ ν) :=
  KLRAlgebra.symNuEquivCenter (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b)

/-- **KL I, Corollary 2.11 (2)**: `R(ν)` is indecomposable. -/
theorem eq_zero_or_one_of_mem_center {z : R1 k Γ ν}
    (hz : z ∈ Subalgebra.center k (R1 k Γ ν)) (hzz : IsIdempotentElem z) : z = 0 ∨ z = 1 :=
  KLRAlgebra.eq_zero_or_one_of_mem_center (klQ_eq_klP (Γ := Γ) stdOrient_spec)
    (fun a b _ => klP_ne_zero _ a b) hz hzz

end KL1

end Categorification.KLR
