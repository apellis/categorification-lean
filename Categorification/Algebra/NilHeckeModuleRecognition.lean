/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.CoinvariantPartialSocle
import Categorification.KLR.NilHeckeFullSplitting

/-!
# Recognizing the coinvariant module of `NH_N`

Let `k` be a field and `R` a finite-dimensional representation of the nilHecke ring
`NH_N = nilHecke k N` on which the multiplications by the variables `x_a` act nilpotently. Since
`1 ∈ NH_N` splits through `N!` copies of the idempotent `e_N = x^δ ∂_{w_0}`
(`NilHecke.exists_isSplitting_one_idemNH`), `dim R = N! · dim e_N R`
(`NilHecke.finrank_eq_factorial_mul_finrank_range`). If `dim R = N!`, then `R` is isomorphic to
the coinvariant module `L_N = k[x_0, …, x_{N-1}] / (Sym⁺)` (`NilHecke.nonempty_coinv_equiv`):
for a generator `v_0` of the line `e_N R`, `p ↦ p ∂_{w_0} v_0` kills `Sym⁺` (a symmetric
polynomial `s` without constant term commutes with `e_N`, so it acts on the line `e_N R` by a
nilpotent scalar), intertwines the actions of `NH_N`, and is injective since `L_N` is simple.

Together with `NilHecke.mem_coinvSocle_of_idemNHAt`, this gives the statement about `NH_N`
used in Chuang–Rouquier, arXiv:math/0407205v2, proof of Proposition 5.20 (b): in such an `R`,
the vectors fixed by the idempotent `e_i` of `NH_i ⊆ NH_N` and killed by the `x_a`, `a ≥ i`, form
a line (`NilHecke.exists_forall_mem_span_of_idemNHAt`).

## Main results

* `NilHecke.finrank_eq_card_mul_finrank_range_of_isSplitting`: if `1 ∈ End R` splits through
  copies of `E`, then `dim R = (number of copies) · dim E R`.
* `NilHecke.nonempty_coinv_equiv`: a representation of `NH_N` of dimension `N!` on which the
  `x_a` are nilpotent is isomorphic to `L_N`.
* `NilHecke.exists_forall_mem_span_of_idemNHAt`: the partial socle in such a representation is a
  line.
-/

namespace Categorification.NilHecke

open MvPolynomial Module

variable {k : Type*} [Field k] {N : ℕ}

/-! ### Dimension count from a splitting -/

theorem finrank_eq_card_mul_finrank_range_of_isSplitting {R : Type*} [AddCommGroup R]
    [Module k R] [FiniteDimensional k R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Module.End k R} {a b : ι → Module.End k R}
    (h : Graded.IsSplitting 1 (fun _ => E) a b) :
    finrank k R = Fintype.card ι * finrank k (LinearMap.range E) := by
  have hEb : ∀ j, E * b j = b j := fun j => by
    conv_rhs => rw [← mul_one (b j), ← h.sum_eq, Finset.mul_sum]
    simp_rw [← mul_assoc, h.mul_eq, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
  have hfix : ∀ (j : ι) (u : R), u ∈ LinearMap.range E → E u = u := by
    rintro j _ ⟨w, rfl⟩
    have hEE : E * E = E :=
      calc E * E = E * (b j * a j) := by rw [h.mul_self j]
        _ = E := by rw [← mul_assoc, hEb, h.mul_self j]
    rw [← Module.End.mul_apply, hEE]
  let F : R →ₗ[k] (ι → LinearMap.range E) :=
    LinearMap.pi fun j => (b j).codRestrict (LinearMap.range E) fun v =>
      LinearMap.mem_range.2 ⟨b j v, by rw [← Module.End.mul_apply, hEb]⟩
  let G : (ι → LinearMap.range E) →ₗ[k] R :=
    { toFun := fun u => ∑ j, a j (u j)
      map_add' := fun u u' => by simp [Finset.sum_add_distrib]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Pi.smul_apply, Submodule.coe_smul, map_smul] }
  have hGF : G.comp F = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    change ∑ j, a j (b j v) = v
    have hs := congrArg (fun T : Module.End k R => T v) h.sum_eq
    simp only [LinearMap.sum_apply, Module.End.mul_apply, Module.End.one_apply] at hs
    exact hs
  have hFG : F.comp G = LinearMap.id := by
    refine LinearMap.ext fun u => funext fun i => Subtype.ext ?_
    change b i (∑ j, a j (u j)) = u i
    rw [map_sum, Finset.sum_eq_single i (fun j _ hj => by
      rw [← Module.End.mul_apply, h.mul_ne (Ne.symm hj), LinearMap.zero_apply])
      (fun hi => absurd (Finset.mem_univ i) hi), ← Module.End.mul_apply, h.mul_self]
    exact hfix i _ (u i).2
  let e : R ≃ₗ[k] (ι → LinearMap.range E) :=
    LinearEquiv.ofLinearMap (f := F) (g := G) hFG hGF
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]

variable {R : Type*} [AddCommGroup R] [Module k R] [FiniteDimensional k R]

/-- The idempotent `e_N = x^δ ∂_{w_0}` as an element of `NH_N`. -/
private noncomputable abbrev eN (k : Type*) [Field k] (N : ℕ) : nilHecke k N :=
  ⟨idemNH k N, idemNH_mem⟩

/-- **`dim R = N! · dim e_N R`** for every finite-dimensional representation of `NH_N`. -/
theorem finrank_eq_factorial_mul_finrank_range (ρ : nilHecke k N →ₐ[k] Module.End k R) :
    finrank k R = N.factorial * finrank k (LinearMap.range (ρ (eN k N))) := by
  obtain ⟨ι, _, _, a, b, hc, hS⟩ := exists_isSplitting_one_idemNH k N
  have h := hS.map ρ
  rw [map_one] at h
  rw [finrank_eq_card_mul_finrank_range_of_isSplitting h, hc]

/-! ### The comparison map -/

/-- Multiplication by polynomials, as an algebra map into `NH_N`. -/
private noncomputable def mulPolyNH (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (Fin N) k →ₐ[k] nilHecke k N :=
  (mulPoly k N).codRestrict (nilHecke k N) mulPoly_mem

@[simp] private theorem coe_mulPolyNH (p : MvPolynomial (Fin N) k) :
    (mulPolyNH k N p : Module.End k (MvPolynomial (Fin N) k)) = mulPoly k N p := rfl

/-- `∂_j p = q ∂_j + (∂_j p)` as operators, for some polynomial `q` (namely `s_j p`). -/
private theorem dd_mul_mulPoly (j : ℕ) (p : MvPolynomial (Fin N) k) :
    ∃ q, dd k N j * mulPoly k N p = mulPoly k N q * dd k N j + mulPoly k N (dd k N j p) := by
  by_cases h : j + 1 < N
  · refine ⟨rename (Equiv.swap (⟨j, by omega⟩ : Fin N) ⟨j + 1, h⟩) p, ?_⟩
    refine LinearMap.ext fun f => ?_
    simp only [dd_of_lt h, LinearMap.add_apply, Module.End.mul_apply, mulPoly_apply]
    rw [ddiff_mul (by simp [Fin.ext_iff])]
    ring
  · refine ⟨0, ?_⟩
    simp [dd_eq_zero (by omega : N ≤ j + 1)]

section Comparison

variable (ρ : nilHecke k N →ₐ[k] Module.End k R) (v₀ : R)

/-- `p ↦ p ∂_{w_0} v₀`. -/
private noncomputable def cmp : MvPolynomial (Fin N) k →ₗ[k] R :=
  (LinearMap.applyₗ (ρ ⟨ddw (w0Word N), ddw_mem _⟩ v₀)).comp
    (ρ.comp (mulPolyNH k N)).toLinearMap

omit [FiniteDimensional k R] in
private theorem cmp_apply (p : MvPolynomial (Fin N) k) :
    cmp ρ v₀ p = ρ (mulPolyNH k N p) (ρ ⟨ddw (w0Word N), ddw_mem _⟩ v₀) := rfl

omit [FiniteDimensional k R] in
private theorem cmp_mul (p q : MvPolynomial (Fin N) k) :
    cmp ρ v₀ (p * q) = ρ (mulPolyNH k N p) (cmp ρ v₀ q) := by
  rw [cmp_apply, cmp_apply, map_mul, map_mul, Module.End.mul_apply]

omit [FiniteDimensional k R] in
/-- `p ↦ p ∂_{w_0} v₀` intertwines the actions of `NH_N`. -/
private theorem cmp_nilHecke {T : Module.End k (MvPolynomial (Fin N) k)} (hT : T ∈ nilHecke k N)
    (p : MvPolynomial (Fin N) k) : cmp ρ v₀ (T p) = ρ ⟨T, hT⟩ (cmp ρ v₀ p) := by
  induction hT using Algebra.adjoin_induction generalizing p with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨j, rfl⟩
    · exact cmp_mul ρ v₀ (X a) p
    · obtain ⟨q, hq⟩ := dd_mul_mulPoly (k := k) j p
      have hq' : (⟨dd k N j, dd_mem j⟩ : nilHecke k N) * mulPolyNH k N p =
          mulPolyNH k N q * ⟨dd k N j, dd_mem j⟩ + mulPolyNH k N (dd k N j p) :=
        Subtype.ext hq
      have h0 : ρ ⟨dd k N j, dd_mem j⟩ (ρ ⟨ddw (w0Word N), ddw_mem _⟩ v₀) = 0 := by
        rw [← Module.End.mul_apply, ← map_mul]
        have : (⟨dd k N j, dd_mem j⟩ : nilHecke k N) * ⟨ddw (w0Word N), ddw_mem _⟩ = 0 :=
          Subtype.ext (dd_mul_ddw_w0Word j)
        rw [this, map_zero, LinearMap.zero_apply]
      rw [cmp_apply, cmp_apply]
      symm
      rw [← Module.End.mul_apply, ← map_mul, hq', map_add, map_mul, LinearMap.add_apply,
        Module.End.mul_apply, h0, map_zero, zero_add]
  | algebraMap r =>
    rw [Module.algebraMap_end_apply, map_smul]
    have : (⟨algebraMap k _ r, Subalgebra.algebraMap_mem _ r⟩ : nilHecke k N) =
        algebraMap k (nilHecke k N) r := rfl
    rw [this, AlgHom.commutes, Module.algebraMap_end_apply]
  | add x y hx hy ihx ihy =>
    rw [LinearMap.add_apply, map_add, ihx, ihy]
    have : (⟨x + y, add_mem hx hy⟩ : nilHecke k N) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add, LinearMap.add_apply]
  | mul x y hx hy ihx ihy =>
    rw [Module.End.mul_apply, ihx, ihy]
    have : (⟨x * y, mul_mem hx hy⟩ : nilHecke k N) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul, Module.End.mul_apply]

variable {ρ}

omit [FiniteDimensional k R] in
/-- If the `x_a` act nilpotently, so does every polynomial without constant term. -/
private theorem isNilpotent_mulPolyNH
    (hnil : ∀ a : Fin N, IsNilpotent (ρ ⟨mulX k N a, mulX_mem a⟩))
    {s : MvPolynomial (Fin N) k} (hs : constantCoeff s = 0) :
    IsNilpotent (ρ (mulPolyNH k N s)) := by
  have hmem : s ∈ Ideal.span (X '' Set.univ : Set (MvPolynomial (Fin N) k)) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hm0 : m = 0 := Finsupp.ext fun i => hcon i (Set.mem_univ i)
    rw [hm0, MvPolynomial.mem_support_iff, ← constantCoeff_eq, hs] at hm
    exact hm rfl
  have hcomm : ∀ p q : MvPolynomial (Fin N) k,
      Commute (ρ (mulPolyNH k N p)) (ρ (mulPolyNH k N q)) := fun p q => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm]
  clear hs
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    exact hnil a
  | zero => rw [map_zero, map_zero]; exact IsNilpotent.zero
  | add x y _ _ hx hy =>
    rw [map_add, map_add]; exact (hcomm x y).isNilpotent_add hx hy
  | smul c y _ hy =>
    rw [smul_eq_mul, map_mul, map_mul]; exact (hcomm c y).isNilpotent_mul_left hy

variable (hR : finrank k R = N.factorial)
  (hnil : ∀ a : Fin N, IsNilpotent (ρ ⟨mulX k N a, mulX_mem a⟩))

include hR in
private theorem finrank_range_eN : finrank k (LinearMap.range (ρ (eN k N))) = 1 := by
  have h := finrank_eq_factorial_mul_finrank_range (k := k) ρ
  rw [hR] at h
  have hpos := N.factorial_pos
  nlinarith [h]

private theorem eN_mul_mulPolyNH {s : MvPolynomial (Fin N) k} (hs : s.IsSymmetric) :
    eN k N * mulPolyNH k N s = mulPolyNH k N s * eN k N := by
  refine Subtype.ext (LinearMap.ext fun f => ?_)
  show idemNH k N (s * f) = s * idemNH k N f
  simp only [idemNH, Module.End.mul_apply, mulPoly_apply]
  rw [ddw_mul_of_forall (fun j _ h => hs _) f]
  ring

private theorem ddw_mul_mulPolyNH {s : MvPolynomial (Fin N) k} (hs : s.IsSymmetric) :
    (⟨ddw (w0Word N), ddw_mem _⟩ : nilHecke k N) * mulPolyNH k N s =
      mulPolyNH k N s * ⟨ddw (w0Word N), ddw_mem _⟩ := by
  refine Subtype.ext (LinearMap.ext fun f => ?_)
  show ddw (w0Word N) (s * f) = s * ddw (w0Word N) f
  exact ddw_mul_of_forall (fun j _ h => hs _) f

include hR hnil in
/-- `p ↦ p ∂_{w_0} v₀` kills `Sym⁺` for `v₀ ∈ e_N R`. -/
private theorem cmp_eq_zero_of_mem {v₀ : R} (hv₀ : v₀ ∈ LinearMap.range (ρ (eN k N)))
    {p : MvPolynomial (Fin N) k} (hp : p ∈ coinvIdeal k N) : cmp ρ v₀ p = 0 := by
  have hev : ρ (eN k N) v₀ = v₀ := by
    obtain ⟨u, rfl⟩ := hv₀
    have hee : eN k N * eN k N = eN k N :=
      Subtype.ext (isIdempotentElem_idemNH (k := k) (m := N)).eq
    rw [← Module.End.mul_apply, ← map_mul, hee]
  induction hp using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨hsym, hs0⟩ := hs
    -- `s` acts on the line `e_N R` by a nilpotent scalar
    have hline : ρ (mulPolyNH k N s) v₀ ∈ LinearMap.range (ρ (eN k N)) :=
      ⟨ρ (mulPolyNH k N s) v₀, by
        rw [← Module.End.mul_apply, ← map_mul, eN_mul_mulPolyNH hsym, map_mul,
          Module.End.mul_apply, hev]⟩
    have hsv : ρ (mulPolyNH k N s) v₀ = 0 := by
      by_cases hv0 : v₀ = 0
      · rw [hv0, map_zero]
      have hspan : LinearMap.range (ρ (eN k N)) = k ∙ v₀ := by
        symm
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hv₀
        · rw [finrank_span_singleton hv0, finrank_range_eN hR]
      rw [hspan, Submodule.mem_span_singleton] at hline
      obtain ⟨c, hc⟩ := hline
      obtain ⟨n, hn⟩ := isNilpotent_mulPolyNH hnil hs0
      have hpow : ∀ m : ℕ, (ρ (mulPolyNH k N s) ^ m) v₀ = c ^ m • v₀ := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, ← hc, smul_smul,
            pow_succ]
      have := hpow n
      rw [hn, LinearMap.zero_apply] at this
      have hc0 : c ^ n = 0 := by
        by_contra hne
        exact hv0 ((smul_eq_zero.1 this.symm).resolve_left hne)
      have hn0 : n ≠ 0 := by rintro rfl; simp at hc0
      rw [← hc, (pow_eq_zero_iff hn0).1 hc0, zero_smul]
    rw [cmp_apply, ← Module.End.mul_apply, ← map_mul, ← ddw_mul_mulPolyNH hsym, map_mul,
      Module.End.mul_apply, hsv, map_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c y _ hy => rw [smul_eq_mul, cmp_mul, hy, map_zero]

end Comparison

/-- **A representation of `NH_N` of dimension `N!` on which the `x_a` act nilpotently is
isomorphic to the coinvariant module `L_N`**, as a representation of `NH_N`. -/
theorem nonempty_coinv_equiv (ρ : nilHecke k N →ₐ[k] Module.End k R)
    (hR : finrank k R = N.factorial)
    (hnil : ∀ a : Fin N, IsNilpotent (ρ ⟨mulX k N a, mulX_mem a⟩)) :
    ∃ ψ : Coinv k N ≃ₗ[k] R, ∀ (T : nilHecke k N) (v : Coinv k N),
      ψ (nhAct k N T v) = ρ T (ψ v) := by
  -- a nonzero vector of the line `e_N R`
  have h1 := finrank_range_eN hR (ρ := ρ)
  obtain ⟨v₀, hv₀, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := LinearMap.range
    (ρ (eN k N))) (fun h => by rw [h, finrank_bot] at h1; exact zero_ne_one h1)
  have hev : ρ (eN k N) v₀ = v₀ := by
    obtain ⟨u, rfl⟩ := hv₀
    rw [← Module.End.mul_apply, ← map_mul]
    congr 2
    exact Subtype.ext (isIdempotentElem_idemNH (k := k) (m := N)).eq
  let ψ : Coinv k N →ₗ[k] R :=
    (coinvSub k N).liftQ (cmp ρ v₀) fun p hp => cmp_eq_zero_of_mem hR hnil hv₀ hp
  have hψ : ∀ (T : nilHecke k N) (v : Coinv k N), ψ (nhAct k N T v) = ρ T (ψ v) := by
    intro T v
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact cmp_nilHecke ρ v₀ T.2 p
  have htop : ψ (Submodule.Quotient.mk (xDelta N)) = v₀ := by
    show cmp ρ v₀ (xDelta N) = v₀
    rw [cmp_apply, ← Module.End.mul_apply, ← map_mul]
    exact hev
  -- the kernel is an `NH_N`-submodule of the simple module `L_N`
  let K : Submodule (nilHecke k N) (NHRep k N) :=
    { carrier := {v | ψ ((NHRep.of k N).symm v) = 0}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢; rw [hx, hy, add_zero]
      zero_mem' := by simp
      smul_mem' := fun T v hv => by
        simp only [Set.mem_ofPred_eq] at hv ⊢
        change ψ (nhAct k N T ((NHRep.of k N).symm v)) = 0
        rw [hψ, hv, map_zero] }
  have hinj : Function.Injective ψ := by
    rcases (isSimpleModule_coinv (k := k) (m := N)).eq_bot_or_eq_top K with hK | hK
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro v hv
      have : NHRep.of k N v ∈ K := hv
      rw [hK] at this
      exact this
    · exfalso
      have : NHRep.of k N (Submodule.Quotient.mk (xDelta N)) ∈ K := by rw [hK]; trivial
      exact hv0 (htop ▸ this)
  have hbij : Function.Bijective ψ := by
    refine ⟨hinj, ?_⟩
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    rw [finrank_coinv, hR]
  exact ⟨LinearEquiv.ofBijective ψ hbij, hψ⟩

/-- In a representation of `NH_N` of dimension `N!` on which the `x_a` act nilpotently, the
vectors fixed by the idempotent `e_i` of `NH_i ⊆ NH_N` and killed by the `x_a`, `a ≥ i`, lie on a
line (Chuang–Rouquier, arXiv:math/0407205v2, proof of Proposition 5.20 (b)). -/
theorem exists_forall_mem_span_of_idemNHAt (ρ : nilHecke k N →ₐ[k] Module.End k R)
    (hR : finrank k R = N.factorial)
    (hnil : ∀ a : Fin N, IsNilpotent (ρ ⟨mulX k N a, mulX_mem a⟩)) {i : ℕ} (hi : i ≤ N) :
    ∃ u₀ : R, ∀ u : R, ρ (idemNHAt k N i) u = u →
      (∀ b : Fin N, i ≤ b → ρ ⟨mulX k N b, mulX_mem b⟩ u = 0) → u ∈ k ∙ u₀ := by
  obtain ⟨ψ, hψ⟩ := nonempty_coinv_equiv ρ hR hnil
  refine ⟨ψ (Submodule.Quotient.mk (xDelta N)), fun u hu hout => ?_⟩
  obtain ⟨v, rfl⟩ := ψ.surjective u
  have hv : nhAct k N (idemNHAt k N i) v = v := by
    apply ψ.injective; rw [hψ, hu]
  have hvout : ∀ b : Fin N, i ≤ b → coinvMul k (X b) v = 0 := fun b hb => by
    apply ψ.injective
    rw [← nhAct_mulX, hψ, hout b hb, map_zero]
  have hmem := mem_coinvSocle_of_idemNHAt hi hv hvout
  rw [coinvSocle_eq_span_xDelta, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, rfl⟩ := hmem
  rw [map_smul]
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)

end Categorification.NilHecke
