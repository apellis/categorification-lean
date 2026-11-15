/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Algebra

/-!
# The polynomial representation of the gallery algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.1,
Proposition `prop:action`.

The gallery algebra `GalleryAlgebra k Γ ν` acts on `V = (FullChamber Γ ν → k[y_s])`, one copy of
the polynomial ring for each full chamber: `e C` is the projection to the copy of `C`, a
polynomial acts by multiplication on every copy, a relabelling `r g C` renames the variables by
`g` from the copy of `C` to that of `g • C`, and a step `t C C'` across the hyperplane `h` maps
the copy of `C` to that of `C'` by

* `wallOp`: multiplication by `Q_e(y_a, y_b)` when crossing the wall `w = (e, a, b)` from the
  side where `b` is left of the ghost of `a`, and the identity in the other direction;
* `psiOp`: the divided difference `∂_{l r}`, or `P_i(y_l, y_r)(1 - s_{l r})` when there is a loop
  at the colour `i`, when crossing a diagonal with the strand `l` on the left.

This file proves that these operators satisfy the defining relations of the gallery algebra.
The relations of three strands of one colour are the labelled nilHecke braid relation
(`ddiff_braid_labelled`) and its loop correction (`psi_braid_loop`, Webster's relation (4c)).

## Main results

* `ddiff_braid_labelled`: `∂_{v w} ∂_{u w} ∂_{u v} = ∂_{u v} ∂_{u w} ∂_{v w}`.
* `psiOp_leibniz`: `ψ (f g) - f ψ g = Δ(f) s(g)`, Webster's relations (1).
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-! ### Polynomial identities -/

section Poly

omit [DecidableEq I] in
theorem loopFactor_rename (P : MvPolynomial (Fin 2) k) (φ : Strand ν → Strand ν)
    (s s' : Strand ν) : rename φ (loopFactor P s s') = loopFactor P (φ s) (φ s') := by
  rw [loopFactor, ← AlgHom.comp_apply, comp_aeval, loopFactor]
  congr 2
  funext j
  fin_cases j <;> simp

omit [DecidableEq I] in
theorem loopFactor_comm {P : MvPolynomial (Fin 2) k} (hP : rename (swap (0 : Fin 2) 1) P = P)
    (s s' : Strand ν) : loopFactor P s s' = loopFactor P s' s := by
  conv_lhs => rw [loopFactor, ← hP, aeval_rename]
  rw [loopFactor]
  congr 2
  funext j
  fin_cases j <;> simp [swap_apply_left, swap_apply_right]

/-- Renaming the variables by a colour-preserving permutation conjugates `ψ`. -/
theorem psiOp_rename (φ : Perm (Strand ν)) (hφ : ∀ s, (φ s).1 = s.1) {s s' : Strand ν}
    (hss' : s ≠ s') (f : PolyRing ν k) :
    rename φ (psiOp Γ s s' f) = psiOp Γ (φ s) (φ s') (rename φ f) := by
  rcases h : Γ.loop s.1 with _ | P
  · have h' : Γ.loop (φ s).1 = none := by rw [hφ]; exact h
    rw [psiOp_of_none h, psiOp_of_none h', rename_ddiff φ.injective hss']
  · have h' : Γ.loop (φ s).1 = some P := by rw [hφ]; exact h
    rw [psiOp_of_some h, psiOp_of_some h', map_mul, map_sub, loopFactor_rename, rename_rename,
      rename_rename, φ.injective.swap_comp]

/-- `ψ` is linear over polynomials symmetric in its two strands. -/
theorem psiOp_mul_of_rename_eq {s s' : Strand ν} (hss' : s ≠ s') {c : PolyRing ν k}
    (hc : rename (swap s s') c = c) (f : PolyRing ν k) :
    psiOp Γ s s' (c * f) = c * psiOp Γ s s' f := by
  rcases h : Γ.loop s.1 with _ | P
  · rw [psiOp_of_none h, ddiff_mul_of_rename_eq hss' hc]
  · rw [psiOp_of_some h, psiOp_of_some h, map_mul, hc]
    ring

/-- Webster's relations (1), labelled form: `ψ (f g) - f ψ g = Δ_{s s'}(f) s_{s s'}(g)`. -/
theorem psiOp_leibniz {s s' : Strand ν} (hss' : s ≠ s') (f g : PolyRing ν k) :
    psiOp Γ s s' (f * g) - f * psiOp Γ s s' g =
      stepFactor Γ s s' f * rename (swap s s') g := by
  rcases h : Γ.loop s.1 with _ | P
  · simp only [psiOp_of_none h, stepFactor, h]
    have e1 := ddiff_spec (k := k) hss' f
    have e2 := ddiff_spec (k := k) hss' g
    rw [ddiff_mul hss']
    linear_combination (ddiff s s' g) * e1 - (ddiff s s' f) * e2
  · simp only [psiOp_of_some h, stepFactor, h, map_mul]
    ring

theorem stepFactor_rename_swap {s s' : Strand ν} (hss' : s ≠ s') (f : PolyRing ν k) :
    stepFactor Γ s s' (rename (swap s s') f) = -stepFactor Γ s s' f := by
  rcases h : Γ.loop s.1 with _ | P
  · simp only [stepFactor, h, ddiff_rename_swap hss']
  · simp only [stepFactor, h, rename_swap_rename_swap]
    ring

/-- `ψ` with the two strands exchanged, without a loop. -/
theorem psiOp_swap_of_none {s s' : Strand ν} (hss' : s ≠ s') (h : Γ.loop s.1 = none)
    (h' : Γ.loop s'.1 = none) (f : PolyRing ν k) :
    psiOp Γ s' s f = -psiOp Γ s s' f := by
  rw [psiOp_of_none h, psiOp_of_none h', ddiff_comm hss']

/-- `ψ` with the two strands exchanged, with a symmetric loop polynomial. -/
theorem psiOp_swap_of_some {s s' : Strand ν} {P : MvPolynomial (Fin 2) k}
    (hP : rename (swap (0 : Fin 2) 1) P = P) (h : Γ.loop s.1 = some P)
    (h' : Γ.loop s'.1 = some P) (f : PolyRing ν k) :
    psiOp Γ s' s f = psiOp Γ s s' f := by
  rw [psiOp_of_some h, psiOp_of_some h', loopFactor_comm hP, swap_comm]

/-- The strand bigon, read with the strands exchanged after the first crossing. -/
theorem psiOp_psiOp_swap (hΓ : Γ.PSymm) {s s' : Strand ν} (hss' : s ≠ s') (hc : s.1 = s'.1)
    (f : PolyRing ν k) :
    psiOp Γ s' s (psiOp Γ s s' f) =
      match Γ.loop s.1 with
      | none => 0
      | some P => -2 * loopFactor P s s' * rename (swap s s') (psiOp Γ s s' f) := by
  rcases h : Γ.loop s.1 with _ | P
  · have h' : Γ.loop s'.1 = none := by rw [← hc]; exact h
    rw [psiOp_swap_of_none hss' h h', psiOp_of_none h, ddiff_ddiff hss', neg_zero]
  · have h' : Γ.loop s'.1 = some P := by rw [← hc]; exact h
    have hP := hΓ _ P h
    rw [psiOp_swap_of_some hP h h']
    simp only [psiOp_of_some h, map_mul, map_sub, rename_swap_rename_swap,
      rename_swap_loopFactor hP]
    ring

/-- `ψ`s on disjoint pairs of strands commute. -/
theorem psiOp_psiOp_comm {a b c d : Strand ν} (hab : a ≠ b) (hcd : c ≠ d) (hab' : a.1 = b.1)
    (hcd' : c.1 = d.1) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (f : PolyRing ν k) :
    psiOp Γ a b (psiOp Γ c d f) = psiOp Γ c d (psiOp Γ a b f) := by
  -- `ψ_{c d}` commutes with `s_{a b}`, and with multiplication by `P(y_a, y_b)`
  have hcol : ∀ {x y : Strand ν}, x.1 = y.1 → ∀ s, ((swap x y) s).1 = s.1 := by
    intro x y hxy s
    rcases eq_or_ne s x with rfl | h1
    · rw [swap_apply_left]; exact hxy.symm
    rcases eq_or_ne s y with rfl | h2
    · rw [swap_apply_right]; exact hxy
    · rw [swap_apply_of_ne_of_ne h1 h2]
  have r1 : ∀ g, rename (swap a b) (psiOp Γ c d g) = psiOp Γ c d (rename (swap a b) g) := by
    intro g
    rw [psiOp_rename _ (hcol hab') hcd, swap_apply_of_ne_of_ne hac.symm hbc.symm,
      swap_apply_of_ne_of_ne had.symm hbd.symm]
  have r2 : ∀ g, rename (swap c d) (psiOp Γ a b g) = psiOp Γ a b (rename (swap c d) g) := by
    intro g
    rw [psiOp_rename _ (hcol hcd') hab, swap_apply_of_ne_of_ne hac had,
      swap_apply_of_ne_of_ne hbc hbd]
  rcases h1 : Γ.loop a.1 with _ | P
  · rcases h2 : Γ.loop c.1 with _ | Q
    · rw [psiOp_of_none h1, psiOp_of_none h2, ddiff_ddiff_comm hab hcd hac had hbc hbd]
    · have hQ : rename (swap a b) (loopFactor Q c d) = loopFactor Q c d := by
        rw [loopFactor_rename, swap_apply_of_ne_of_ne hac.symm hbc.symm,
          swap_apply_of_ne_of_ne had.symm hbd.symm]
      rw [psiOp_of_some h2, psiOp_of_some h2, psiOp_mul_of_rename_eq hab hQ, map_sub,
        ← r2]
  · have hP : rename (swap c d) (loopFactor P a b) = loopFactor P a b := by
      rw [loopFactor_rename, swap_apply_of_ne_of_ne hac had, swap_apply_of_ne_of_ne hbc hbd]
    rw [psiOp_of_some h1, psiOp_of_some h1, psiOp_mul_of_rename_eq hcd hP, map_sub, ← r1]

end Poly

/-! ### The braid relations of three strands of one colour -/

section Braid

variable {σ : Type*} [DecidableEq σ] {u v w : σ}

/-- Composition rules for the transpositions of three distinct elements, used to put
products of renamings in the normal form `1, s_{uv}, s_{uw}, s_{vw}, s_{uw} s_{uv},
s_{vw} s_{uv}`. -/
theorem swap_comp_swap_of_three (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (⇑(swap u v) ∘ ⇑(swap u w) = ⇑(swap v w) ∘ ⇑(swap u v)) ∧
    (⇑(swap u v) ∘ ⇑(swap v w) = ⇑(swap u w) ∘ ⇑(swap u v)) ∧
    (⇑(swap u w) ∘ ⇑(swap v w) = ⇑(swap v w) ∘ ⇑(swap u v)) ∧
    (⇑(swap v w) ∘ ⇑(swap u w) = ⇑(swap u w) ∘ ⇑(swap u v)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext x <;> simp only [Function.comp_apply, swap_apply_def] <;>
    split_ifs <;> simp_all

/-- `Δ · ∂_{vw} ∂_{uw} ∂_{uv} f` is the alternating sum of the `S₃`-translates of `f`,
where `Δ = (X u - X v)(X u - X w)(X v - X w)`. -/
theorem ddiff_braid_labelled_aux (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (f : MvPolynomial σ k) :
    (X u - X v) * (X u - X w) * (X v - X w) * ddiff v w (ddiff u w (ddiff u v f)) =
      f - rename (swap u v) f - rename (swap v w) f - rename (swap u w) f
        + rename (swap u w) (rename (swap u v) f)
        + rename (swap v w) (rename (swap u v) f) := by
  obtain ⟨r1, r2, r3, r4⟩ := swap_comp_swap_of_three huv huw hvw
  set D1 := ddiff u v f
  set D2 := ddiff u w D1
  have E1 := ddiff_spec huv f
  have E2 := ddiff_spec huw D1
  have E3 := ddiff_spec hvw D2
  have sE2 := congrArg (rename (swap v w)) E2
  have saE1 := congrArg (rename (swap u w)) E1
  have sbE1 := congrArg (rename (swap v w)) E1
  have hD1 : rename (swap u v) D1 = D1 := rename_swap_ddiff huv f
  have Ecc : rename (swap v w) (rename (swap u w) D1) = rename (swap u w) D1 := by
    rw [rename_rename, r4, ← rename_rename, hD1]
  have h1 : swap v w u = u := swap_apply_of_ne_of_ne huv huw
  have h2 : swap u w v = v := swap_apply_of_ne_of_ne huv.symm hvw
  simp only [map_mul, map_sub, rename_X, swap_apply_left, swap_apply_right, h1, h2] at sE2 saE1 sbE1
  linear_combination (X u - X v) * (X u - X w) * E3 + (X u - X v) * E2 - (X u - X w) * sE2
    + E1 - sbE1 + (X u - X w) * Ecc - saE1

/-- The nilHecke braid relation with explicit strands:
`∂_{vw} ∂_{uw} ∂_{uv} = ∂_{uv} ∂_{uw} ∂_{vw}`. -/
theorem ddiff_braid_labelled (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (f : MvPolynomial σ k) :
    ddiff v w (ddiff u w (ddiff u v f)) = ddiff u v (ddiff u w (ddiff v w f)) := by
  obtain ⟨r1, r2, r3, r4⟩ := swap_comp_swap_of_three huv huw hvw
  have hL := ddiff_braid_labelled_aux huv huw hvw f
  have hR := ddiff_braid_labelled_aux hvw.symm huw.symm huv.symm f
  rw [ddiff_comm huv, ddiff_comm huw, ddiff_comm hvw] at hR
  simp only [map_neg, neg_neg, mul_neg] at hR
  rw [swap_comm w v, swap_comm v u, swap_comm w u, rename_rename, rename_rename, r3,
    r2] at hR
  rw [rename_rename, rename_rename] at hL
  apply X_sub_X_mul_left_cancel huv
  apply X_sub_X_mul_left_cancel huw
  apply X_sub_X_mul_left_cancel hvw
  linear_combination hL - hR

/-- Webster's relation (4c) with explicit strands: with `ψ_{ab} g = P_{ab} (g - s_{ab} g)` for a
symmetric `P`, the difference of the two braid words is a combination of two crossings
followed by renamings. -/
theorem psi_braid_loop {P : MvPolynomial (Fin 2) k} (hP : rename (swap (0 : Fin 2) 1) P = P)
    {u v w : Strand ν} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (g : PolyRing ν k) :
    let ψ : Strand ν → Strand ν → PolyRing ν k → PolyRing ν k :=
      fun a b f => loopFactor P a b * (f - rename (swap a b) f)
    ψ v w (ψ u w (ψ u v g)) - ψ u v (ψ u w (ψ v w g)) =
      -(loopFactor P u v * loopFactor P u w - loopFactor P v w * loopFactor P u w -
          loopFactor P v w * loopFactor P u v) *
          rename (swap u w) (rename (swap u v) (ψ u v g)) +
        -(loopFactor P u v * loopFactor P u w + loopFactor P u v * loopFactor P v w -
          loopFactor P u w * loopFactor P v w) *
          rename (swap u w) (rename (swap v w) (ψ v w g)) := by
  intro ψ
  obtain ⟨r1, r2, r3, r4⟩ := swap_comp_swap_of_three huv huw hvw
  have c2 : ∀ f : Strand ν → Strand ν, ⇑(swap u v) ∘ (⇑(swap v w) ∘ f) =
      ⇑(swap u w) ∘ (⇑(swap u v) ∘ f) := fun f => by rw [← Function.comp_assoc, r2]; rfl
  have c4 : ∀ f : Strand ν → Strand ν, ⇑(swap v w) ∘ (⇑(swap u w) ∘ f) =
      ⇑(swap u w) ∘ (⇑(swap u v) ∘ f) := fun f => by rw [← Function.comp_assoc, r4]; rfl
  have i1 : ∀ a b : Strand ν, ⇑(swap a b) ∘ ⇑(swap a b) = id := fun a b => by
    funext x; simp
  have h1 : swap v w u = u := swap_apply_of_ne_of_ne huv huw
  have h2 : swap u w v = v := swap_apply_of_ne_of_ne huv.symm hvw
  have h3 : swap u v w = w := swap_apply_of_ne_of_ne huw.symm hvw.symm
  have p1 : loopFactor P v u = loopFactor P u v := loopFactor_comm hP _ _
  have p3 : loopFactor P w v = loopFactor P v w := loopFactor_comm hP _ _
  simp only [ψ, map_mul, map_sub, rename_rename, loopFactor_rename, Function.comp_id,
    swap_apply_left, swap_apply_right, h1, h2, h3, p1, p3, r1, r2, r3, r4, c2, c4, i1,
    rename_id, AlgHom.id_apply]
  ring

end Braid

/-! ### Block operators on `V = (FullChamber Γ ν → k[y_s])` -/

section Blocks

variable {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommGroup M] [Module k M]

variable (k) in
/-- The operator `V → V` acting by `a` from the copy of `A` to the copy of `B`. -/
noncomputable def blk (A B : ι) (a : M →ₗ[k] M) : (ι → M) →ₗ[k] (ι → M) :=
  LinearMap.single k (fun _ => M) B ∘ₗ a ∘ₗ LinearMap.proj A

omit [DecidableEq I] in
theorem blk_apply (A B : ι) (a : M →ₗ[k] M) (x : ι → M) :
    blk k A B a x = Pi.single B (a (x A)) := rfl

omit [DecidableEq I] in
theorem blk_comp_blk (A B D : ι) (a b : M →ₗ[k] M) :
    blk k B D b ∘ₗ blk k A B a = blk k A D (b ∘ₗ a) := by
  ext x : 1
  simp [blk_apply]

omit [DecidableEq I] in
theorem blk_comp_blk_of_ne {A B B' D : ι} (h : B ≠ B') (a b : M →ₗ[k] M) :
    blk k B' D b ∘ₗ blk k A B a = 0 := by
  ext x : 1
  simp [blk_apply, Ne.symm h]

omit [DecidableEq I] in
@[simp] theorem blk_zero (A B : ι) : blk k A B (0 : M →ₗ[k] M) = 0 := by
  ext x : 1
  simp [blk_apply]

omit [DecidableEq I] in
theorem blk_add (A B : ι) (a b : M →ₗ[k] M) : blk k A B (a + b) = blk k A B a + blk k A B b := by
  ext x : 1
  simp [blk_apply, Pi.single_add]

omit [DecidableEq I] in
theorem blk_sub (A B : ι) (a b : M →ₗ[k] M) : blk k A B (a - b) = blk k A B a - blk k A B b := by
  ext x : 1
  simp [blk_apply, Pi.single_sub]

omit [DecidableEq I] in
theorem sum_blk_id [Fintype ι] : ∑ A : ι, blk k A A (LinearMap.id : M →ₗ[k] M) = 1 := by
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sum_apply]
  simp only [blk_apply, LinearMap.id_apply, Module.End.one_apply]
  exact Finset.univ_sum_single x

/-- Pointwise application of `a` on every copy. -/
noncomputable def diagOp (a : M →ₗ[k] M) : (ι → M) →ₗ[k] (ι → M) :=
  LinearMap.pi fun A => a ∘ₗ LinearMap.proj A

omit [DecidableEq I] [DecidableEq ι] in
@[simp] theorem diagOp_apply (a : M →ₗ[k] M) (x : ι → M) (A : ι) :
    diagOp (ι := ι) a x A = a (x A) := rfl

omit [DecidableEq I] in
theorem diagOp_comp_blk (A B : ι) (a b : M →ₗ[k] M) :
    diagOp b ∘ₗ blk k A B a = blk k A B (b ∘ₗ a) := by
  ext x : 1
  funext D
  simp only [LinearMap.comp_apply, diagOp_apply, blk_apply, Pi.single_apply]
  split_ifs with h
  · subst h; rfl
  · exact map_zero b

omit [DecidableEq I] in
theorem blk_comp_diagOp (A B : ι) (a b : M →ₗ[k] M) :
    blk k A B a ∘ₗ diagOp b = blk k A B (a ∘ₗ b) := rfl

end Blocks

/-! ### The operators of hyperplane steps -/

section Steps

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Wall.factor_eq (w : Wall Γ ν) : w.factor = loopFactor (k := k) (Γ.Q w.edge) w.src w.tgt :=
  rfl

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem wallOp_eq_mulLeft (w : Wall Γ ν) (σ σ' : Bool) :
    wallOp (k := k) w σ σ' =
      LinearMap.mulLeft k (if σ = false ∧ σ' = true then w.factor else 1) := by
  unfold wallOp
  split_ifs
  · rfl
  · ext f : 1; simp

variable (Γ) in
/-- The operator of crossing the hyperplane `h` from the side `σ` to the side `σ'`. Across a
diagonal from the side `σ`, the left strand is `d.fst` if `σ` and `d.snd` otherwise. -/
noncomputable def hypOp : Hyp Γ ν → Bool → Bool → PolyRing ν k →ₗ[k] PolyRing ν k
  | .inl w, σ, σ' => wallOp w σ σ'
  | .inr d, σ, _ => psiOp Γ (if σ then d.fst else d.snd) (if σ then d.snd else d.fst)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem FullChamber.Adjacent.unique {C C' : FullChamber Γ ν} {h h' : Hyp Γ ν}
    (hh : C.Adjacent C' h) (hh' : C.Adjacent C' h') : h = h' := by
  by_contra hne
  exact hh'.1 (hh.2 h' (Ne.symm hne))

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem FullChamber.Adjacent.apply_eq_not {C C' : FullChamber Γ ν} {h : Hyp Γ ν}
    (hh : C.Adjacent C' h) : C'.1 h = !C.1 h := by
  have := hh.1
  revert this
  cases C.1 h <;> cases C'.1 h <;> simp

variable (Γ) in
/-- The operator of the step from `C` to `C'`: zero unless they are adjacent. -/
noncomputable def stepOp (C C' : FullChamber Γ ν) : PolyRing ν k →ₗ[k] PolyRing ν k :=
  open Classical in
  if hC : ∃ h, C.Adjacent C' h then hypOp Γ hC.choose (C.1 hC.choose) (C'.1 hC.choose) else 0

omit [IsStrictOrderedRing 𝕜] in
theorem stepOp_eq {C C' : FullChamber Γ ν} {h : Hyp Γ ν} (hh : C.Adjacent C' h) :
    stepOp (k := k) Γ C C' = hypOp Γ h (C.1 h) (!C.1 h) := by
  have hC : ∃ h, C.Adjacent C' h := ⟨h, hh⟩
  rw [stepOp, dite_eq_left_of_eq_true (eq_true hC), (hC.choose_spec.unique hh), hh.apply_eq_not]

omit [IsStrictOrderedRing 𝕜] in
theorem stepOp_of_not {C C' : FullChamber Γ ν} (hh : ∀ h, ¬C.Adjacent C' h) :
    stepOp (k := k) Γ C C' = 0 := by
  rw [stepOp, dite_eq_right_of_eq_false (eq_false (not_exists.2 hh))]

end Steps

/-! ### Relabelling hyperplanes and steps -/

section Transport

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem ColPerm.mul_inv_apply (g h : ColPerm ν) (s : Strand ν) :
    (g * h).1⁻¹ s = h.1⁻¹ (g.1⁻¹ s) := rfl

omit [DecidableEq I] in
theorem Diag.eq_of_pair {d d' : Diag ν}
    (h : (d.fst = d'.fst ∧ d.snd = d'.snd) ∨ (d.fst = d'.snd ∧ d.snd = d'.fst)) : d = d' := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Subtype.ext (Prod.ext h₁ h₂)
  · exfalso
    have a := d.2.2
    have b := d'.2.2
    change d.fst.2.val < d.snd.2.val at a
    change d'.fst.2.val < d'.snd.2.val at b
    rw [h₁, h₂] at a
    omega

omit [DecidableEq I] in
theorem Diag.comap_spec (g : ColPerm ν) (d : Diag ν) :
    ((d.comap g).2 = false ∧ (d.comap g).1.fst = g.1⁻¹ d.fst ∧
      (d.comap g).1.snd = g.1⁻¹ d.snd) ∨
    ((d.comap g).2 = true ∧ (d.comap g).1.fst = g.1⁻¹ d.snd ∧
      (d.comap g).1.snd = g.1⁻¹ d.fst) := by
  unfold Diag.comap
  split_ifs
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩

omit [DecidableEq I] in
theorem Diag.comap_one (d : Diag ν) : (d.comap 1).1 = d := by
  apply Diag.eq_of_pair
  rcases Diag.comap_spec 1 d with ⟨-, h₁, h₂⟩ | ⟨-, h₁, h₂⟩
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩

omit [DecidableEq I] in
theorem Diag.comap_mul (g h : ColPerm ν) (d : Diag ν) :
    (d.comap (g * h)).1 = ((d.comap g).1.comap h).1 := by
  apply Diag.eq_of_pair
  rcases Diag.comap_spec (g * h) d with ⟨-, a₁, a₂⟩ | ⟨-, a₁, a₂⟩ <;>
  rcases Diag.comap_spec h (d.comap g).1 with ⟨-, b₁, b₂⟩ | ⟨-, b₁, b₂⟩ <;>
  rcases Diag.comap_spec g d with ⟨-, c₁, c₂⟩ | ⟨-, c₁, c₂⟩ <;>
  simp only [a₁, a₂, b₁, b₂, c₁, c₂, ColPerm.mul_inv_apply, and_self, true_or, or_true]

namespace Hyp

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem comap_one (x : Hyp Γ ν) : x.comap 1 = x := by
  rcases x with w | d
  · rfl
  · exact congrArg Sum.inr (Diag.comap_one d)

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem comap_mul (g h : ColPerm ν) (x : Hyp Γ ν) : x.comap (g * h) = (x.comap g).comap h := by
  rcases x with w | d
  · rfl
  · exact congrArg Sum.inr (Diag.comap_mul g h d)

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem comap_inv_comap (g : ColPerm ν) (x : Hyp Γ ν) : (x.comap g⁻¹).comap g = x := by
  rw [← comap_mul, inv_mul_cancel, comap_one]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] theorem comap_comap_inv (g : ColPerm ν) (x : Hyp Γ ν) : (x.comap g).comap g⁻¹ = x := by
  rw [← comap_mul, mul_inv_cancel, comap_one]

end Hyp

namespace FullChamber

omit [DecidableEq I] in
theorem smul_apply (g : ColPerm ν) (C : FullChamber Γ ν) (x : Hyp Γ ν) :
    (g • C).1 x = if x.reverses g then !C.1 (x.comap g) else C.1 (x.comap g) := rfl

omit [DecidableEq I] in
theorem Adjacent.smul {C C' : FullChamber Γ ν} {h : Hyp Γ ν} (hh : C.Adjacent C' h)
    (g : ColPerm ν) : (g • C).Adjacent (g • C') (h.comap g⁻¹) := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [smul_apply, smul_apply, Hyp.comap_inv_comap]
    have := hh.1
    split_ifs <;> simpa using this
  · have hx' : x.comap g ≠ h := fun e => hx (by rw [← e, Hyp.comap_comap_inv])
    rw [smul_apply, smul_apply, hh.2 _ hx']

omit [DecidableEq I] in
theorem Adjacent.of_smul {C C' : FullChamber Γ ν} {h : Hyp Γ ν} (g : ColPerm ν)
    (hh : (g • C).Adjacent (g • C') h) : C.Adjacent C' (h.comap g) := by
  have := hh.smul g⁻¹
  rwa [inv_smul_smul, inv_smul_smul, inv_inv] at this

end FullChamber

/-- Renaming the variables by a relabelling. -/
noncomputable abbrev ren (g : ColPerm ν) : PolyRing ν k →ₗ[k] PolyRing ν k :=
  (rename (R := k) ⇑g.1).toLinearMap

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Wall.rename_factor_comap (g : ColPerm ν) (w : Wall Γ ν) :
    rename ⇑g.1 (w.comap g).factor = w.factor (k := k) := by
  rw [Wall.factor_eq, Wall.factor_eq, loopFactor_rename]
  show loopFactor _ (g.1 (g.1⁻¹ w.src)) (g.1 (g.1⁻¹ w.tgt)) = _
  rw [show ∀ x, g.1 (g.1⁻¹ x) = x from fun x => g.1.apply_symm_apply x,
    show ∀ x, g.1 (g.1⁻¹ x) = x from fun x => g.1.apply_symm_apply x]
  rfl

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem ren_comp_hypOp (g : ColPerm ν) (x : Hyp Γ ν) (σ : Bool) :
    ren (k := k) g ∘ₗ hypOp Γ (x.comap g) σ (!σ) =
      hypOp Γ x (if x.reverses g then !σ else σ) (!(if x.reverses g then !σ else σ)) ∘ₗ
        ren g := by
  rcases x with w | d
  · simp only [Hyp.comap, Hyp.reverses, Bool.false_eq_true, ↓reduceIte, hypOp,
      wallOp_eq_mulLeft]
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply,
      map_mul]
    split_ifs
    · rw [Wall.rename_factor_comap]
    · rw [map_one]
  · simp only [Hyp.comap, Hyp.reverses, hypOp]
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    have hne : ∀ τ : Bool, (if τ then (d.comap g).1.fst else (d.comap g).1.snd) ≠
        (if τ then (d.comap g).1.snd else (d.comap g).1.fst) := by
      intro τ
      cases τ
      · exact (d.comap g).1.fst_ne_snd.symm
      · exact (d.comap g).1.fst_ne_snd
    rw [psiOp_rename g.1 (ColPerm.apply_fst g) (hne σ)]
    rcases Diag.comap_spec g d with ⟨e, h₁, h₂⟩ | ⟨e, h₁, h₂⟩ <;>
      cases σ <;> simp [e, h₁, h₂]

theorem ren_comp_stepOp (g : ColPerm ν) (C C' : FullChamber Γ ν) :
    ren (k := k) g ∘ₗ stepOp Γ C C' = stepOp Γ (g • C) (g • C') ∘ₗ ren g := by
  by_cases hC : ∃ h, C.Adjacent C' h
  · obtain ⟨h, hh⟩ := hC
    rw [stepOp_eq hh, stepOp_eq (hh.smul g), FullChamber.smul_apply]
    have := ren_comp_hypOp (k := k) g (h.comap g⁻¹) (C.1 h)
    simpa only [Hyp.comap_inv_comap] using this
  · push Not at hC
    have hC' : ∀ h, ¬(g • C).Adjacent (g • C') h := fun h hh => hC _ (hh.of_smul g)
    rw [stepOp_of_not hC, stepOp_of_not hC', LinearMap.comp_zero, LinearMap.zero_comp]

end Transport

end Categorification.WeightedKLR
