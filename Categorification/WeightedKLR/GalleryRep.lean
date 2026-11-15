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

/-! ### Bigons, polynomials past steps and squares -/

section Local

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Diag.fst_label_eq_snd (d : Diag ν) : d.fst.1 = d.snd.1 := d.2.1

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.left_ne_right (C : FullChamber Γ ν) (d : Diag ν) : d.left C ≠ d.right C := by
  unfold Diag.left Diag.right
  split_ifs
  · exact d.fst_ne_snd
  · exact d.fst_ne_snd.symm

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.left_label (C : FullChamber Γ ν) (d : Diag ν) : (d.left C).1 = d.fst.1 := by
  unfold Diag.left
  split_ifs
  · rfl
  · exact d.fst_label_eq_snd.symm

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.right_label (C : FullChamber Γ ν) (d : Diag ν) : (d.right C).1 = d.fst.1 := by
  unfold Diag.right
  split_ifs
  · exact d.fst_label_eq_snd.symm
  · rfl

omit [IsStrictOrderedRing 𝕜] in
theorem Diag.swap_left_right (C : FullChamber Γ ν) (d : Diag ν) :
    swap (d.left C) (d.right C) = swap d.fst d.snd := by
  unfold Diag.left Diag.right
  split_ifs
  · rfl
  · exact swap_comm _ _

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.left_of_adjacent {C C' : FullChamber Γ ν} {d : Diag ν}
    (h : C.Adjacent C' (.inr d)) : d.left C' = d.right C := by
  unfold Diag.left Diag.right
  rw [h.apply_eq_not]
  cases C.1 (.inr d) <;> rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.right_of_adjacent {C C' : FullChamber Γ ν} {d : Diag ν}
    (h : C.Adjacent C' (.inr d)) : d.right C' = d.left C := by
  unfold Diag.left Diag.right
  rw [h.apply_eq_not]
  cases C.1 (.inr d) <;> rfl

omit [IsStrictOrderedRing 𝕜] in
theorem stepOp_inl {C C' : FullChamber Γ ν} {w : Wall Γ ν} (h : C.Adjacent C' (.inl w)) :
    stepOp (k := k) Γ C C' = wallOp w (C.1 (.inl w)) (!C.1 (.inl w)) :=
  stepOp_eq h

omit [IsStrictOrderedRing 𝕜] in
theorem stepOp_inr {C C' : FullChamber Γ ν} {d : Diag ν} (h : C.Adjacent C' (.inr d)) :
    stepOp (k := k) Γ C C' = psiOp Γ (d.left C) (d.right C) :=
  stepOp_eq h

omit [IsStrictOrderedRing 𝕜] in
/-- The ghost bigon in the representation. -/
theorem stepOp_comp_stepOp_inl {C C' : FullChamber Γ ν} {w : Wall Γ ν}
    (h : C.Adjacent C' (.inl w)) :
    stepOp (k := k) Γ C' C ∘ₗ stepOp Γ C C' = LinearMap.mulLeft k w.factor := by
  rw [stepOp_inl h, stepOp_inl h.symm, h.apply_eq_not, Bool.not_not]
  exact wallOp_comp_wallOp w (by cases C.1 (.inl w) <;> decide)

omit [IsStrictOrderedRing 𝕜] in
/-- The strand bigon in the representation. -/
theorem stepOp_stepOp_inr (hΓ : Γ.PSymm) {C C' : FullChamber Γ ν} {d : Diag ν}
    (h : C.Adjacent C' (.inr d)) (f : PolyRing ν k) :
    stepOp Γ C' C (stepOp Γ C C' f) =
      match Γ.loop d.fst.1 with
      | none => 0
      | some P => -2 * loopFactor P (d.left C) (d.right C) *
          rename (swap d.fst d.snd) (stepOp Γ C C' f) := by
  rw [stepOp_inr h, stepOp_inr h.symm, Diag.left_of_adjacent h, Diag.right_of_adjacent h,
    psiOp_psiOp_swap hΓ (Diag.left_ne_right C d)
      (by rw [Diag.left_label C d, Diag.right_label C d]),
    Diag.left_label C d, Diag.swap_left_right C d]

omit [IsStrictOrderedRing 𝕜] in
/-- Polynomials past a diagonal step in the representation. -/
theorem stepOp_mul_inr {C C' : FullChamber Γ ν} {d : Diag ν} (h : C.Adjacent C' (.inr d))
    (f g : PolyRing ν k) :
    stepOp Γ C C' (f * g) - f * stepOp Γ C C' g =
      stepFactor Γ (d.left C) (d.right C) f * rename (swap d.fst d.snd) g := by
  rw [stepOp_inr h, psiOp_leibniz (Diag.left_ne_right C d), Diag.swap_left_right C d]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Wall.rename_swap_factor (w : Wall Γ ν) {a b : Strand ν} (ha₁ : a ≠ w.src)
    (ha₂ : a ≠ w.tgt) (hb₁ : b ≠ w.src) (hb₂ : b ≠ w.tgt) :
    rename (swap a b) (w.factor (k := k)) = w.factor := by
  rw [Wall.factor_eq, loopFactor_rename, swap_apply_of_ne_of_ne ha₁.symm hb₁.symm,
    swap_apply_of_ne_of_ne ha₂.symm hb₂.symm]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem wallOp_psiOp_comm (w : Wall Γ ν) {a b : Strand ν} (hab : a ≠ b) (ha₁ : a ≠ w.src)
    (ha₂ : a ≠ w.tgt) (hb₁ : b ≠ w.src) (hb₂ : b ≠ w.tgt) (σ σ' : Bool) :
    wallOp (k := k) w σ σ' ∘ₗ psiOp Γ a b = psiOp Γ a b ∘ₗ wallOp w σ σ' := by
  rw [wallOp_eq_mulLeft]
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [psiOp_mul_of_rename_eq hab]
  split_ifs
  · exact Wall.rename_swap_factor w ha₁ ha₂ hb₁ hb₂
  · exact map_one _

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The operators of two independent hyperplanes commute. -/
theorem hypOp_comm {h₁ h₂ : Hyp Γ ν} (hi : h₁.Independent h₂) (σ₁ σ₁' σ₂ σ₂' : Bool) :
    hypOp (k := k) Γ h₂ σ₂ σ₂' ∘ₗ hypOp Γ h₁ σ₁ σ₁' =
      hypOp Γ h₁ σ₁ σ₁' ∘ₗ hypOp Γ h₂ σ₂ σ₂' := by
  rcases h₁ with w₁ | d₁ <;> rcases h₂ with w₂ | d₂
  · simp only [hypOp, wallOp_eq_mulLeft]
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    ring
  · rcases hi with ⟨-, h⟩ | hd
    · exact absurd h (by simp)
    simp only [Hyp.strands, Finset.disjoint_insert_left, Finset.disjoint_insert_right,
      Finset.mem_insert, Finset.mem_singleton, Finset.disjoint_singleton, not_or] at hd
    simp only [hypOp]
    have hne : ∀ τ : Bool, (if τ then d₂.fst else d₂.snd) ≠ (if τ then d₂.snd else d₂.fst) := by
      intro τ; cases τ
      · exact d₂.fst_ne_snd.symm
      · exact d₂.fst_ne_snd
    cases σ₂ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first
      | exact (wallOp_psiOp_comm w₁ (hne false) (by tauto) (by tauto) (by tauto) (by tauto) _
          _).symm
      | exact (wallOp_psiOp_comm w₁ (hne true) (by tauto) (by tauto) (by tauto) (by tauto) _
          _).symm
  · rcases hi with ⟨h, -⟩ | hd
    · exact absurd h (by simp)
    simp only [Hyp.strands, Finset.disjoint_insert_left, Finset.disjoint_insert_right,
      Finset.mem_insert, Finset.mem_singleton, Finset.disjoint_singleton, not_or] at hd
    simp only [hypOp]
    have hne : ∀ τ : Bool, (if τ then d₁.fst else d₁.snd) ≠ (if τ then d₁.snd else d₁.fst) := by
      intro τ; cases τ
      · exact d₁.fst_ne_snd.symm
      · exact d₁.fst_ne_snd
    cases σ₁ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      first
      | exact (wallOp_psiOp_comm w₂ (hne false) (by tauto) (by tauto) (by tauto) (by tauto) _ _)
      | exact (wallOp_psiOp_comm w₂ (hne true) (by tauto) (by tauto) (by tauto) (by tauto) _ _)
  · rcases hi with ⟨h, -⟩ | hd
    · exact absurd h (by simp)
    simp only [Hyp.strands, Finset.disjoint_insert_left, Finset.disjoint_insert_right,
      Finset.mem_insert, Finset.mem_singleton, Finset.disjoint_singleton, not_or] at hd
    simp only [hypOp]
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply]
    cases σ₁ <;> cases σ₂ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact (psiOp_psiOp_comm (Γ := Γ)
        (by first | exact Diag.fst_ne_snd _ | exact (Diag.fst_ne_snd _).symm)
        (by first | exact Diag.fst_ne_snd _ | exact (Diag.fst_ne_snd _).symm)
        (by first | exact Diag.fst_label_eq_snd _ | exact (Diag.fst_label_eq_snd _).symm)
        (by first | exact Diag.fst_label_eq_snd _ | exact (Diag.fst_label_eq_snd _).symm)
        (by tauto) (by tauto) (by tauto) (by tauto) f).symm

omit [IsStrictOrderedRing 𝕜] in
/-- The square relation in the representation. -/
theorem stepOp_square {C B B' D : FullChamber Γ ν} {h₁ h₂ : Hyp Γ ν} (hne : h₁ ≠ h₂)
    (hi : h₁.Independent h₂) (a₁ : C.Adjacent B h₁) (a₂ : B.Adjacent D h₂)
    (a₃ : C.Adjacent B' h₂) (a₄ : B'.Adjacent D h₁) :
    stepOp (k := k) Γ B D ∘ₗ stepOp Γ C B = stepOp Γ B' D ∘ₗ stepOp Γ C B' := by
  rw [stepOp_eq a₁, stepOp_eq a₂, stepOp_eq a₃, stepOp_eq a₄, ← a₁.2 h₂ hne.symm,
    ← a₃.2 h₁ hne]
  exact hypOp_comm hi _ _ _ _

end Local

/-! ### Hexagons -/

section Hexagons

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [IsStrictOrderedRing 𝕜] in
/-- The operator of the gallery `A₀ → A₁ → A₂ → A₃`, read off the sides of `A₀`. -/
theorem Hexagon.stepOp_gal₁ (H : Hexagon Γ ν) :
    stepOp (k := k) Γ H.A₂ H.A₃ ∘ₗ stepOp Γ H.A₁ H.A₂ ∘ₗ stepOp Γ H.A₀ H.A₁ =
      hypOp Γ H.h₃ (H.A₀.1 H.h₃) (!H.A₀.1 H.h₃) ∘ₗ hypOp Γ H.h₂ (H.A₀.1 H.h₂) (!H.A₀.1 H.h₂) ∘ₗ
        hypOp Γ H.h₁ (H.A₀.1 H.h₁) (!H.A₀.1 H.h₁) := by
  rw [stepOp_eq H.adj₀₁, stepOp_eq H.adj₁₂, stepOp_eq H.adj₂₃, ← H.adj₁₂.2 H.h₃ H.ne₂₃.symm,
    ← H.adj₀₁.2 H.h₃ H.ne₁₃.symm, ← H.adj₀₁.2 H.h₂ H.ne₁₂.symm]

omit [IsStrictOrderedRing 𝕜] in
/-- The operator of the gallery `A₀ → A₅ → A₄ → A₃`, read off the sides of `A₀`. -/
theorem Hexagon.stepOp_gal₂ (H : Hexagon Γ ν) :
    stepOp (k := k) Γ H.A₄ H.A₃ ∘ₗ stepOp Γ H.A₅ H.A₄ ∘ₗ stepOp Γ H.A₀ H.A₅ =
      hypOp Γ H.h₁ (H.A₀.1 H.h₁) (!H.A₀.1 H.h₁) ∘ₗ hypOp Γ H.h₂ (H.A₀.1 H.h₂) (!H.A₀.1 H.h₂) ∘ₗ
        hypOp Γ H.h₃ (H.A₀.1 H.h₃) (!H.A₀.1 H.h₃) := by
  rw [stepOp_eq H.adj₀₅, stepOp_eq H.adj₅₄, stepOp_eq H.adj₄₃, ← H.adj₅₄.2 H.h₁ H.ne₁₂,
    ← H.adj₀₅.2 H.h₁ H.ne₁₃, ← H.adj₀₅.2 H.h₂ H.ne₂₃]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Three walls: the operators are multiplications and commute. -/
theorem hypOp_walls {h₁ h₂ h₃ : Hyp Γ ν} (e₁ : h₁.isLeft) (e₂ : h₂.isLeft) (e₃ : h₃.isLeft)
    (σ₁ σ₂ σ₃ : Bool) :
    hypOp (k := k) Γ h₃ σ₃ (!σ₃) ∘ₗ hypOp Γ h₂ σ₂ (!σ₂) ∘ₗ hypOp Γ h₁ σ₁ (!σ₁) =
      hypOp Γ h₁ σ₁ (!σ₁) ∘ₗ hypOp Γ h₂ σ₂ (!σ₂) ∘ₗ hypOp Γ h₃ σ₃ (!σ₃) := by
  rcases h₁ with w₁ | d₁ <;> rcases h₂ with w₂ | d₂ <;> rcases h₃ with w₃ | d₃ <;>
    simp only [Sum.isLeft_inl, Sum.isLeft_inr, Bool.false_eq_true] at e₁ e₂ e₃
  simp only [hypOp, wallOp_eq_mulLeft]
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  ring

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Wall.factor_comap_refl (w : Wall Γ ν) (d : Diag ν) :
    (w.comap d.refl).factor (k := k) = rename (swap d.fst d.snd) w.factor := by
  rw [← Wall.rename_factor_comap d.refl w]
  exact (rename_swap_rename_swap d.fst d.snd _).symm

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A strand crossing two strands of one colour through a ghost, the diagonal crossed in the
middle: Webster's relations (4a), (4b) in the representation. -/
theorem hypOp_mid_diag (w : Wall Γ ν) (d : Diag ν) {l r : Strand ν} (hlr : l ≠ r)
    (hs : swap l r = swap d.fst d.snd) {σ τ : Bool} (hστ : σ ≠ τ) :
    wallOp (k := k) (w.comap d.refl) τ (!τ) ∘ₗ psiOp Γ l r ∘ₗ wallOp w σ (!σ) -
        wallOp w σ (!σ) ∘ₗ psiOp Γ l r ∘ₗ wallOp (w.comap d.refl) τ (!τ) =
      LinearMap.mulLeft k (stepFactor Γ l r w.factor) ∘ₗ ren d.refl := by
  have hF := Wall.factor_comap_refl (k := k) w d
  rw [← hs] at hF
  have hR : ∀ f, ren (k := k) d.refl f = rename (swap l r) f := fun f => by
    rw [hs]; rfl
  refine LinearMap.ext fun f => ?_
  have L := psiOp_leibniz (Γ := Γ) hlr
  cases σ <;> cases τ <;> simp only [ne_eq, not_true_eq_false] at hστ <;>
    simp only [wallOp_eq_mulLeft, hF, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, hR, Bool.not_false, Bool.not_true, and_true,
      Bool.false_eq_true, and_false, ↓reduceIte, one_mul]
  · exact L _ _
  · rw [← neg_sub, L, stepFactor_rename_swap hlr, neg_mul, neg_neg]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The same flat with the diagonal crossed first or last: both walls act alike, by
multiplication by a polynomial symmetric in the two strands, or trivially. -/
theorem hypOp_end_diag (w : Wall Γ ν) (d : Diag ν) {l r : Strand ν} (hlr : l ≠ r)
    (hs : swap l r = swap d.fst d.snd) (σ : Bool) :
    wallOp (k := k) (w.comap d.refl) σ (!σ) ∘ₗ wallOp w σ (!σ) ∘ₗ psiOp Γ l r =
      psiOp Γ l r ∘ₗ wallOp w σ (!σ) ∘ₗ wallOp (w.comap d.refl) σ (!σ) := by
  have hF := Wall.factor_comap_refl (k := k) w d
  rw [← hs] at hF
  refine LinearMap.ext fun f => ?_
  cases σ
  · simp only [wallOp_eq_mulLeft, hF, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Bool.not_false, and_self, ↓reduceIte]
    have hc : rename (swap l r) (rename (swap l r) w.factor * w.factor) =
        rename (swap l r) w.factor * w.factor := by
      rw [map_mul, rename_swap_rename_swap, mul_comm]
    rw [← mul_assoc, ← mul_assoc, ← psiOp_mul_of_rename_eq hlr hc, mul_comm (w.factor)]
  · simp only [wallOp_eq_mulLeft, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Bool.not_true, Bool.true_eq_false, false_and, ↓reduceIte, one_mul]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Without a loop, `ψ` on either orientation of a pair is a multiple of one divided
difference. -/
theorem psiOp_pair_of_none {u v a b : Strand ν} (huv : u ≠ v) (hc : u.1 = v.1)
    (h : Γ.loop u.1 = none) (hab : (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    ∃ c : k, psiOp (k := k) Γ a b = c • ddiff u v := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨1, by rw [psiOp_of_none h, one_smul]⟩
  · refine ⟨-1, LinearMap.ext fun f => ?_⟩
    rw [psiOp_of_none (hc ▸ h), ddiff_comm huv, LinearMap.smul_apply, neg_one_smul]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- With a symmetric loop, `ψ` does not depend on the orientation of the pair. -/
theorem psiOp_pair_of_some {u v a b : Strand ν} {P : MvPolynomial (Fin 2) k}
    (hP : rename (swap (0 : Fin 2) 1) P = P) (hc : u.1 = v.1) (h : Γ.loop u.1 = some P)
    (hab : (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    psiOp (k := k) Γ a b = psiOp Γ u v := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact LinearMap.ext fun f => psiOp_swap_of_some hP h (hc ▸ h) f

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Three strands of one colour without a loop: the braid relation. -/
theorem psiOp_braid_of_none {u v w a₁ b₁ a₂ b₂ a₃ b₃ : Strand ν} (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) (hc₁ : u.1 = v.1) (hc₂ : u.1 = w.1) (h : Γ.loop u.1 = none)
    (j₁ : (a₁ = u ∧ b₁ = v) ∨ (a₁ = v ∧ b₁ = u)) (j₂ : (a₂ = u ∧ b₂ = w) ∨ (a₂ = w ∧ b₂ = u))
    (j₃ : (a₃ = v ∧ b₃ = w) ∨ (a₃ = w ∧ b₃ = v)) :
    psiOp (k := k) Γ a₃ b₃ ∘ₗ psiOp Γ a₂ b₂ ∘ₗ psiOp Γ a₁ b₁ =
      psiOp Γ a₁ b₁ ∘ₗ psiOp Γ a₂ b₂ ∘ₗ psiOp Γ a₃ b₃ := by
  obtain ⟨c₁, e₁⟩ := psiOp_pair_of_none huv hc₁ h j₁
  obtain ⟨c₂, e₂⟩ := psiOp_pair_of_none huw hc₂ h j₂
  obtain ⟨c₃, e₃⟩ := psiOp_pair_of_none hvw (hc₁.symm.trans hc₂) (hc₁ ▸ h) j₃
  rw [e₁, e₂, e₃]
  refine LinearMap.ext fun f => ?_
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul,
    ddiff_braid_labelled huv huw hvw]
  congr 1
  ring

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Three strands of one colour with a loop: Webster's relation (4c). -/
theorem psiOp_braid_of_some {u v w a₁ b₁ a₂ b₂ a₃ b₃ : Strand ν} {P : MvPolynomial (Fin 2) k}
    (hP : rename (swap (0 : Fin 2) 1) P = P) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) (hc₁ : u.1 = v.1) (hc₂ : u.1 = w.1) (h : Γ.loop u.1 = some P)
    (j₁ : (a₁ = u ∧ b₁ = v) ∨ (a₁ = v ∧ b₁ = u)) (j₂ : (a₂ = u ∧ b₂ = w) ∨ (a₂ = w ∧ b₂ = u))
    (j₃ : (a₃ = v ∧ b₃ = w) ∨ (a₃ = w ∧ b₃ = v)) (f : PolyRing ν k) :
    psiOp (k := k) Γ a₃ b₃ (psiOp Γ a₂ b₂ (psiOp Γ a₁ b₁ f)) -
        psiOp Γ a₁ b₁ (psiOp Γ a₂ b₂ (psiOp Γ a₃ b₃ f)) =
      -(loopFactor P u v * loopFactor P u w - loopFactor P v w * loopFactor P u w -
          loopFactor P v w * loopFactor P u v) *
          rename (swap u w) (rename (swap u v) (psiOp Γ a₁ b₁ f)) +
        -(loopFactor P u v * loopFactor P u w + loopFactor P u v * loopFactor P v w -
          loopFactor P u w * loopFactor P v w) *
          rename (swap u w) (rename (swap v w) (psiOp Γ a₃ b₃ f)) := by
  have hv : Γ.loop v.1 = some P := hc₁ ▸ h
  rw [psiOp_pair_of_some hP hc₁ h j₁, psiOp_pair_of_some hP hc₂ h j₂,
    psiOp_pair_of_some hP (hc₁.symm.trans hc₂) hv j₃]
  simp only [psiOp_of_some h, psiOp_of_some hv]
  exact psi_braid_loop hP huv huw hvw f

end Hexagons

/-! ### The representation -/

section Assembly

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [IsStrictOrderedRing 𝕜] in
theorem hypOp_inr_left (C : FullChamber Γ ν) (d : Diag ν) (σ' : Bool) :
    hypOp (k := k) Γ (.inr d) (C.1 (.inr d)) σ' = psiOp Γ (d.left C) (d.right C) := rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.Joins.left_right {d : Diag ν} {a b : Strand ν} (h : d.Joins a b)
    (C : FullChamber Γ ν) : (d.left C = a ∧ d.right C = b) ∨ (d.left C = b ∧ d.right C = a) := by
  unfold Diag.left Diag.right
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> split_ifs <;> simp

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.Joins.ne {d : Diag ν} {a b : Strand ν} (h : d.Joins a b) : a ≠ b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact d.fst_ne_snd
  · exact d.fst_ne_snd.symm

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem Diag.Joins.label_eq {d : Diag ν} {a b : Strand ν} (h : d.Joins a b) : a.1 = b.1 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact d.fst_label_eq_snd
  · exact d.fst_label_eq_snd.symm

omit [IsStrictOrderedRing 𝕜] in
theorem Diag.Joins.swap_eq {d : Diag ν} {a b : Strand ν} (h : d.Joins a b) :
    swap d.fst d.snd = swap a b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact swap_comm _ _

omit [IsStrictOrderedRing 𝕜] in
theorem Diag.refl_mul_refl (d : Diag ν) : d.refl * d.refl = 1 :=
  Subtype.ext (swap_mul_self _ _)

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem ren_mul_apply (g h : ColPerm ν) (f : PolyRing ν k) :
    ren (k := k) (g * h) f = ren g (ren h f) := by
  simp only [ren, AlgHom.toLinearMap_apply, rename_rename]
  rfl

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
theorem ren_one : ren (k := k) (1 : ColPerm ν) = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  simp only [ren, AlgHom.toLinearMap_apply, LinearMap.id_apply]
  exact rename_id_apply f

variable (k Γ ν) in
/-- The action of the generators on `V = (FullChamber Γ ν → k[y_s])`. -/
noncomputable def genOp : Gen k Γ ν → Module.End k (FullChamber Γ ν → PolyRing ν k)
  | .idem C => blk k C C LinearMap.id
  | .poly f => diagOp (LinearMap.mulLeft k f)
  | .step C C' => blk k C C' (stepOp Γ C C')
  | .relabel g C => blk k C (g • C) (ren g)

variable (k Γ ν) in
/-- The action of the free algebra on the generators. -/
noncomputable def freeRep :
    FreeAlgebra k (Gen k Γ ν) →ₐ[k] Module.End k (FullChamber Γ ν → PolyRing ν k) :=
  FreeAlgebra.lift k (genOp k Γ ν)

theorem freeRep_gal₁ (H : Hexagon Γ ν) :
    freeRep k Γ ν (H.gal₁ k Γ ν) =
      blk k H.A₀ H.A₃ (stepOp Γ H.A₂ H.A₃ ∘ₗ stepOp Γ H.A₁ H.A₂ ∘ₗ stepOp Γ H.A₀ H.A₁) := by
  simp only [Hexagon.gal₁, freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp,
    Module.End.mul_eq_comp, blk_comp_blk, LinearMap.comp_assoc]

theorem freeRep_gal₂ (H : Hexagon Γ ν) :
    freeRep k Γ ν (H.gal₂ k Γ ν) =
      blk k H.A₀ H.A₃ (stepOp Γ H.A₄ H.A₃ ∘ₗ stepOp Γ H.A₅ H.A₄ ∘ₗ stepOp Γ H.A₀ H.A₅) := by
  simp only [Hexagon.gal₂, freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp,
    Module.End.mul_eq_comp, blk_comp_blk, LinearMap.comp_assoc]

/-- The representation respects the defining relations of the gallery algebra. -/
theorem freeRep_rel (hΓ : Γ.PSymm) {x y : FreeAlgebra k (Gen k Γ ν)} (h : Rel k Γ ν x y) :
    freeRep k Γ ν x = freeRep k Γ ν y := by
  cases h with
  | idem_mul C D =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp]
    split_ifs with hCD
    · subst hCD
      rw [blk_comp_blk, LinearMap.id_comp, FreeAlgebra.lift_ι_apply]
      rfl
    · rw [blk_comp_blk_of_ne (Ne.symm hCD), map_zero]
  | idem_sum =>
    simp only [freeRep, map_sum, FreeAlgebra.lift_ι_apply, genOp, map_one]
    exact sum_blk_id
  | poly_add f g =>
    simp only [freeRep, map_add, FreeAlgebra.lift_ι_apply, genOp]
    refine LinearMap.ext fun x => ?_
    funext A
    simp [add_mul]
  | poly_mul f g =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp]
    refine LinearMap.ext fun x => ?_
    funext A
    simp
  | poly_C c =>
    simp only [freeRep, AlgHom.commutes, FreeAlgebra.lift_ι_apply, genOp]
    refine LinearMap.ext fun x => ?_
    funext A
    simp [Module.algebraMap_end_apply, C_mul']
  | poly_idem f C =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
      diagOp_comp_blk, blk_comp_diagOp, LinearMap.comp_id, LinearMap.id_comp]
  | step_idem C C' =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
      blk_comp_blk, LinearMap.comp_id, LinearMap.id_comp]
  | step_zero C C' hC =>
    simp only [freeRep, FreeAlgebra.lift_ι_apply, genOp, stepOp_of_not hC, blk_zero, map_zero]
  | relabel_idem g C =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
      blk_comp_blk, LinearMap.comp_id, LinearMap.id_comp]
  | relabel_one C =>
    simp only [freeRep, FreeAlgebra.lift_ι_apply, genOp, one_smul, ren_one]
  | relabel_mul g h C =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
      blk_comp_blk, mul_smul]
    congr 1
    exact LinearMap.ext fun f => (ren_mul_apply g h f).symm
  | relabel_poly g C f =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
      diagOp_comp_blk, blk_comp_diagOp]
    congr 1
    refine LinearMap.ext fun p => ?_
    simp [ren, map_mul]
  | relabel_step g C C' =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
      blk_comp_blk, ren_comp_stepOp]
  | wall_bigon C C' w h =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
      blk_comp_blk, diagOp_comp_blk, LinearMap.comp_id, stepOp_comp_stepOp_inl h]
  | diag_bigon C C' d h =>
    rcases hl : Γ.loop d.fst.1 with _ | P
    · simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
        blk_comp_blk, map_zero]
      convert blk_zero (k := k) C C
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.comp_apply, stepOp_stepOp_inr hΓ h f, hl, LinearMap.zero_apply]
    · simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
        blk_comp_blk, diagOp_comp_blk, h.symm.refl_smul]
      congr 1
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.comp_apply, stepOp_stepOp_inr hΓ h f, hl, LinearMap.mulLeft_apply]
      rfl
  | wall_poly C C' w h f =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
      diagOp_comp_blk, blk_comp_diagOp, stepOp_inl h, wallOp_eq_mulLeft]
    congr 1
    refine LinearMap.ext fun p => ?_
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
    ring
  | diag_poly C C' d h f =>
    simp only [freeRep, map_mul, map_sub, FreeAlgebra.lift_ι_apply, genOp,
      Module.End.mul_eq_comp, diagOp_comp_blk, blk_comp_diagOp, h.refl_smul, ← blk_sub]
    congr 1
    refine LinearMap.ext fun g => ?_
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    exact stepOp_mul_inr h f g
  | square C B B' D h₁ h₂ hne hi a₁ a₂ a₃ a₄ =>
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
      blk_comp_blk, stepOp_square hne hi a₁ a₂ a₃ a₄]
  | hex_walls H e₁ e₂ e₃ =>
    rw [freeRep_gal₁, freeRep_gal₂, H.stepOp_gal₁, H.stepOp_gal₂, hypOp_walls e₁ e₂ e₃]
  | hex_mid_diag H w d h₁ h₂ h₃ hσ hA =>
    have e₁ : H.A₁.1 H.h₂ = H.A₀.1 H.h₂ := (H.adj₀₁.2 _ H.ne₁₂.symm).symm
    rw [h₂] at e₁
    have hl : d.left H.A₁ = d.left H.A₀ := by unfold Diag.left; rw [e₁]
    have hr : d.right H.A₁ = d.right H.A₀ := by unfold Diag.right; rw [e₁]
    rw [map_sub, freeRep_gal₁, freeRep_gal₂, H.stepOp_gal₁, H.stepOp_gal₂, ← blk_sub, h₁, h₂,
      h₃, hypOp_inr_left, hl, hr]
    simp only [freeRep, map_mul, FreeAlgebra.lift_ι_apply, genOp, Module.End.mul_eq_comp,
      diagOp_comp_blk, hA]
    congr 1
    exact hypOp_mid_diag w d (Diag.left_ne_right _ d) (Diag.swap_left_right _ d) hσ
  | hex_end_diag H w d h₂ hd hσ =>
    rw [freeRep_gal₁, freeRep_gal₂, H.stepOp_gal₁, H.stepOp_gal₂]
    congr 1
    rcases hd with ⟨h₁, h₃⟩ | ⟨h₁, h₃⟩
    · rw [h₁, h₂, h₃, hypOp_inr_left, ← hσ]
      exact hypOp_end_diag w d (Diag.left_ne_right _ d) (Diag.swap_left_right _ d) _
    · rw [h₁, h₂, h₃, hypOp_inr_left, ← hσ]
      exact (hypOp_end_diag w d (Diag.left_ne_right _ d) (Diag.swap_left_right _ d) _).symm
  | hex_diags H d₁ d₂ d₃ u v w h₁ h₂ h₃ j₁ j₂ j₃ hA =>
    have huv := j₁.ne
    have huw := j₂.ne
    have hvw := j₃.ne
    have hc₁ := j₁.label_eq
    have hc₂ := j₂.label_eq
    rw [map_sub, freeRep_gal₁, freeRep_gal₂, H.stepOp_gal₁, H.stepOp_gal₂, ← blk_sub, h₁, h₂,
      h₃, hypOp_inr_left, hypOp_inr_left, hypOp_inr_left]
    rcases hl : Γ.loop u.1 with _ | P
    · simp only [map_zero]
      rw [psiOp_braid_of_none huv huw hvw hc₁ hc₂ hl (j₁.left_right _) (j₂.left_right _)
        (j₃.left_right _), sub_self, blk_zero]
    · have hP := hΓ u.1 P hl
      have a₁ : H.A₀.Adjacent H.A₁ (.inr d₁) := h₁ ▸ H.adj₀₁
      have a₅ : H.A₀.Adjacent H.A₅ (.inr d₃) := h₃ ▸ H.adj₀₅
      have g₁ : (d₂.refl * d₁.refl) • H.A₁ = H.A₃ := by
        rw [← a₁.refl_smul, ← mul_smul, mul_assoc, Diag.refl_mul_refl, mul_one, hA]
      have g₂ : (d₂.refl * d₃.refl) • H.A₅ = H.A₃ := by
        rw [← a₅.refl_smul, ← mul_smul, mul_assoc, Diag.refl_mul_refl, mul_one, hA]
      simp only [Hexagon.loopCorrection, freeRep, map_add, map_mul, FreeAlgebra.lift_ι_apply,
        genOp, Module.End.mul_eq_comp, blk_comp_blk, diagOp_comp_blk, g₁, g₂, ← blk_add,
        stepOp_inr a₁, stepOp_inr a₅]
      congr 1
      refine LinearMap.ext fun f => ?_
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.mulLeft_apply, ren_mul_apply]
      have r₁ : ∀ p, ren (k := k) d₁.refl p = rename (swap u v) p := fun p => by
        rw [← j₁.swap_eq]; rfl
      have r₂ : ∀ p, ren (k := k) d₂.refl p = rename (swap u w) p := fun p => by
        rw [← j₂.swap_eq]; rfl
      have r₃ : ∀ p, ren (k := k) d₃.refl p = rename (swap v w) p := fun p => by
        rw [← j₃.swap_eq]; rfl
      rw [r₁, r₂, r₂, r₃]
      exact psiOp_braid_of_some hP huv huw hvw hc₁ hc₂ hl (j₁.left_right _) (j₂.left_right _)
        (j₃.left_right _) f

variable (k) in
/-- The polynomial representation of the gallery algebra (B. Webster, arXiv:1209.2463v4,
Proposition `prop:action`, for labelled strands), for symmetric loop polynomials. -/
noncomputable def galleryRep (hΓ : Γ.PSymm) :
    GalleryAlgebra k Γ ν →ₐ[k] Module.End k (FullChamber Γ ν → PolyRing ν k) :=
  RingQuot.liftAlgHom k ⟨freeRep k Γ ν, fun _ _ h => freeRep_rel hΓ h⟩

theorem galleryRep_mk (hΓ : Γ.PSymm) (x : FreeAlgebra k (Gen k Γ ν)) :
    galleryRep k hΓ (GalleryAlgebra.mk k Γ ν x) = freeRep k Γ ν x :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ x

end Assembly

end Categorification.WeightedKLR
