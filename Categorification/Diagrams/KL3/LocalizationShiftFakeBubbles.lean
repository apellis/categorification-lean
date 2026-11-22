/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftBubbles
import Categorification.Diagrams.KL3.Grassmannian
import Categorification.Diagrams.KL3.SymmetryPsi

/-!
# Fake bubbles under the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. The weight shift `shiftFree RD k δ a b` induces a ring homomorphism
`shiftEnd` from the endomorphisms of the empty word at weight `μ` in the free diagram
category to those at weight `μ + δ` in `U′`. Under Webster's hypothesis
`a i - b i = -⟨αᵢ^∨, δ⟩` it sends the clockwise bubble with label `m`, real or fake
(`cwL`), to the image of the bubble `cwU` with label `m + ⟨αᵢ^∨, δ⟩` at weight `μ + δ`
(`shiftEnd_cwL`), and the counterclockwise bubble with label `m` to the one with label
`m - ⟨αᵢ^∨, δ⟩` (`shiftEnd_ccwL`). Fake bubbles are defined by the infinite Grassmannian
relation; the proof expresses the bubbles of `U` in every degree through the same inverse
series (`cwU_eq_grassInv`, `ccwU_eq_grassInv`).
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v

/-- The Grassmannian recursion computes the inverse series, in any ring. -/
theorem grassInv_eq_of_ring {A : Type*} [Ring A] (c ψ : ℕ → A) (hc : c 0 = 1)
    (h : ∀ N, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, c p.1 * ψ p.2 =
      if N = 0 then 1 else 0) :
    ∀ k, grassInv c k = ψ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · have h0 := h 0
      simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, hc, one_mul] at h0
      rw [grassInv_zero, h0, ite_eq_left trivial]
    · have hk := h (k + 1)
      rw [Finset.Nat.sum_antidiagonal_succ, hc, one_mul, ite_eq_right (Nat.succ_ne_zero k)] at hk
      dsimp only at hk
      rw [grassInv_succ, eq_neg_of_add_eq_zero_left hk, neg_inj,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range
          (fun a => c (a + 1) * ψ (k - a))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ih _ (by omega)]

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- The clockwise bubbles of `U` are the inverse series of the counterclockwise ones, in every
degree. -/
theorem cwU_eq_grassInv (ρ : X) (i : I) (d : ℕ) :
    cwU RD k ρ i (ip RD i ρ - 1 + d) =
      grassInv (fun a => ccwU RD k ρ i (-ip RD i ρ - 1 + a)) d := by
  refine (grassInv_eq_of_ring _ (fun b => cwU RD k ρ i (ip RD i ρ - 1 + b)) ?_ ?_ d).symm
  · simpa using ccwU_deg0 RD k ρ i
  · intro N
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rcases N with _ | N
    · simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, add_zero, Nat.sub_zero,
        ↓reduceIte]
      rw [cwU_deg0, ccwU_deg0]; exact Category.id_comp _
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]
      have := grassmannian RD k ρ i (N + 1) (by omega)
      rw [← this]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj := Finset.mem_range.1 hj
      show cwU RD k ρ i _ ≫ ccwU RD k ρ i _ = _
      rw [endEmpty_comm]
      congr 2
      push_cast [show j ≤ N + 1 by omega]
      ring

/-- The counterclockwise bubbles of `U` are the inverse series of the clockwise ones, in every
degree. -/
theorem ccwU_eq_grassInv (ρ : X) (i : I) (d : ℕ) :
    ccwU RD k ρ i (-ip RD i ρ - 1 + d) =
      grassInv (fun a => cwU RD k ρ i (ip RD i ρ - 1 + a)) d := by
  refine (grassInv_eq_of_ring _ (fun b => ccwU RD k ρ i (-ip RD i ρ - 1 + b)) ?_ ?_ d).symm
  · simpa using cwU_deg0 RD k ρ i
  · intro N
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rcases N with _ | N
    · simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, add_zero, Nat.sub_zero,
        ↓reduceIte]
      rw [cwU_deg0, ccwU_deg0]; exact Category.id_comp _
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]
      have := grassmannian RD k ρ i (N + 1) (by omega)
      rw [← Finset.sum_range_reflect] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj := Finset.mem_range.1 hj
      show ccwU RD k ρ i _ ≫ cwU RD k ρ i _ = _
      congr 2
      · push_cast [show j ≤ N + 1 by omega]
        ring

/-- `grassInv` only depends on the coefficients of positive index. -/
theorem grassInv_congr_of_ring {A : Type*} [Ring A] (c c' : ℕ → A)
    (h : ∀ a, c (a + 1) = c' (a + 1)) : ∀ n, grassInv c n = grassInv c' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [grassInv_zero, grassInv_zero]
    · rw [grassInv_succ, grassInv_succ]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [h, ih _ (by omega)]

/-- An additive functor on endomorphisms, as a ring homomorphism. -/
def funEnd {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] [Preadditive 𝒞] [Preadditive 𝒟]
    (F : 𝒞 ⥤ 𝒟) [F.Additive] (x : 𝒞) : End x →+* End (F.obj x) where
  toFun f := F.map f
  map_one' := F.map_id x
  map_mul' f g := F.map_comp g f
  map_zero' := F.map_zero x x
  map_add' _ _ := F.map_add

/-- Conjugation by `eqToHom` on endomorphisms, as a ring homomorphism. -/
def endConj {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {x y : 𝒞} (h : x = y) :
    End x →+* End y := by
  subst h; exact RingHom.id _

theorem endConj_apply {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {x y : 𝒞} (h : x = y)
    (f : End x) : endConj h f = eqToHom h.symm ≫ f ≫ eqToHom h := by
  subst h; simp [endConj]

/-- The localization functor on endomorphisms of `1_ν`, as a ring homomorphism. -/
abbrev toLocEnd (ν : X) : End ((pres RD k).obj (ob RD ν [])) →+* End (lob RD k ν []) :=
  funEnd (toLoc RD k) _

variable (δ : X) (a b : I → ℤ)

/-- The weight shift on diagrams of `U`. -/
abbrev shiftU : Obj (psig RD) ⥤ (presLoc RD k).Presented :=
  (incl RD).toLayerMap.functor ⋙ shiftFree RD k δ a b

theorem freeLift_shiftFree_inclLin {s t : Obj (psig RD)} (f : LinDiagram k s t) :
    (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k f) =
      (freeLift k (shiftU RD k δ a b)).map f :=
  freeLift_map_mapDomain (F := shiftU RD k δ a b) (G := shiftFree RD k δ a b)
    (incl RD).toLayerMap.map LinearMap.id (fun _ => rfl) f

/-- The weight shift on endomorphisms of `1_μ`, as a ring homomorphism. -/
def shiftEnd (μ : X) : LEnd RD k (ob RD μ []) →+* End (lob RD k (μ + δ) []) :=
  (endConj (x := (freeLift k (shiftU RD k δ a b)).obj (Free.of k (ob RD μ [])))
    (shiftFree_obj_ob RD k δ a b μ [])).comp (funEnd (freeLift k (shiftU RD k δ a b)) _)

theorem shiftEnd_apply (μ : X) (f : LEnd RD k (ob RD μ [])) :
    shiftEnd RD k δ a b μ f = eqToHom (shiftFree_obj_ob RD k δ a b μ []).symm ≫
      (freeLift k (shiftFree RD k δ a b)).map (inclLin RD k f) ≫
        eqToHom (shiftFree_obj_ob RD k δ a b μ []) := by
  rw [freeLift_shiftFree_inclLin, shiftEnd, RingHom.comp_apply, endConj_apply]; rfl

theorem shiftEnd_cwReal (μ : X) (i : I) (α : ℕ) :
    shiftEnd RD k δ a b μ (LinDiagram.of (cwReal RD μ i α)) =
      zcw (μ + δ) i (b i + (α + -a i)) := by
  rw [shiftEnd_apply, inclLin_of, freeLift_map_of]
  show _ ≫ (shiftFree RD k δ a b).map (inclD RD (mkD RD μ (cwLs i α) (sChain_cwLs i α))) ≫ _ = _
  rw [shiftFree_map_mkD, imgList_eq_zg, zg_img_cw]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  erw [Category.comp_id]

theorem shiftEnd_ccwReal (μ : X) (i : I) (α : ℕ) :
    shiftEnd RD k δ a b μ (LinDiagram.of (ccwReal RD μ i α)) =
      zccw (μ + δ) i (α + (a i + -b i)) := by
  rw [shiftEnd_apply, inclLin_of, freeLift_map_of]
  show _ ≫ (shiftFree RD k δ a b).map (inclD RD (mkD RD μ (ccwLs i α) (sChain_ccwLs i α))) ≫
    _ = _
  rw [shiftFree_map_mkD, imgList_eq_zg, zg_img_ccw]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp]
  erw [Category.comp_id]

theorem shiftEnd_cwR (hab : ∀ i, a i - b i = -ip RD i δ) (μ : X) (i : I) (m : ℤ)
    (hm : 0 ≤ m) :
    shiftEnd RD k δ a b μ (cwR RD k μ i m) =
      (toLoc RD k).map (cwU RD k (μ + δ) i (m + ip RD i δ)) := by
  rw [cwR, ite_eq_left hm, shiftEnd_cwReal, ← zcw_eq]
  congr 1
  have := hab i
  omega

theorem shiftEnd_ccwR (hab : ∀ i, a i - b i = -ip RD i δ) (μ : X) (i : I) (m : ℤ)
    (hm : 0 ≤ m) :
    shiftEnd RD k δ a b μ (ccwR RD k μ i m) =
      (toLoc RD k).map (ccwU RD k (μ + δ) i (m - ip RD i δ)) := by
  rw [ccwR, ite_eq_left hm, shiftEnd_ccwReal, ← zccw_eq]
  congr 1
  have := hab i
  omega

/-- **The weight shift on clockwise bubbles**, real or fake: under Webster's hypothesis the
bubble with label `m` in the region `μ` goes to the bubble with label `m + ⟨αᵢ^∨, δ⟩` in the
region `μ + δ`. -/
theorem shiftEnd_cwL (hab : ∀ i, a i - b i = -ip RD i δ) (μ : X) (i : I) (m : ℤ) :
    shiftEnd RD k δ a b μ (cwL RD k μ i m) =
      (toLoc RD k).map (cwU RD k (μ + δ) i (m + ip RD i δ)) := by
  have hip := ip_add_shift RD δ i μ
  by_cases hm : 0 ≤ m
  · rw [show cwL RD k μ i m = cwR RD k μ i m by rw [cwL, cwR, ite_eq_left hm, ite_eq_left hm]]
    exact shiftEnd_cwR RD k δ a b hab μ i m hm
  by_cases hd : 0 ≤ m + 1 - ip RD i μ
  · rw [cwL, ite_eq_right hm, ite_eq_left hd, map_grassInv]
    have e : m + ip RD i δ = ip RD i (μ + δ) - 1 + ((m + 1 - ip RD i μ).toNat : ℕ) := by omega
    rw [e, cwU_eq_grassInv]
    change _ = toLocEnd RD k (μ + δ) _
    rw [map_grassInv]
    refine grassInv_congr_of_ring _ _ (fun a' => ?_) _
    rw [shiftEnd_ccwR RD k δ a b hab μ i _ (by omega)]
    rw [show -ip RD i μ - 1 + ((a' + 1 : ℕ) : ℤ) - ip RD i δ =
      -ip RD i (μ + δ) - 1 + ((a' + 1 : ℕ) : ℤ) by omega]
    rfl
  · rw [cwL, ite_eq_right hm, ite_eq_right hd, map_zero, cwU_eq_zero RD k _ i _ (by omega),
      CategoryTheory.Functor.map_zero]

/-- **The weight shift on counterclockwise bubbles**, real or fake: the label `m` goes to
`m - ⟨αᵢ^∨, δ⟩`. -/
theorem shiftEnd_ccwL (hab : ∀ i, a i - b i = -ip RD i δ) (μ : X) (i : I) (m : ℤ) :
    shiftEnd RD k δ a b μ (ccwL RD k μ i m) =
      (toLoc RD k).map (ccwU RD k (μ + δ) i (m - ip RD i δ)) := by
  have hip := ip_add_shift RD δ i μ
  by_cases hm : 0 ≤ m
  · rw [show ccwL RD k μ i m = ccwR RD k μ i m by rw [ccwL, ccwR, ite_eq_left hm, ite_eq_left hm]]
    exact shiftEnd_ccwR RD k δ a b hab μ i m hm
  by_cases hd : 0 ≤ m + 1 + ip RD i μ
  · rw [ccwL, ite_eq_right hm, ite_eq_left hd, map_grassInv]
    have e : m - ip RD i δ = -ip RD i (μ + δ) - 1 + ((m + 1 + ip RD i μ).toNat : ℕ) := by omega
    rw [e, ccwU_eq_grassInv]
    change _ = toLocEnd RD k (μ + δ) _
    rw [map_grassInv]
    refine grassInv_congr_of_ring _ _ (fun a' => ?_) _
    rw [shiftEnd_cwR RD k δ a b hab μ i _ (by omega)]
    rw [show ip RD i μ - 1 + ((a' + 1 : ℕ) : ℤ) + ip RD i δ =
      ip RD i (μ + δ) - 1 + ((a' + 1 : ℕ) : ℤ) by omega]
    rfl
  · rw [ccwL, ite_eq_right hm, ite_eq_right hd, map_zero, ccwU_eq_zero RD k _ i _ (by omega),
      CategoryTheory.Functor.map_zero]

end Categorification.KL3.Diagram
