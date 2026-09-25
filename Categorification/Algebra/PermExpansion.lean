/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Expansions of operators on polynomials in the skew group ring

Let `k` be an integral domain, `R = k[x_0, …, x_{n-1}]` and `K = Frac R`. The symmetric
group `S_n` acts on `R` by `rename` and hence on `K` by field automorphisms `act k w`.
A map `T : R → R` has *expansion* `g : S_n → K` if

  `T f = ∑_w g w · w(f)` in `K`, for all `f ∈ R`,

i.e. `T` is the restriction of the element `∑_w g w · w` of the skew group ring `K ⋊ S_n`.
Multiplication operators, `rename`, and divided differences have expansions; expansions
compose by the skew convolution `conv`, and are unique by Dedekind's independence of
characters. This is the tool used to prove linear independence of the operators in
the polynomial representation of KLR algebras (KL I, arXiv:0803.4121v2, Thm 2.5).

## Main definitions

* `PermExpansion.act k w` : the automorphism of `K` induced by `rename w`.
* `PermExpansion.HasExp T g` : `T` has expansion `g`.
* `PermExpansion.conv g g'` : skew convolution, the expansion of a composite.

## Main results

* `PermExpansion.HasExp.comp` : expansions of composites.
* `PermExpansion.HasExp.unique` : expansions are unique.
* `PermExpansion.hasExp_rename`, `hasExp_mul_rename`, `hasExp_ddiffLike`, `HasExp.mulLeft`,
  `HasExp.comp_mul` : basic expansions.
-/

namespace Categorification.PermExpansion

open MvPolynomial Equiv

variable {n : ℕ} {k : Type*} [CommRing k]

local notation "R" => MvPolynomial (Fin n) k
local notation "K" => FractionRing (MvPolynomial (Fin n) k)

variable (k) in
/-- The field automorphism of `Frac k[x]` induced by `rename w`. -/
noncomputable def act (w : Perm (Fin n)) : K ≃+* K :=
  IsFractionRing.ringEquivOfRingEquiv (renameEquiv k w).toRingEquiv

@[simp] theorem act_algebraMap (w : Perm (Fin n)) (f : R) :
    act k w (algebraMap R K f) = algebraMap R K (rename w f) := by
  simp [act]

theorem act_mul (u v : Perm (Fin n)) (x : K) : act k (u * v) x = act k u (act k v x) := by
  let φ : K →+* K := (act k u : K →+* K).comp (act k v : K →+* K)
  have : (act k (u * v) : K →+* K) = φ :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun f => by
      simp [φ, rename_rename, Perm.coe_mul])
  exact DFunLike.congr_fun this x

@[simp] theorem act_one (x : K) : act k (1 : Perm (Fin n)) x = x := by
  have : (act k (1 : Perm (Fin n)) : K →+* K) = RingHom.id K :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun f => by simp)
  exact DFunLike.congr_fun this x

theorem act_sum {ι : Type*} (w : Perm (Fin n)) (s : Finset ι) (f : ι → K) :
    act k w (∑ i ∈ s, f i) = ∑ i ∈ s, act k w (f i) :=
  map_sum (act k w) f s

theorem act_eq_zero {w : Perm (Fin n)} {x : K} (h : act k w x = 0) : x = 0 :=
  (map_eq_zero_iff _ (act k w).injective).mp h

theorem act_ne_zero (w : Perm (Fin n)) {x : K} (hx : x ≠ 0) : act k w x ≠ 0 :=
  (map_ne_zero_iff _ (act k w).injective).mpr hx

theorem algebraMap_ne_zero {f : R} (hf : f ≠ 0) : algebraMap R K f ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hf

/-- `T : R → R` has expansion `g : S_n → K`: `T f = ∑_w g w · w(f)` in `Frac R`. -/
def HasExp (T : R → R) (g : Perm (Fin n) → K) : Prop :=
  ∀ f, algebraMap R K (T f) = ∑ w, g w * act k w (algebraMap R K f)

/-- Skew convolution: the expansion of `T ∘ T'` from those of `T` and `T'`. -/
noncomputable def conv (g g' : Perm (Fin n) → K) (w : Perm (Fin n)) : K :=
  ∑ u, g u * act k u (g' (u⁻¹ * w))

theorem sum_single_mul (w₀ : Perm (Fin n)) (c : K) (F : Perm (Fin n) → K) :
    ∑ w, (Pi.single w₀ c : Perm (Fin n) → K) w * F w = c * F w₀ := by
  simp [Pi.single_apply]

namespace HasExp

theorem congr {T T' : R → R} {g : Perm (Fin n) → K} (h : HasExp T g) (hT : ∀ f, T' f = T f) : HasExp T' g := by
  intro f; rw [hT]; exact h f

theorem congr_exp {T : R → R} {g g' : Perm (Fin n) → K} (h : HasExp T g) (hg : g = g') : HasExp T g' := hg ▸ h

theorem zero : HasExp (fun _ => (0 : R)) 0 := by
  intro f; simp

theorem add {T T' : R → R} {g g' : Perm (Fin n) → K} (h : HasExp T g) (h' : HasExp T' g') : HasExp (fun f => T f + T' f) (g + g') := by
  intro f; simp [h f, h' f, add_mul, Finset.sum_add_distrib]

theorem sum {ι : Type*} (s : Finset ι) {T : ι → R → R} {g : ι → Perm (Fin n) → K}
    (h : ∀ i ∈ s, HasExp (T i) (g i)) :
    HasExp (fun f => ∑ i ∈ s, T i f) (fun w => ∑ i ∈ s, g i w) := by
  intro f
  rw [map_sum, Finset.sum_congr rfl fun i hi => h i hi f, Finset.sum_comm]
  simp [Finset.sum_mul]

/-- Left multiplication by a polynomial. -/
theorem mulLeft {T : R → R} {g : Perm (Fin n) → K} (p : R) (h : HasExp T g) :
    HasExp (fun f => p * T f) (fun w => algebraMap R K p * g w) := by
  intro f; simp [h f, Finset.mul_sum, mul_assoc]

/-- Scalar multiplication. -/
theorem smul {T : R → R} {g : Perm (Fin n) → K} (c : k) (h : HasExp T g) :
    HasExp (fun f => c • T f) (fun w => algebraMap R K (C c) * g w) := by
  simpa [smul_eq_C_mul] using h.mulLeft (C c)

/-- Precomposition with a multiplication operator. -/
theorem comp_mul {T : R → R} {g : Perm (Fin n) → K} (p : R) (h : HasExp T g) :
    HasExp (fun f => T (p * f)) (fun w => g w * act k w (algebraMap R K p)) := by
  intro f; simp [h (p * f), mul_assoc]

/-- Expansions compose by skew convolution. -/
theorem comp {T T' : R → R} {g g' : Perm (Fin n) → K} (h : HasExp T g) (h' : HasExp T' g') : HasExp (T ∘ T') (conv g g') := by
  intro f
  simp only [Function.comp_apply, h (T' f), h' f, map_sum, map_mul, conv, Finset.sum_mul,
    Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft u)]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, act_mul, mul_assoc]

/-- The characters `f ↦ w(f)` of the multiplicative monoid of `R` in `K`. -/
noncomputable def chi (w : Perm (Fin n)) : R →* K :=
  ((algebraMap R K).comp (rename w).toRingHom).toMonoidHom

theorem chi_injective [IsDomain k] : Function.Injective (chi (n := n) (k := k)) := by
  intro u v huv
  ext a
  have := DFunLike.congr_fun huv (X a)
  simp only [chi, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.coe_comp,
    Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X] at this
  exact congrArg Fin.val (X_injective (IsFractionRing.injective R K this))

/-- Expansions are unique (Dedekind independence of the characters `f ↦ w(f)`). -/
theorem unique [IsDomain k] {T : R → R} {g g' : Perm (Fin n) → K} (h : HasExp T g) (h' : HasExp T g') : g = g' := by
  have li := (linearIndependent_monoidHom R K).comp chi chi_injective
  have key := Fintype.linearIndependent_iff.mp li (g - g') (by
    funext f
    have e1 := h f
    have e2 := h' f
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, chi,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Pi.sub_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, Pi.zero_apply]
    simp only [act_algebraMap] at e1 e2
    rw [← e1, ← e2, sub_self])
  funext w
  exact sub_eq_zero.mp (key w)

/-- If `T` vanishes identically then its expansion vanishes. -/
theorem eq_zero_of_forall [IsDomain k] {T : R → R} {g : Perm (Fin n) → K} (h : HasExp T g) (hT : ∀ f, T f = 0) : g = 0 :=
  (h.congr fun f => (hT f).symm).unique zero

end HasExp

/-- The identity has expansion `δ_1`. -/
theorem hasExp_id : HasExp (fun f : R => f) (Pi.single 1 1) := by
  intro f; simp [sum_single_mul]

/-- `rename w` has expansion `δ_w`. -/
theorem hasExp_rename (w : Perm (Fin n)) :
    HasExp (fun f : R => rename w f) (Pi.single w 1) := by
  intro f; simp [sum_single_mul]

/-- `f ↦ p * rename w f` has expansion `p δ_w`. -/
theorem hasExp_mul_rename (p : R) (w : Perm (Fin n)) :
    HasExp (fun f : R => p * rename w f) (Pi.single w (algebraMap R K p)) := by
  intro f; simp [sum_single_mul]

/-- An operator `D` with `(X a - X b) * D f = f - rename (swap a b) f` (a divided difference)
has expansion `(X a - X b)⁻¹ (δ_1 - δ_{(a b)})`. -/
theorem hasExp_ddiffLike [IsDomain k] {a b : Fin n} (hab : a ≠ b) {D : R → R}
    (hD : ∀ f, (X a - X b) * D f = f - rename (swap a b) f) :
    HasExp D (Pi.single 1 (algebraMap R K (X a - X b))⁻¹ +
      Pi.single (swap a b) (-(algebraMap R K (X a - X b))⁻¹)) := by
  intro f
  have hne : algebraMap R K (X a - X b) ≠ 0 :=
    algebraMap_ne_zero (sub_ne_zero.mpr fun h => hab (X_injective h))
  have := congrArg (algebraMap R K) (hD f)
  rw [map_mul, map_sub _ f] at this
  have key : algebraMap R K (D f) = (algebraMap R K (X a - X b))⁻¹ *
      (algebraMap R K f - algebraMap R K (rename (swap a b) f)) := by
    rw [← this, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, sum_single_mul, act_one,
    act_algebraMap, Perm.coe_one, rename_id_apply]
  rw [key]
  ring

/-! ### Support of a convolution -/

theorem conv_ne_zero {g g' : Perm (Fin n) → K} {w : Perm (Fin n)} (h : conv g g' w ≠ 0) :
    ∃ u v, g u ≠ 0 ∧ g' v ≠ 0 ∧ u * v = w := by
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨u, u⁻¹ * w, left_ne_zero_of_mul hu, fun h0 => ?_, mul_inv_cancel_left u w⟩
  rw [h0, map_zero, mul_zero] at hu
  exact hu rfl

/-- The top coefficient of a convolution with an expansion supported on `{1, s}`. -/
theorem conv_top {g g' : Perm (Fin n) → K} {s w : Perm (Fin n)}
    (hg : ∀ u, g u ≠ 0 → u = 1 ∨ u = s) (hw : g' (s * w) = 0) :
    conv g g' (s * w) = g s * act k s (g' w) := by
  unfold conv
  rw [Finset.sum_eq_single s]
  · rw [inv_mul_cancel_left]
  · intro u _ hus
    by_cases hu : g u = 0
    · rw [hu, zero_mul]
    · rcases hg u hu with rfl | rfl
      · rw [inv_one, one_mul, hw, map_zero, mul_zero]
      · exact absurd rfl hus
  · exact fun h => absurd (Finset.mem_univ _) h

end Categorification.PermExpansion
