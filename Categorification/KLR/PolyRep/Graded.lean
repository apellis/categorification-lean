/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.PolyRep.Sound
import Categorification.KLR.Grading

/-!
# The polynomial representation is graded

The polynomial representation `Pol_ν = ⊕_i Pol_i` of KL I (arXiv:0803.4121v2, §2.3; see
`PolyRep.polyRep`) is graded: give the variable `x_a` of `Pol_i` the degree of a dot on an
`i_a`-strand. The action of `R(ν)` on `Pol_ν` respects the gradings, provided the polynomials
`P a b` defining the action of the crossings are homogeneous of the degree of the corresponding
crossing. This is used in the proof of Webster, arXiv:1603.06311v3, Lemma `lem:gamma-homo`
(label), to pass to graded completions.

For a grading datum `G` of `Q` the weight of the variable `X a` in the component `Pol_i` is
`G.degX (i.lbl a)`. The crossing `ψ_j e_i` with bottom labels `a = i_j`, `b = i_{j+1}` sends
`f ∈ Pol_i` to `P a b (x_j, x_{j+1}) · s_j f ∈ Pol_{s_j i}`; in the component `s_j i` the
variables `x_j`, `x_{j+1}` carry the weights `degX b`, `degX a`. Hence the hypothesis is

  `hPdeg : ∀ a b, a ≠ b → (P a b).IsWeightedHomogeneous ![G.degX b, G.degX a] (G.degΨ a b)`,

which is compatible with the homogeneity of `Q a b = P b a (u, v) · P a b (v, u)` required by
`GradingDatum` (of degree `degΨ b a + degΨ a b` for the weights `(degX a, degX b)`).

## Main definitions and results

* `PolyRep.homGrade G ν e` : the polynomials of `Pol_ν` homogeneous of degree `e`;
* `PolyRep.homPart G e` : the projection onto the degree `e` part; `PolyRep.sum_homPart`;
* `PolyRep.opGrade G ν d` : the operators on `Pol_ν` of degree `d`;
* `PolyRep.polyRep_mem_opGrade` : an element of `R(ν)` of degree `d` acts by an operator of
  degree `d`; `PolyRep.polyRep_mem_homGrade`.
-/

namespace Categorification

open MvPolynomial

/-- Renaming variables preserves weighted homogeneity when the weights are transported. -/
theorem isWeightedHomogeneous_rename {V W : Type*} {k : Type*} [CommSemiring k] {w : V → ℤ}
    {w' : W → ℤ} (σ : V → W) (hσ : ∀ v, w' (σ v) = w v) {p : MvPolynomial V k} {d : ℤ}
    (hp : p.IsWeightedHomogeneous w d) : (rename σ p).IsWeightedHomogeneous w' d := by
  rw [p.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun u hu => ?_
  rw [rename_monomial]
  refine isWeightedHomogeneous_monomial _ _ _ ?_
  rw [← hp (mem_support_iff.1 hu), Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (by simp) (fun _ _ _ => add_smul _ _ _)]
  exact Finsupp.sum_congr fun v _ => by rw [hσ]

section ddiff

variable {σ : Type*} [DecidableEq σ] {k : Type*} [CommRing k] {w : σ → ℤ} {a b : σ}

omit [DecidableEq σ] in
theorem isWeightedHomogeneous_X_pow_mul_X_pow (hw : w a = w b) (p q : ℕ) :
    (X a ^ p * X b ^ q : MvPolynomial σ k).IsWeightedHomogeneous w ((p + q : ℕ) * w a) := by
  convert ((isWeightedHomogeneous_X k w a).pow p).mul ((isWeightedHomogeneous_X k w b).pow q)
    using 1
  rw [hw]; push_cast; simp only [nsmul_eq_mul]; ring

/-- The divided difference of a monomial lowers the weighted degree by `w a = w b`. -/
theorem isWeightedHomogeneous_ddiffMonomial (hab : a ≠ b) (hw : w a = w b) (s : σ →₀ ℕ) :
    (ddiffMonomial a b s : MvPolynomial σ k).IsWeightedHomogeneous w
      (Finsupp.weight w s - w a) := by
  have hs : Finsupp.weight w s =
      Finsupp.weight w ((s.erase a).erase b) + (s a + s b : ℕ) * w a := by
    conv_lhs => rw [← erase_add_single hab s]
    simp only [map_add, Finsupp.weight_single, nsmul_eq_mul, hw]
    push_cast; ring
  have hr := isWeightedHomogeneous_monomial (R := k) w ((s.erase a).erase b) 1 rfl
  have key : ∀ p q : ℕ, q < p →
      ((monomial ((s.erase a).erase b) 1 : MvPolynomial σ k) *
        ∑ t ∈ Finset.range (p - q), X a ^ (q + t) * X b ^ (p - 1 - t)).IsWeightedHomogeneous w
        (Finsupp.weight w ((s.erase a).erase b) + ((p + q - 1 : ℕ) : ℤ) * w a) := by
    intro p q hqp
    refine hr.mul (IsWeightedHomogeneous.sum _ _ _ fun t ht => ?_)
    have := isWeightedHomogeneous_X_pow_mul_X_pow (k := k) hw (q + t) (p - 1 - t)
    rwa [show q + t + (p - 1 - t) = p + q - 1 by have := Finset.mem_range.1 ht; omega] at this
  unfold ddiffMonomial
  split_ifs with h
  · rcases Nat.eq_or_lt_of_le h with heq | hlt
    · simp only [heq, Nat.sub_self, Finset.range_zero, Finset.sum_empty, mul_zero]
      exact isWeightedHomogeneous_zero _ _ _
    · convert key (s a) (s b) hlt using 1
      rw [hs, Nat.cast_sub (by omega)]; push_cast; ring
  · convert (key (s b) (s a) (by omega)).neg using 1
    rw [hs, Nat.cast_sub (by omega)]; push_cast; ring

/-- The divided difference `∂_{ab}` lowers the weighted degree by `w a`, if `w a = w b`. -/
theorem isWeightedHomogeneous_ddiff (hab : a ≠ b) (hw : w a = w b) {f : MvPolynomial σ k}
    {e : ℤ} (hf : f.IsWeightedHomogeneous w e) :
    (Categorification.ddiff a b f).IsWeightedHomogeneous w (e - w a) := by
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s hs => ?_
  rw [← mul_one (f.coeff s), ← smul_eq_mul, ← smul_monomial, map_smul, ddiff_monomial_one,
    smul_eq_C_mul, ← hf (mem_support_iff.1 hs)]
  exact (isWeightedHomogeneous_ddiffMonomial hab hw s).C_mul _

end ddiff

end Categorification

namespace Categorification.KLR.PolyRep

open MvPolynomial TypeA Equiv KLRAlgebra

variable {I : Type*} {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} (G : GradingDatum Q) {ν : Multiset I}

local notation "m" => Multiset.card ν

/-! ### Homogeneous elements of `Pol_ν` -/

/-- The weights of the variables of the component `Pol_i`: `x_a` has the degree of a dot on an
`i_a`-strand. -/
def wt (i : Seq ν) : Fin m → ℤ := fun a => G.degX (i.lbl a)

variable (ν) in
/-- The polynomials in `Pol_ν` that are homogeneous of degree `e`. -/
def homGrade (e : ℤ) : Submodule k (Pol k ν) where
  carrier := {f | ∀ i, (f i).IsWeightedHomogeneous (wt G i) e}
  zero_mem' i := isWeightedHomogeneous_zero _ _ _
  add_mem' hf hg i := (hf i).add (hg i)
  smul_mem' c f hf i := by
    simpa only [Pi.smul_apply, smul_eq_C_mul] using (hf i).C_mul c

theorem mem_homGrade {e : ℤ} {f : Pol k ν} :
    f ∈ homGrade G ν e ↔ ∀ i, (f i).IsWeightedHomogeneous (wt G i) e := Iff.rfl

/-- The degree `e` part of an element of `Pol_ν`, componentwise. -/
noncomputable def homPart (e : ℤ) : Pol k ν →ₗ[k] Pol k ν :=
  LinearMap.pi fun i => (weightedHomogeneousComponent (wt G i) e).comp (LinearMap.proj i)

@[simp] theorem homPart_apply (e : ℤ) (f : Pol k ν) (i : Seq ν) :
    homPart G e f i = weightedHomogeneousComponent (wt G i) e (f i) := rfl

theorem homPart_mem (e : ℤ) (f : Pol k ν) : homPart G e f ∈ homGrade G ν e := fun _ =>
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem homPart_of_mem {e e' : ℤ} {f : Pol k ν} (hf : f ∈ homGrade G ν e) :
    homPart G e' f = if e' = e then f else 0 := by
  funext i
  rw [homPart_apply, weightedHomogeneousComponent_of_mem (hf i)]
  split_ifs <;> rfl

/-- The (finite) set of degrees in which `f` has a nonzero component. -/
noncomputable def degrees (f : Pol k ν) : Finset ℤ :=
  Finset.univ.biUnion fun i => (f i).support.image (Finsupp.weight (wt G i))

theorem homPart_eq_zero_of_notMem {e : ℤ} {f : Pol k ν} (he : e ∉ degrees G f) :
    homPart G e f = 0 := by
  funext i
  rw [homPart_apply]
  refine weightedHomogeneousComponent_eq_zero' _ _ fun s hs => ?_
  intro h
  exact he (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image.2 ⟨s, hs, h⟩⟩)

/-- `f` is the sum of its homogeneous components, over any finite set of degrees containing
all degrees in which `f` is nonzero. -/
theorem sum_homPart {f : Pol k ν} {S : Finset ℤ} (hS : ∀ e ∉ S, homPart G e f = 0) :
    ∑ e ∈ S, homPart G e f = f := by
  classical
  funext i
  ext s
  rw [Finset.sum_apply, coeff_sum]
  simp only [homPart_apply, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have := congrArg (fun g : Pol k ν => (g i).coeff s) (hS _ h)
    simp only [homPart_apply, coeff_weightedHomogeneousComponent] at this
    exact this.symm

theorem sum_homPart_degrees (f : Pol k ν) : ∑ e ∈ degrees G f, homPart G e f = f :=
  sum_homPart G fun _ he => homPart_eq_zero_of_notMem G he

/-! ### Operators of degree `d` -/

variable (ν) in
/-- The operators on `Pol_ν` of degree `d`: those mapping degree `e` to degree `d + e`. -/
def opGrade (d : ℤ) : Submodule k (Module.End k (Pol k ν)) where
  carrier := {T | ∀ e, ∀ f ∈ homGrade G ν e, T f ∈ homGrade G ν (d + e)}
  zero_mem' _ _ _ := Submodule.zero_mem _
  add_mem' hT hT' e f hf := Submodule.add_mem _ (hT e f hf) (hT' e f hf)
  smul_mem' c _ hT e f hf := Submodule.smul_mem _ c (hT e f hf)

theorem mem_opGrade {d : ℤ} {T : Module.End k (Pol k ν)} :
    T ∈ opGrade G ν d ↔ ∀ e, ∀ f ∈ homGrade G ν e, T f ∈ homGrade G ν (d + e) := Iff.rfl

theorem mul_mem_opGrade {d d' : ℤ} {T T' : Module.End k (Pol k ν)} (hT : T ∈ opGrade G ν d)
    (hT' : T' ∈ opGrade G ν d') : T * T' ∈ opGrade G ν (d + d') := fun e f hf => by
  rw [add_assoc]; exact hT _ _ (hT' e f hf)

theorem one_mem_opGrade : (1 : Module.End k (Pol k ν)) ∈ opGrade G ν 0 := fun e f hf => by
  rwa [zero_add]

variable [DecidableEq I]

theorem opE_mem_opGrade (i : Seq ν) : (opE i : Module.End k (Pol k ν)) ∈ opGrade G ν 0 :=
  fun e f hf t => by
    rw [zero_add, opE_apply]
    split_ifs with h
    · subst h; exact hf t
    · exact isWeightedHomogeneous_zero _ _ _

theorem opX_mul_opE_mem_opGrade (a : Fin m) (i : Seq ν) :
    (opX a * opE i : Module.End k (Pol k ν)) ∈ opGrade G ν (G.degX (i.lbl a)) :=
  fun e f hf t => by
    rw [Module.End.mul_apply, opX_apply, opE_apply]
    split_ifs with h
    · subst h; exact (isWeightedHomogeneous_X k (wt G t) a).mul (hf t)
    · rw [mul_zero]; exact isWeightedHomogeneous_zero _ _ _

variable {P : I → I → MvPolynomial (Fin 2) k}
  (hPdeg : ∀ a b, a ≠ b → (P a b).IsWeightedHomogeneous ![G.degX b, G.degX a] (G.degΨ a b))

include hPdeg in
theorem opΨ_mul_opE_mem_opGrade (j : ℕ) (i : Seq ν) :
    (opΨ P j * opE i : Module.End k (Pol k ν)) ∈ opGrade G ν (G.dψ j i) := by
  by_cases h : j + 1 < m
  swap
  · rw [opΨ_eq_zero P (by omega), zero_mul]; exact Submodule.zero_mem _
  intro e f hf t
  set p : Fin m := ⟨j, by omega⟩
  set q : Fin m := ⟨j + 1, h⟩
  have hpq : p ≠ q := fun h' => by simpa [p, q] using congrArg Fin.val h'
  rw [Module.End.mul_apply, opΨ_apply_of_eq P (p := p) (q := q) rfl rfl, opE_apply,
    G.dψ_of_lt h]
  split_ifs with ht
  swap
  · rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  have ht' : t = swap p q • i := by rw [← ht, swap_smul_swap_smul]
  subst ht'
  clear ht
  have hwt : ∀ c, wt G (swap p q • i) c = wt G i (swap p q c) := fun c => by
    simp only [wt, Seq.lbl, swap_smul_apply]
  rw [swap_smul_apply, swap_smul_apply, swap_apply_left, swap_apply_right]
  change (crossOp P (i.lbl p) (i.lbl q) p q (f i)).IsWeightedHomogeneous _ _
  by_cases hab : i.lbl p = i.lbl q
  · rw [hab, crossOp_self, G.degΨ_self]
    have hsi : swap p q • i = i := swap_smul_eq_self hab
    rw [hsi]
    have := isWeightedHomogeneous_ddiff (k := k) (w := wt G i) hpq
      (by simp only [wt, hab]) (hf i)
    convert this using 1
    simp only [wt, hab]; ring
  · rw [crossOp_of_ne P hab]
    refine (isWeightedHomogeneous_rename _ (fun v => ?_) (hPdeg _ _ hab)).mul
      (isWeightedHomogeneous_rename _ (fun c => ?_) (hf i))
    · fin_cases v
      · simp [wt]
      · simp [wt]
    · rw [hwt, swap_apply_self]

/-! ### The action of `R(ν)` respects the gradings -/

variable (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))

/-- An element of `R(ν)[ℤ]` whose coefficient of degree `d` acts by an operator of degree `d`,
for every `d`. -/
def IsGradedImage (φ : AddMonoidAlgebra (KLRAlgebra k Q ν) ℤ) : Prop :=
  ∀ d, polyRep hPQ (φ.coeff d) ∈ opGrade G ν d

theorem isGradedImage_single {d₀ : ℤ} {c : KLRAlgebra k Q ν}
    (hc : polyRep hPQ c ∈ opGrade G ν d₀) :
    IsGradedImage (G := G) hPQ (AddMonoidAlgebra.single d₀ c) :=
  fun d => by
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · exact h ▸ hc
    · rw [map_zero]; exact Submodule.zero_mem _

theorem isGradedImage_add {φ ψ : AddMonoidAlgebra (KLRAlgebra k Q ν) ℤ}
    (hφ : IsGradedImage (G := G) hPQ φ) (hψ : IsGradedImage (G := G) hPQ ψ) :
    IsGradedImage (G := G) hPQ (φ + ψ) := fun d => by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
  exact Submodule.add_mem _ (hφ d) (hψ d)

theorem isGradedImage_sum {ι : Type*} (s : Finset ι)
    {φ : ι → AddMonoidAlgebra (KLRAlgebra k Q ν) ℤ}
    (hφ : ∀ i ∈ s, IsGradedImage (G := G) hPQ (φ i)) :
    IsGradedImage (G := G) hPQ (∑ i ∈ s, φ i) := fun d => by
  rw [AddMonoidAlgebra.coeff_sum, Finset.sum_apply', map_sum]
  exact Submodule.sum_mem _ fun i hi => hφ i hi d

theorem isGradedImage_mul {φ ψ : AddMonoidAlgebra (KLRAlgebra k Q ν) ℤ}
    (hφ : IsGradedImage (G := G) hPQ φ) (hψ : IsGradedImage (G := G) hPQ ψ) :
    IsGradedImage (G := G) hPQ (φ * ψ) := fun d => by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  simp only [Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun d₁ _ => Submodule.sum_mem _ fun d₂ _ => ?_
  split_ifs with h
  · rw [map_mul, ← h]; exact mul_mem_opGrade G (hφ d₁) (hψ d₂)
  · rw [map_zero]; exact Submodule.zero_mem _

theorem isGradedImage_algebraMap (r : k) :
    IsGradedImage (G := G) hPQ (algebraMap k (AddMonoidAlgebra (KLRAlgebra k Q ν) ℤ) r) := by
  rw [Algebra.algebraMap_eq_smul_one, AddMonoidAlgebra.one_def, AddMonoidAlgebra.smul_single]
  refine isGradedImage_single G hPQ ?_
  rw [map_smul, map_one]; exact Submodule.smul_mem _ r (one_mem_opGrade G)

include hPdeg in
/-- The coefficient of degree `d` of the coaction acts by an operator of degree `d`. -/
theorem isGradedImage_coaction (a : KLRAlgebra k Q ν) :
    IsGradedImage (G := G) hPQ (G.coaction a) := by
  obtain ⟨u, rfl⟩ := mk_surjective a
  induction u using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes, AlgHom.commutes]; exact isGradedImage_algebraMap G hPQ r
  | grade1 g =>
    cases g with
    | idem i =>
      rw [show KLRAlgebra.mk k Q ν (FreeAlgebra.ι k (Gen.idem i)) = e i from rfl,
        GradingDatum.coaction_e]
      exact isGradedImage_single G hPQ (by rw [polyRep_e]; exact opE_mem_opGrade G i)
    | dot a =>
      rw [show KLRAlgebra.mk k Q ν (FreeAlgebra.ι k (Gen.dot a)) = x a from rfl,
        GradingDatum.coaction_x]
      refine isGradedImage_sum G hPQ _ fun i _ => isGradedImage_single G hPQ ?_
      rw [map_mul, polyRep_x, polyRep_e]; exact opX_mul_opE_mem_opGrade G a i
    | cross j =>
      rw [show KLRAlgebra.mk k Q ν (FreeAlgebra.ι k (Gen.cross j)) = ψ j from rfl,
        GradingDatum.coaction_ψ]
      refine isGradedImage_sum G hPQ _ fun i _ => isGradedImage_single G hPQ ?_
      rw [map_mul, polyRep_ψ, polyRep_e]; exact opΨ_mul_opE_mem_opGrade G hPdeg j i
  | mul u v hu hv => rw [map_mul, map_mul]; exact isGradedImage_mul G hPQ hu hv
  | add u v hu hv => rw [map_add, map_add]; exact isGradedImage_add G hPQ hu hv

include hPdeg in
/-- The polynomial representation (KL I §2.3) is graded: an element of `R(ν)` of degree `d`
acts on `Pol_ν` by an operator of degree `d`. -/
theorem polyRep_mem_opGrade {a : KLRAlgebra k Q ν} {d : ℤ} (ha : a ∈ G.grade ν d) :
    polyRep hPQ a ∈ opGrade G ν d := by
  have := isGradedImage_coaction G hPdeg hPQ a d
  rwa [G.mem_grade.1 ha, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at this

include hPdeg in
/-- The polynomial representation (KL I §2.3) is graded: an element of degree `d` maps
polynomials of degree `e` to polynomials of degree `d + e`. -/
theorem polyRep_mem_homGrade {a : KLRAlgebra k Q ν} {d e : ℤ} (ha : a ∈ G.grade ν d)
    {f : Pol k ν} (hf : f ∈ homGrade G ν e) : polyRep hPQ a f ∈ homGrade G ν (d + e) :=
  polyRep_mem_opGrade G hPdeg hPQ ha e f hf

end Categorification.KLR.PolyRep
