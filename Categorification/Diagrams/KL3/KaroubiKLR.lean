/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.Decompositions
import Categorification.Algebra.IdempotentEquiv

/-!
# Idempotents of `R(ν)` as 1-morphisms of `U̇`

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.5
(TeX label `subsec_dirsumdecs`): "Due to the existence of the homomorphism `ϕ_{ν,λ}` in the
formula (3.30) any degree `0` idempotent `e` of `R(ν)` gives rise to the idempotent `ϕ_{ν,λ}(e)`
of `E_ν 1_λ` and to the 1-morphism `(E_ν 1_λ, ϕ_{ν,λ}(e))` of `U̇`."

Here `ϕ_{ν,λ}` is `toUEnd RD k μ ν : R(ν) → END_U(E_ν 1_μ)` (`Categorification.Diagrams.KL3.Upward`,
upward strands, KL II algebra `R2 k C ν` with `Q_ij = u^{d_ij} + v^{d_ji}`), with entries
`upEnt RD k μ r s s' : E_s 1_μ ⟶ E_{s'} 1_μ` (`s, s' ∈ Seq ν`).

## Main results

* `grade_transfer`: an algebra map out of `R(ν)` which sends `e_i`, `x_a e_i`, `ψ_j e_i` into
  the corresponding degrees of a family `ℬ` of submodules closed under products sends every
  homogeneous element of degree `d` into `ℬ d` (the grading of `R(ν)` is defined by a coaction,
  so this is not formal).
* `upEnt_mem`: **`ϕ_{ν,λ}` preserves degrees** for the KL II grading `klGradingDatum2` and the
  grading `deg` of `U`.
* `kobj`: for an idempotent `f ∈ e_s R(ν) e_s` of degree `0` and a shift `t`, the object
  `(E_s 1_μ {t}, ϕ(f))` of `U̇`; `khom`: morphisms between such objects given by homogeneous
  elements `y ∈ f' R(ν) f`, with `khom_comp`, `khom_self`.
* `kIso`: **equivalent idempotents give isomorphic 1-morphisms**: if `a b = f`, `b a = f'`
  (`IsEquivPair`) with `a` of degree `d` and `b` of degree `-d`, then
  `(E_s 1_μ {t}, ϕ(f)) ≅ (E_{s'} 1_μ {t + d}, ϕ(f'))`.
* `kobj_one`: `(E_s 1_μ {t}, ϕ(1_s)) = E_s 1_μ {t}`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  Categorification.GradedBicat

/-! ## Transfer of degrees along algebra maps out of `R(ν)` -/

section Transfer

open KLR KLR.KLRAlgebra

variable {I' : Type*} [DecidableEq I'] {k' : Type*} [CommRing k']
  {Q : I' → I' → MvPolynomial (Fin 2) k'} {ν : Multiset I'} (G : KLR.GradingDatum Q)
  {B : Type*} [Ring B] [Algebra k' B] (ℬ : ℤ → Submodule k' B)

/-- **Transfer of degrees.** Let `φ : R(ν) → B` be an algebra map and `ℬ` a family of
submodules of `B` with `1 ∈ ℬ 0` and `ℬ d ℬ d' ⊆ ℬ (d + d')`. If `φ` sends `e_i`, `x_a e_i` and
`ψ_j e_i` into `ℬ` of their degrees, then it sends every element of degree `d` into `ℬ d`. -/
theorem grade_transfer (hB1 : (1 : B) ∈ ℬ 0)
    (hBmul : ∀ {d d' : ℤ} {y z : B}, y ∈ ℬ d → z ∈ ℬ d' → y * z ∈ ℬ (d + d'))
    (φ : KLRAlgebra k' Q ν →ₐ[k'] B) (he : ∀ i, φ (e i) ∈ ℬ 0)
    (hx : ∀ a i, φ (x a * e i) ∈ ℬ (G.degX (i.lbl a)))
    (hψ : ∀ j i, φ (ψ j * e i) ∈ ℬ (G.dψ j i)) {d : ℤ} {r : KLRAlgebra k' Q ν}
    (hr : r ∈ G.grade ν d) : φ r ∈ ℬ d := by
  classical
  let T : Set (KLRAlgebra k' Q ν) := {b | ∀ d', φ (GradedRing.proj (G.grade ν) d' b) ∈ ℬ d'}
  have hT0 : (0 : KLRAlgebra k' Q ν) ∈ T := fun d' => by
    rw [map_zero, map_zero]; exact zero_mem _
  have hTadd : ∀ b c, b ∈ T → c ∈ T → b + c ∈ T := fun b c hb hc d' => by
    rw [map_add, map_add]; exact add_mem (hb d') (hc d')
  have hT1 : (1 : KLRAlgebra k' Q ν) ∈ T := by
    intro d'
    rw [GradedRing.proj_apply]
    by_cases hd : d' = 0
    · subst hd
      rw [DirectSum.decompose_of_mem_same _ (SetLike.one_mem_graded _), map_one]
      exact hB1
    · rw [DirectSum.decompose_of_mem_ne _ (SetLike.one_mem_graded _) (Ne.symm hd), map_zero]
      exact zero_mem _
  have hThom : ∀ (h : KLRAlgebra k' Q ν) (d₀ : ℤ), h ∈ G.grade ν d₀ → φ h ∈ ℬ d₀ →
      ∀ b ∈ T, h * b ∈ T := by
    intro h d₀ hh hφ b hb d'
    have key := DirectSum.coe_decompose_mul_add_of_left_mem (G.grade ν) (b := b)
      (j := d' - d₀) hh
    rw [add_sub_cancel] at key
    rw [GradedRing.proj_apply, key, map_mul]
    have h2 := hBmul hφ (hb (d' - d₀))
    rwa [GradedRing.proj_apply, add_sub_cancel] at h2
  let M : Set (KLRAlgebra k' Q ν) := {a | ∀ b ∈ T, a * b ∈ T}
  have hM0 : (0 : KLRAlgebra k' Q ν) ∈ M := fun b _ => by rw [zero_mul]; exact hT0
  have hMadd : ∀ a a', a ∈ M → a' ∈ M → a + a' ∈ M := fun a a' ha ha' b hb => by
    rw [add_mul]; exact hTadd _ _ (ha b hb) (ha' b hb)
  have hMmul : ∀ a a', a ∈ M → a' ∈ M → a * a' ∈ M := fun a a' ha ha' b hb => by
    rw [mul_assoc]; exact ha _ (ha' b hb)
  have hMsum : ∀ (f : Seq ν → KLRAlgebra k' Q ν), (∀ i, f i ∈ M) → ∑ i, f i ∈ M :=
    fun f hf => Finset.sum_induction f (· ∈ M) hMadd hM0 fun i _ => hf i
  have hMalg : ∀ c : k', algebraMap k' (KLRAlgebra k' Q ν) c ∈ M := fun c =>
    hThom _ 0 (SetLike.algebraMap_mem_graded _ c) (by
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]; exact Submodule.smul_mem _ c hB1)
  have hall : ∀ u, KLRAlgebra.mk k' Q ν u ∈ M := by
    intro u
    induction u using FreeAlgebra.induction with
    | grade0 c => rw [AlgHom.commutes]; exact hMalg c
    | grade1 g =>
      cases g with
      | idem i => exact hThom _ 0 (G.e_mem_grade i) (he i)
      | dot a =>
        change x a ∈ M
        rw [← mul_one (x a), ← sum_e, Finset.mul_sum]
        exact hMsum _ fun i => hThom _ _ (G.x_mul_e_mem_grade a i) (hx a i)
      | cross j =>
        change ψ j ∈ M
        rw [← mul_one (ψ j), ← sum_e, Finset.mul_sum]
        exact hMsum _ fun i => hThom _ _ (G.ψ_mul_e_mem_grade' j i) (hψ j i)
    | mul u v hu hv => rw [map_mul]; exact hMmul _ _ hu hv
    | add u v hu hv => rw [map_add]; exact hMadd _ _ hu hv
  have hrT : r ∈ T := by
    obtain ⟨u, hu⟩ := mk_surjective (k := k') (Q := Q) (ν := ν) r
    have := hall u 1 hT1
    rwa [mul_one, hu] at this
  have := hrT d
  rwa [GradedRing.proj_apply, DirectSum.decompose_of_mem_same _ hr] at this

end Transfer

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k] [DecidableEq I]

/-! ## `ϕ_{ν,λ}` preserves degrees -/

section Degrees

open KLR KLR.KLRAlgebra KLR.Diagram

variable (μ : X) (ν : Multiset I)

/-- The 1-morphism `E_s 1_μ` of upward strands, for `s ∈ Seq ν`. -/
abbrev ZU (s : Seq ν) : (pres RD k).Presented := (pres RD k).obj (ob RD μ (ups (word s)))

/-- Matrices `(E_s 1_μ ⟶ E_{s'} 1_μ)_{s, s'}` all of whose entries have degree `d`. -/
def matDeg (d : ℤ) : Submodule k (MatEnd (ZU RD k μ ν)) where
  carrier := {f | ∀ s s', f s s' ∈ (pres RD k).homDeg (deg RD) _ _ d}
  add_mem' hf hg s s' := Submodule.add_mem _ (hf s s') (hg s s')
  zero_mem' _ _ := Submodule.zero_mem _
  smul_mem' r _ hf s s' := Submodule.smul_mem _ r (hf s s')

variable {RD k μ ν}

theorem single_mem_matDeg {s s' : Seq ν} {f : ZU RD k μ ν s ⟶ ZU RD k μ ν s'} {d : ℤ}
    (hf : f ∈ (pres RD k).homDeg (deg RD) _ _ d) : MatEnd.single s s' f ∈ matDeg RD k μ ν d := by
  intro a a'
  rw [MatEnd.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simpa using hf
  · exact Submodule.zero_mem _

theorem one_mem_matDeg : (1 : MatEnd (ZU RD k μ ν)) ∈ matDeg RD k μ ν 0 := by
  intro a a'
  rw [MatEnd.one_apply]
  split_ifs with h
  · subst h
    simpa using (pres RD k).id_mem_homDeg (deg RD) _
  · exact Submodule.zero_mem _

theorem mul_mem_matDeg {d d' : ℤ} {f g : MatEnd (ZU RD k μ ν)} (hf : f ∈ matDeg RD k μ ν d)
    (hg : g ∈ matDeg RD k μ ν d') : f * g ∈ matDeg RD k μ ν (d + d') := by
  intro a a'
  rw [MatEnd.mul_apply, add_comm]
  exact Submodule.sum_mem _ fun j _ => comp_mem_homDeg (hg a j) (hf j a')

theorem toUEnd_e_mem (i : Seq ν) : toUEnd RD k μ ν (e i) ∈ matDeg RD k μ ν 0 := by
  rw [toUEnd_e]
  exact single_mem_matDeg ((pres RD k).id_mem_homDeg (deg RD) _)

theorem toUEnd_x_e_mem (a : Fin (Multiset.card ν)) (i : Seq ν) :
    toUEnd RD k μ ν (x a * e i) ∈ matDeg RD k μ ν ((klGradingDatum2 k C).degX (i.lbl a)) := by
  rw [map_mul, toUEnd_x, toUEnd_e, Finset.sum_mul]
  refine Submodule.sum_mem _ fun t _ => ?_
  by_cases hti : t = i
  · subst hti
    rw [MatEnd.single_mul_single]
    refine single_mem_matDeg (mem_homDeg_of_eq (comp_mem_homDeg
      ((pres RD k).id_mem_homDeg (deg RD) _) ?_) (zero_add _))
    rw [dotE, upFunctor_diag]
    refine diag_mem_homDeg' ?_
    rw [degree_upDiag]
    simp [dotD, Diagram.degree, KLR.Diagram.layers_dl, KLR.Diagram.lay, degK, klGradingDatum2]
  · rw [MatEnd.single_mul_single_of_ne _ _ (Ne.symm hti)]
    exact Submodule.zero_mem _

theorem toUEnd_ψ_e_mem (j : ℕ) (i : Seq ν) :
    toUEnd RD k μ ν (ψ j * e i) ∈ matDeg RD k μ ν ((klGradingDatum2 k C).dψ j i) := by
  rw [map_mul, toUEnd_ψ, toUEnd_e, Finset.sum_mul]
  refine Submodule.sum_mem _ fun t _ => ?_
  by_cases hti : t = i
  · subst hti
    rw [MatEnd.single_mul_single]
    refine single_mem_matDeg (mem_homDeg_of_eq (comp_mem_homDeg
      ((pres RD k).id_mem_homDeg (deg RD) _) ?_) (zero_add _))
    by_cases h : j + 1 < Multiset.card ν
    · rw [crossE_def _ h, upFunctor_diag, GradingDatum.dψ_of_lt _ h]
      refine diag_mem_homDeg' ?_
      rw [degree_upDiag]
      simp [crossD, Diagram.degree, KLR.Diagram.layers_dl, KLR.Diagram.lay, degK, klGradingDatum2]
    · rw [crossE, dif_neg h, Functor.map_zero]
      exact Submodule.zero_mem _
  · rw [MatEnd.single_mul_single_of_ne _ _ (Ne.symm hti)]
    exact Submodule.zero_mem _

/-- **`ϕ_{ν,λ}` preserves degrees**: an element of degree `d` of `R(ν)` (KL II grading) is sent
to a matrix of 2-morphisms of degree `d`. -/
theorem toUEnd_mem {d : ℤ} {r : R2 k C ν} (hr : r ∈ (klGradingDatum2 k C).grade ν d) :
    toUEnd RD k μ ν r ∈ matDeg RD k μ ν d :=
  grade_transfer (klGradingDatum2 k C) (matDeg RD k μ ν) one_mem_matDeg mul_mem_matDeg
    (toUEnd RD k μ ν) toUEnd_e_mem toUEnd_x_e_mem toUEnd_ψ_e_mem hr

end Degrees

/-! ## Entries of `ϕ_{ν,λ}` -/

section Entries

open KLR KLR.KLRAlgebra KLR.Diagram

variable (μ : X) {ν : Multiset I}

/-- The entry `E_s 1_μ ⟶ E_{s'} 1_μ` of `ϕ_{ν,λ}(r)`. -/
abbrev upEnt (r : R2 k C ν) (s s' : Seq ν) : ZU RD k μ ν s ⟶ ZU RD k μ ν s' :=
  toUEnd RD k μ ν r s s'

variable {RD k μ}

theorem upEnt_mem {d : ℤ} {r : R2 k C ν} (hr : r ∈ (klGradingDatum2 k C).grade ν d)
    (s s' : Seq ν) : upEnt RD k μ r s s' ∈ (pres RD k).homDeg (deg RD) _ _ d :=
  toUEnd_mem hr s s'

theorem upEnt_e (s : Seq ν) : upEnt RD k μ (e s : R2 k C ν) s s = 𝟙 _ := by
  rw [upEnt, toUEnd_e, MatEnd.single_apply_self]

theorem upEnt_eq_zero {z : R2 k C ν} {s' : Seq ν} (hz : e s' * z = z) (s j : Seq ν) (hj : j ≠ s') :
    upEnt RD k μ z s j = 0 := by
  rw [upEnt, ← hz, map_mul, toUEnd_e, MatEnd.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [MatEnd.single_apply_of_ne _ (fun h => hj h.2), Limits.comp_zero]

theorem upEnt_mul {y z : R2 k C ν} {s' : Seq ν} (hz : e s' * z = z) (s s'' : Seq ν) :
    upEnt RD k μ (y * z) s s'' = upEnt RD k μ z s s' ≫ upEnt RD k μ y s' s'' := by
  rw [upEnt, map_mul, MatEnd.mul_apply, Finset.sum_eq_single s']
  · intro j _ hj
    have h0 := upEnt_eq_zero (RD := RD) (k := k) (μ := μ) hz s j hj
    simp only [upEnt] at h0
    rw [h0, Limits.zero_comp]
  · intro h; exact absurd (Finset.mem_univ _) h

variable (RD) in
/-- The weight `ν_X = ∑_{i ∈ ν} i_X`. -/
def wν (ν : Multiset I) : X := (ν.map RD.iX).sum

omit [DecidableEq I] in
theorem wt_ups_word (s : Seq ν) : wt RD μ (ups (word s)) = wν RD ν + μ := by
  rw [wt_ups]
  congr 1
  have h := congrArg (fun m => (Multiset.map RD.iX m).sum) s.2
  simp only at h
  rw [wν, ← h, Multiset.map_map]
  simp only [wsum, word, List.map_ofFn, List.sum_ofFn]
  rfl

end Entries

/-! ## The 1-morphisms `(E_s 1_μ {t}, ϕ(f))` -/

section KObj

open KLR KLR.KLRAlgebra KLR.Diagram

variable (μ : X) {ν : Multiset I}

variable (C) in
/-- An idempotent `f ∈ e_s R(ν) e_s` of degree `0`, for the sequence `s`. -/
structure CornerIdem (s : Seq ν) where
  /-- The idempotent. -/
  f : R2 k C ν
  deg0 : f ∈ (klGradingDatum2 k C).grade ν 0
  idem : f * f = f
  left : e s * f = f

variable {RD k μ}

theorem CornerIdem.upEnt_idem {s : Seq ν} (F : CornerIdem C k s) :
    upEnt RD k μ F.f s s ≫ upEnt RD k μ F.f s s = upEnt RD k μ F.f s s := by
  rw [← upEnt_mul F.left, F.idem]

variable (RD μ) in
/-- **The 1-morphism `(E_s 1_μ {t}, ϕ(f))` of `U̇`** (KL III §3.5), for an idempotent
`f ∈ e_s R(ν) e_s` of degree `0` and a shift `t`. -/
abbrev kobj {s : Seq ν} (F : CornerIdem C k s) (t : ℤ) : UKar RD k (wν RD ν + μ) μ :=
  idemObj (nfHom RD k (wν RD ν + μ) μ (ups (word s)) (wt_ups_word (μ := μ) s)) t (upEnt RD k μ F.f s s)
    (upEnt_mem F.deg0 s s) F.upEnt_idem

/-- The corner idempotent `e_s` itself. -/
def CornerIdem.ofE (s : Seq ν) : CornerIdem C k s where
  f := e s
  deg0 := (klGradingDatum2 k C).e_mem_grade s
  idem := e_mul_self s
  left := e_mul_self s

/-- `(E_s 1_μ {t}, ϕ(e_s)) = E_s 1_μ {t}`. -/
theorem kobj_ofE (s : Seq ν) (t : ℤ) :
    kobj RD μ (CornerIdem.ofE (C := C) (k := k) s) t =
      nfObj RD k (wν RD ν + μ) μ (ups (word s)) (wt_ups_word (μ := μ) s) t := by
  have h := idemObj_id (P := pres RD k) (deg := deg RD)
    (x := nfHom RD k (wν RD ν + μ) μ (ups (word s)) (wt_ups_word (μ := μ) s)) (t := t)
    ((pres RD k).id_mem_homDeg (deg RD) _) (Category.comp_id _)
  show _ = objOf _ t
  rw [← h]
  exact idemObj_congr (upEnt_e (RD := RD) (k := k) (μ := μ) s) _ _ _ _

theorem corner_left {s s' : Seq ν} {F : CornerIdem C k s} {F' : CornerIdem C k s'} {y : R2 k C ν}
    (hyc : F'.f * y * F.f = y) : e s' * y = y := by
  rw [← hyc, ← mul_assoc, ← mul_assoc, F'.left]

theorem corner_mul_left {s s' : Seq ν} {F : CornerIdem C k s} {F' : CornerIdem C k s'}
    {y : R2 k C ν} (hyc : F'.f * y * F.f = y) : F'.f * y = y := by
  conv_lhs => rw [← hyc]
  rw [← mul_assoc, ← mul_assoc, F'.idem, hyc]

theorem corner_mul_right {s s' : Seq ν} {F : CornerIdem C k s} {F' : CornerIdem C k s'}
    {y : R2 k C ν} (hyc : F'.f * y * F.f = y) : y * F.f = y := by
  conv_lhs => rw [← hyc]
  rw [mul_assoc, F.idem, hyc]

theorem upEnt_corner {s s' : Seq ν} {F : CornerIdem C k s} {F' : CornerIdem C k s'} {y : R2 k C ν}
    (hyc : F'.f * y * F.f = y) :
    upEnt RD k μ y s s' = upEnt RD k μ F.f s s ≫ upEnt RD k μ y s s' ≫ upEnt RD k μ F'.f s' s' := by
  conv_lhs => rw [← hyc]
  rw [upEnt_mul F.left, upEnt_mul (corner_left hyc)]

/-- The morphism `(E_s 1_μ {t}, ϕ(f)) ⟶ (E_{s'} 1_μ {t'}, ϕ(f'))` given by `y ∈ f' R(ν) f` of
degree `t - t'`. -/
def khom {s s' : Seq ν} {F : CornerIdem C k s} {F' : CornerIdem C k s'} {t t' : ℤ} (y : R2 k C ν)
    (hy : y ∈ (klGradingDatum2 k C).grade ν (t - t')) (hyc : F'.f * y * F.f = y) :
    kobj RD μ F t ⟶ kobj RD μ F' t' :=
  idemHom (upEnt RD k μ y s s') (upEnt_mem hy s s') (upEnt_corner (RD := RD) (μ := μ) hyc)

theorem khom_comp {s s' s'' : Seq ν} {F : CornerIdem C k s} {F' : CornerIdem C k s'}
    {F'' : CornerIdem C k s''} {t t' t'' : ℤ} (y z : R2 k C ν)
    (hy : y ∈ (klGradingDatum2 k C).grade ν (t - t'))
    (hz : z ∈ (klGradingDatum2 k C).grade ν (t' - t'')) (hyc : F'.f * y * F.f = y)
    (hzc : F''.f * z * F'.f = z) :
    (khom (RD := RD) (μ := μ) (F := F) (F' := F') y hy hyc) ≫ (khom (F' := F'') z hz hzc) =
      khom (z * y) (by
          have := SetLike.mul_mem_graded hz hy
          rwa [show t' - t'' + (t - t') = t - t'' by ring] at this)
        (by rw [← mul_assoc, corner_mul_left hzc, mul_assoc, corner_mul_right hyc]) := by
  rw [khom, khom, idemHom_comp]
  apply idemHom_congr
  exact (upEnt_mul (corner_left hyc) s s'').symm

theorem khom_self {s : Seq ν} (F : CornerIdem C k s) (t : ℤ)
    (hy : F.f ∈ (klGradingDatum2 k C).grade ν (t - t)) (hyc : F.f * F.f * F.f = F.f) :
    khom (RD := RD) (μ := μ) (F := F) (F' := F) F.f hy hyc = 𝟙 _ :=
  idemHom_eq_id rfl _ _

theorem khom_congr {s s' : Seq ν} {F : CornerIdem C k s} {F' : CornerIdem C k s'} {t t' : ℤ}
    {y y' : R2 k C ν} (h : y = y') (hy : y ∈ (klGradingDatum2 k C).grade ν (t - t'))
    (hy' : y' ∈ (klGradingDatum2 k C).grade ν (t - t')) (hyc : F'.f * y * F.f = y)
    (hyc' : F'.f * y' * F.f = y') :
    khom (RD := RD) (μ := μ) (F := F) (F' := F') y hy hyc = khom y' hy' hyc' := by
  subst h; rfl

theorem khom_eq_zero {s s' : Seq ν} {F : CornerIdem C k s} {F' : CornerIdem C k s'} {t t' : ℤ}
    {y : R2 k C ν} (h : y = 0) (hy : y ∈ (klGradingDatum2 k C).grade ν (t - t'))
    (hyc : F'.f * y * F.f = y) :
    khom (RD := RD) (μ := μ) (F := F) (F' := F') y hy hyc = 0 := by
  subst h
  exact idemHom_eq_zero (by rw [upEnt, map_zero]; rfl) _ _

theorem sum_khom {s s' : Seq ν} {F : CornerIdem C k s} {F' : CornerIdem C k s'} {t t' : ℤ}
    {ι : Type*} (S : Finset ι) (y : ι → R2 k C ν)
    (hy : ∀ i, y i ∈ (klGradingDatum2 k C).grade ν (t - t'))
    (hyc : ∀ i, F'.f * y i * F.f = y i) :
    ∑ i ∈ S, khom (RD := RD) (μ := μ) (F := F) (F' := F') (y i) (hy i) (hyc i) =
      khom (∑ i ∈ S, y i) (Submodule.sum_mem _ fun i _ => hy i)
        (by rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => hyc i) := by
  simp only [khom]
  rw [sum_idemHom]
  apply idemHom_congr
  rw [upEnt, map_sum, MatEnd.sum_apply]

/-- **Equivalent idempotents give isomorphic 1-morphisms of `U̇`**: if `a b = f`, `b a = f'`,
`a b a = a`, `b a b = b` (`IsEquivPair`), `a` of degree `d` and `b` of degree `-d`, then
`(E_s 1_μ {t}, ϕ(f)) ≅ (E_{s'} 1_μ {t + d}, ϕ(f'))`. -/
def kIso {s s' : Seq ν} (F : CornerIdem C k s) (F' : CornerIdem C k s') {a b : R2 k C ν}
    (h : IsEquivPair a b F.f F'.f) {d : ℤ} (ha : a ∈ (klGradingDatum2 k C).grade ν d)
    (hb : b ∈ (klGradingDatum2 k C).grade ν (-d)) (t : ℤ) :
    kobj RD μ F t ≅ kobj RD μ F' (t + d) where
  hom := khom b (by rwa [show t - (t + d) = -d by ring])
    (by rw [h.left_mul', h.mul_right'])
  inv := khom a (by rwa [show t + d - t = d by ring]) (by rw [h.left_mul, h.mul_right])
  hom_inv_id := by
    rw [khom_comp]
    rw [khom_congr h.1 _ (by rw [sub_self]; exact F.deg0)
      _ (by rw [F.idem, F.idem])]
    exact khom_self F t _ _
  inv_hom_id := by
    rw [khom_comp]
    rw [khom_congr h.2.1 _ (by rw [sub_self]; exact F'.deg0)
      _ (by rw [F'.idem, F'.idem])]
    exact khom_self F' (t + d) _ _

theorem grade_sub_self {r : R2 k C ν} (h : r ∈ (klGradingDatum2 k C).grade ν 0) (t : ℤ) :
    r ∈ (klGradingDatum2 k C).grade ν (t - t) := by
  rwa [sub_self]

/-- **Orthogonal decompositions**: if `f = ∑_j g_j` with `g_j` mutually orthogonal idempotents
of degree `0` in `e_s R(ν) e_s`, then `(E_s 1_μ {t}, ϕ(f)) ≅ ⨁_j (E_s 1_μ {t}, ϕ(g_j))`. -/
def kOrthIso {s : Seq ν} (F : CornerIdem C k s) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Gs : ι → CornerIdem C k s) (hsum : ∑ j, (Gs j).f = F.f)
    (horth : ∀ j j', j ≠ j' → (Gs j).f * (Gs j').f = 0) (t : ℤ) :
    kobj RD μ F t ≅ ⨁ fun j => kobj RD μ (Gs j) t :=
  have hl : ∀ j, (Gs j).f * F.f = (Gs j).f := fun j => by
    rw [← hsum, Finset.mul_sum, Finset.sum_eq_single j (fun j' _ h => horth j j' (Ne.symm h))
      (fun h => absurd (Finset.mem_univ j) h), (Gs j).idem]
  have hr : ∀ j, F.f * (Gs j).f = (Gs j).f := fun j => by
    rw [← hsum, Finset.sum_mul, Finset.sum_eq_single j (fun j' _ h => horth j' j h)
      (fun h => absurd (Finset.mem_univ j) h), (Gs j).idem]
  OrthDecomp.iso
    { a := fun j => khom (Gs j).f (grade_sub_self (Gs j).deg0 t) (by rw [(Gs j).idem, hl])
      b := fun j => khom (Gs j).f (grade_sub_self (Gs j).deg0 t) (by rw [hr, (Gs j).idem])
      total := by
        simp only [khom_comp]
        rw [Finset.sum_congr rfl fun j _ => khom_congr (Gs j).idem _ (grade_sub_self (Gs j).deg0 t)
          _ (by rw [hr, hl])]
        rw [sum_khom, khom_congr hsum _ (grade_sub_self F.deg0 t) _ (by rw [F.idem, F.idem])]
        exact khom_self F t _ _
      b_a_self := fun j => by
        rw [khom_comp, khom_congr (Gs j).idem _ (grade_sub_self (Gs j).deg0 t) _
          (by rw [(Gs j).idem, (Gs j).idem])]
        exact khom_self (Gs j) t _ _
      b_a_ne := fun j j' h => by
        rw [khom_comp]
        exact khom_eq_zero (horth j' j (Ne.symm h)) _ _ }

/-- **Families of equivalent idempotents.** Let `(f_m)_{m ∈ M}` and `(f'_n)_{n ∈ N}` be families of
mutually orthogonal idempotents of degree `0` in corners `e_{σ m} R(ν) e_{σ m}`,
`e_{σ' n} R(ν) e_{σ' n}`, and let `β α = ∑_m f_m`, `α β = ∑_n f'_n` (`IsEquivPair β α`), where the
blocks `f'_n α f_m` have degree `t_m - t'_n` and `f_m β f'_n` degree `t'_n - t_m`. Then
`⨁_m (E_{σ m} 1_μ {t_m}, ϕ(f_m)) ≅ ⨁_n (E_{σ' n} 1_μ {t'_n}, ϕ(f'_n))`. -/
def kFamilyIso {M N : Type} [Fintype M] [DecidableEq M] [Fintype N] [DecidableEq N]
    {σ : M → Seq ν} {σ' : N → Seq ν} (F : ∀ m, CornerIdem C k (σ m))
    (F' : ∀ n, CornerIdem C k (σ' n)) (tt : M → ℤ) (tt' : N → ℤ)
    (horth : ∀ m m', m ≠ m' → (F m).f * (F m').f = 0)
    (horth' : ∀ n n', n ≠ n' → (F' n).f * (F' n').f = 0) {α β : R2 k C ν}
    (hpair : IsEquivPair β α (∑ m, (F m).f) (∑ n, (F' n).f))
    (hα : ∀ m n, (F' n).f * α * (F m).f ∈ (klGradingDatum2 k C).grade ν (tt m - tt' n))
    (hβ : ∀ n m, (F m).f * β * (F' n).f ∈ (klGradingDatum2 k C).grade ν (tt' n - tt m)) :
    (⨁ fun m => kobj RD μ (F m) (tt m)) ≅ ⨁ fun n => kobj RD μ (F' n) (tt' n) :=
  have hsand : ∀ m m' : M, (F m').f * (∑ m'', (F m'').f) * (F m).f =
      if m = m' then (F m).f else 0 := fun m m' => by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single m']
    · rw [(F m').idem]
      split_ifs with h
      · subst h; exact (F m).idem
      · exact horth m' m (Ne.symm h)
    · intro b _ hb; rw [horth m' b (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsand' : ∀ n n' : N, (F' n').f * (∑ n'', (F' n'').f) * (F' n).f =
      if n = n' then (F' n).f else 0 := fun n n' => by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single n']
    · rw [(F' n').idem]
      split_ifs with h
      · subst h; exact (F' n).idem
      · exact horth' n' n (Ne.symm h)
    · intro b _ hb; rw [horth' n' b (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  matrixIso
    (fun m n => khom ((F' n).f * α * (F m).f) (hα m n)
      (by rw [← mul_assoc, ← mul_assoc, (F' n).idem, mul_assoc, (F m).idem]))
    (fun n m => khom ((F m).f * β * (F' n).f) (hβ n m)
      (by rw [← mul_assoc, ← mul_assoc, (F m).idem, mul_assoc, (F' n).idem]))
    (fun m m' => by
      simp only [khom_comp]
      rw [sum_khom]
      have key : ∑ n, (F m').f * β * (F' n).f * ((F' n).f * α * (F m).f) =
          (F m').f * (∑ m'', (F m'').f) * (F m).f := by
        calc ∑ n, (F m').f * β * (F' n).f * ((F' n).f * α * (F m).f)
            = ∑ n, (F m').f * β * (F' n).f * α * (F m).f := Finset.sum_congr rfl fun n _ => by
              simp only [mul_assoc]; rw [← mul_assoc (F' n).f (F' n).f, (F' n).idem]
          _ = (F m').f * β * (∑ n, (F' n).f) * α * (F m).f := by
              simp only [Finset.mul_sum, Finset.sum_mul]
          _ = (F m').f * (β * α * β) * α * (F m).f := by
              rw [← hpair.2.1]; simp only [mul_assoc]
          _ = (F m').f * (∑ m'', (F m'').f) * (F m).f := by
              rw [hpair.2.2.1, ← hpair.1]; simp only [mul_assoc]
      split_ifs with h
      · subst h
        rw [eqToHom_refl, khom_congr (key.trans ((hsand m m).trans (if_pos rfl))) _
          (grade_sub_self (F m).deg0 _) _ (by rw [(F m).idem, (F m).idem])]
        exact khom_self _ _ _ _
      · exact khom_eq_zero (key.trans ((hsand m m').trans (if_neg h))) _ _)
    (fun n n' => by
      simp only [khom_comp]
      rw [sum_khom]
      have key : ∑ m, (F' n').f * α * (F m).f * ((F m).f * β * (F' n).f) =
          (F' n').f * (∑ n'', (F' n'').f) * (F' n).f := by
        calc ∑ m, (F' n').f * α * (F m).f * ((F m).f * β * (F' n).f)
            = ∑ m, (F' n').f * α * (F m).f * β * (F' n).f := Finset.sum_congr rfl fun m _ => by
              simp only [mul_assoc]; rw [← mul_assoc (F m).f (F m).f, (F m).idem]
          _ = (F' n').f * α * (∑ m, (F m).f) * β * (F' n).f := by
              simp only [Finset.mul_sum, Finset.sum_mul]
          _ = (F' n').f * (α * β * α) * β * (F' n).f := by
              rw [← hpair.1]; simp only [mul_assoc]
          _ = (F' n').f * (∑ n'', (F' n'').f) * (F' n).f := by
              rw [hpair.2.2.2, ← hpair.2.1]; simp only [mul_assoc]
      split_ifs with h
      · subst h
        rw [eqToHom_refl, khom_congr (key.trans ((hsand' n n).trans (if_pos rfl))) _
          (grade_sub_self (F' n).deg0 _) _ (by rw [(F' n).idem, (F' n).idem])]
        exact khom_self _ _ _ _
      · exact khom_eq_zero (key.trans ((hsand' n n').trans (if_neg h))) _ _)

end KObj

end Categorification.KL3.Diagram
