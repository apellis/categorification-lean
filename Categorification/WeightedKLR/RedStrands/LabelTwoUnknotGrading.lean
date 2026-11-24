/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoUnknotHomology

/-!
# Internal shifts of the label-two middle complex

Webster, arXiv:1309.3796v2, §8.2, printed page 81, proof of Proposition 8.4.
The scalar and epsilon lines in the term of homological degree `n` have
internal shifts `-2n` and `-2n-2`. The specialized differentials preserve that
internal index.
-/

namespace Categorification.Webster.LabelTwo

noncomputable section

open TrivSqZeroExt

variable {k : Type*} [Field k]

local notation "B" => DualNumber k

/-- The scalar line in the two-dimensional middle quotient. -/
def scalarLine : Submodule k B := (TrivSqZeroExt.sndHom k k).ker

/-- The epsilon line in the two-dimensional middle quotient. -/
def epsilonLine : Submodule k B :=
  ((TrivSqZeroExt.fstHom k k k).toLinearMap).ker

theorem scalarLine_inf_epsilonLine : (scalarLine (k := k)) ⊓ epsilonLine = ⊥ := by
  ext x
  change (x.snd=0 ∧ x.fst=0) ↔ x=0
  constructor
  · rintro ⟨h₁,h₂⟩
    exact TrivSqZeroExt.ext h₂ h₁
  · rintro rfl
    exact ⟨rfl,rfl⟩

theorem scalarLine_sup_epsilonLine : (scalarLine (k := k)) ⊔ epsilonLine = ⊤ := by
  apply top_unique
  intro x _
  exact Submodule.mem_sup.mpr ⟨inl x.fst,rfl,inr x.snd,rfl,x.inl_fst_add_inr_snd_eq⟩

/-- The internal component of the term with Webster's shift `-2n`. -/
def internalPiece (n : ℕ) (q : ℤ) : Submodule k B :=
  if q = -2*(n:ℤ) then scalarLine
  else if q = -2*(n:ℤ)-2 then epsilonLine else ⊥

theorem internalPiece_scalar (n : ℕ) : internalPiece (k := k) n (-2*(n:ℤ)) = scalarLine := by
  simp [internalPiece]

theorem internalPiece_epsilon (n : ℕ) : internalPiece (k := k) n (-2*(n:ℤ)-2) = epsilonLine := by
  have h : -2*(n:ℤ)-2 ≠ -2*(n:ℤ) := by omega
  rw [internalPiece,ite_eq_right h,ite_eq_left rfl]

theorem internalPiece_zero_of_ne (n : ℕ) (q : ℤ) (h₁ : q ≠ -2*(n:ℤ))
    (h₂ : q ≠ -2*(n:ℤ)-2) : internalPiece (k := k) n q = ⊥ := by
  rw [internalPiece,ite_eq_right h₁,ite_eq_right h₂]

private theorem twiceEps_mem_epsilonLine (x : B) : twiceEps x ∈ epsilonLine := by
  rw [twiceEps_coordinates]
  rfl

private theorem twiceEps_eq_zero_of_mem_epsilonLine {x : B} (h : x ∈ epsilonLine) :
    twiceEps x = 0 := by
  have hx : x.fst=0 := h
  rw [twiceEps_coordinates,hx,mul_zero,inr_zero]

theorem twiceEps_preserves_internalPiece (n : ℕ) (q : ℤ) {x : B}
    (hx : x ∈ internalPiece (n+1) q) : twiceEps x ∈ internalPiece n q := by
  by_cases h₁ : q = -2*((n+1:ℕ):ℤ)
  · have h₂ : q = -2*(n:ℤ)-2 := by omega
    rw [h₂,internalPiece_epsilon]
    exact twiceEps_mem_epsilonLine x
  · by_cases h₂ : q = -2*((n+1:ℕ):ℤ)-2
    · rw [h₂,internalPiece_epsilon] at hx
      rw [twiceEps_eq_zero_of_mem_epsilonLine hx]
      exact Submodule.zero_mem _
    · rw [internalPiece_zero_of_ne _ _ h₁ h₂,Submodule.mem_bot] at hx
      rw [hx,map_zero]
      exact Submodule.zero_mem _

/-- The actual specialized complex restricts to each internal component. -/
theorem postTensorComplex_preserves_internalPiece (n : ℕ) (q : ℤ) {x : B}
    (hx : x ∈ internalPiece (n+1) q) :
    ((postTensorComplex (k := k)).d (n+1) n).hom x ∈ internalPiece n q := by
  rw [postTensorComplex_d_succ]
  by_cases h : Even n
  · rw [ite_eq_left h,LinearMap.zero_apply]
    exact Submodule.zero_mem _
  · rw [ite_eq_right h]
    exact twiceEps_preserves_internalPiece n q hx


private abbrev nextDifferential (n : ℕ) : B →ₗ[k] B :=
  ((postTensorComplex (k := k)).d (n+1) n).hom

private def previousDifferential : ℕ → B →ₗ[k] B
  | 0 => 0
  | n+1 => nextDifferential n

/-- Cycles of the specialized complex in the homogeneous component. -/
def internalCycles (n : ℕ) (q : ℤ) : Submodule k B :=
  internalPiece n q ⊓ (previousDifferential n).ker

/-- Boundaries in the same internal component. -/
def internalBoundaries (n : ℕ) (q : ℤ) : Submodule k B :=
  (internalPiece (n+1) q).map (nextDifferential n)

theorem internalBoundaries_le_internalCycles (n : ℕ) (q : ℤ) :
    internalBoundaries (k := k) n q ≤ internalCycles n q := by
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨postTensorComplex_preserves_internalPiece n q hx,?_⟩
  cases n with
  | zero => rfl
  | succ n =>
      change nextDifferential n (nextDifferential (n+1) x)=0
      exact congrArg (fun f => (ModuleCat.Hom.hom f) x)
        ((postTensorComplex (k := k)).d_comp_d (n+2) (n+1) n)

theorem internalCycles_zero (q : ℤ) : internalCycles (k := k) 0 q = internalPiece 0 q := by
  simp [internalCycles,previousDifferential]

theorem internalCycles_odd (n : ℕ) (q : ℤ) (hn : Even n) :
    internalCycles (k := k) (n+1) q = internalPiece (n+1) q := by
  simp [internalCycles,previousDifferential,postTensorComplex_d_succ,hn]

theorem internalCycles_positiveEven (n : ℕ) (q : ℤ) (hn : ¬ Even n) (h2 : (2:k)≠0) :
    internalCycles (k := k) (n+1) q = internalPiece (n+1) q ⊓ epsilonLine := by
  rw [internalCycles,previousDifferential,nextDifferential,postTensorComplex_d_succ,ite_eq_right hn,ker_twiceEps h2]
  rfl

private theorem scalarLine_map_twiceEps (h2 : (2:k)≠0) :
    (scalarLine (k := k)).map twiceEps = epsilonLine := by
  ext x
  constructor
  · rintro ⟨z,_,rfl⟩
    exact twiceEps_mem_epsilonLine z
  · intro hx
    refine ⟨inl (x.snd/2),rfl,?_⟩
    rw [twiceEps_coordinates]
    apply TrivSqZeroExt.ext
    · exact (show x.fst=0 from hx).symm
    · change (2:k)*(x.snd/2)=x.snd
      rw [mul_comm,div_mul_cancel₀ _ h2]

private theorem epsilonLine_map_twiceEps :
    (epsilonLine (k := k)).map twiceEps = ⊥ := by
  apply bot_unique
  rintro _ ⟨x,hx,rfl⟩
  rw [twiceEps_eq_zero_of_mem_epsilonLine hx]
  exact Submodule.zero_mem _

theorem internalBoundaries_even (n : ℕ) (q : ℤ) (hn : Even n) :
    internalBoundaries (k := k) n q = ⊥ := by
  simp [internalBoundaries,postTensorComplex_d_succ,hn]

theorem internalBoundaries_odd (n : ℕ) (q : ℤ) (hn : ¬ Even n) (h2 : (2:k)≠0) :
    internalBoundaries (k := k) n q = if q = -2*(n:ℤ)-2 then epsilonLine else ⊥ := by
  rw [internalBoundaries,nextDifferential,postTensorComplex_d_succ,ite_eq_right hn]
  by_cases h₁ : q = -2*((n+1:ℕ):ℤ)
  · have h₂ : q = -2*(n:ℤ)-2 := by omega
    rw [ite_eq_left h₂,h₁,internalPiece_scalar,scalarLine_map_twiceEps h2]
  · have h₃ : q ≠ -2*(n:ℤ)-2 := by omega
    rw [ite_eq_right h₃]
    by_cases h₂ : q = -2*((n+1:ℕ):ℤ)-2
    · rw [h₂,internalPiece_epsilon,epsilonLine_map_twiceEps]
    · rw [internalPiece_zero_of_ne _ _ h₁ h₂,Submodule.map_bot]

/-- Homology of the cycles and boundaries at one internal index. -/
abbrev internalHomology (n : ℕ) (q : ℤ) :=
  ↥(internalCycles (k := k) n q) ⧸
    (internalBoundaries (k := k) n q).comap (internalCycles (k := k) n q).subtype


private def scalarLineEquiv : (scalarLine (k := k)) ≃ₗ[k] k where
  toFun x := x.val.fst
  invFun a := ⟨inl a,rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · rfl
    · exact (show x.val.snd=0 from x.property).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def epsilonLineEquiv : (epsilonLine (k := k)) ≃ₗ[k] k where
  toFun x := x.val.snd
  invFun a := ⟨inr a,rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply TrivSqZeroExt.ext
    · exact (show x.val.fst=0 from x.property).symm
    · rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def internalHomologyEquivOfBoundariesZero {n : ℕ} {q : ℤ} {L : Submodule k B}
    (hC : internalCycles (k := k) n q=L) (hB : internalBoundaries (k := k) n q=⊥) :
    internalHomology (k := k) n q ≃ₗ[k] L :=
  (Submodule.quotEquivOfEqBot _ (by
    rw [hB]
    exact Submodule.ker_subtype _)).trans (LinearEquiv.ofEq _ _ hC)

private theorem internalHomology_subsingleton_of_boundaries_eq {n : ℕ} {q : ℤ}
    (h : internalBoundaries (k := k) n q=internalCycles n q) :
    Subsingleton (internalHomology (k := k) n q) :=
  Submodule.Quotient.subsingleton_iff.mpr
    (by rw [h,Submodule.comap_subtype_self])

/-- In homological degree zero the scalar class has internal shift zero. -/
def internalHomology_zero_scalar : internalHomology (k := k) 0 0 ≃ₗ[k] k :=
  (internalHomologyEquivOfBoundariesZero (k := k)
    ((internalCycles_zero 0).trans (show internalPiece 0 0=scalarLine from internalPiece_scalar 0))
    (internalBoundaries_even 0 0 ⟨0,rfl⟩)).trans scalarLineEquiv

/-- In homological degree zero the epsilon class has internal shift `-2`. -/
def internalHomology_zero_epsilon : internalHomology (k := k) 0 (-2) ≃ₗ[k] k :=
  (internalHomologyEquivOfBoundariesZero (k := k)
    ((internalCycles_zero (-2)).trans
      (show internalPiece 0 (-2)=epsilonLine from internalPiece_epsilon 0))
    (internalBoundaries_even 0 (-2) ⟨0,rfl⟩)).trans epsilonLineEquiv

/-- The odd scalar class in degree `n+1` has shift `-2(n+1)`. -/
def internalHomology_odd (n : ℕ) (hn : Even n) (h2 : (2:k)≠0) :
    internalHomology (k := k) (n+1) (-2*((n+1:ℕ):ℤ)) ≃ₗ[k] k := by
  refine (internalHomologyEquivOfBoundariesZero (k := k) (L := scalarLine) ?_ ?_).trans
    scalarLineEquiv
  · rw [internalCycles_odd _ _ hn,internalPiece_scalar]
  · rw [internalBoundaries_odd _ _ (by simp [Nat.even_add_one,hn]) h2]
    exact ite_eq_right (by omega)

/-- The positive even epsilon class in degree `n+1` has shift `-2(n+1)-2`. -/
def internalHomology_positiveEven (n : ℕ) (hn : ¬ Even n) (h2 : (2:k)≠0) :
    internalHomology (k := k) (n+1) (-2*((n+1:ℕ):ℤ)-2) ≃ₗ[k] k := by
  refine (internalHomologyEquivOfBoundariesZero (k := k) (L := epsilonLine) ?_ ?_).trans
    epsilonLineEquiv
  · rw [internalCycles_positiveEven _ _ hn h2,internalPiece_epsilon,inf_idem]
  · exact internalBoundaries_even _ _ (by simp [Nat.even_add_one,hn])

/-- The homological and internal indices with surviving classes. -/
def InternalSupport : ℕ → ℤ → Prop
  | 0,q => q=0 ∨ q= -2
  | n+1,q => if Even n then q= -2*((n+1:ℕ):ℤ) else q= -2*((n+1:ℕ):ℤ)-2

theorem internalHomology_off_support (n : ℕ) (q : ℤ) (h2 : (2:k)≠0)
    (h : ¬InternalSupport n q) : Subsingleton (internalHomology (k := k) n q) := by
  apply internalHomology_subsingleton_of_boundaries_eq
  cases n with
  | zero =>
      change ¬ (q=0 ∨ q= -2) at h
      rw [internalBoundaries_even 0 _ ⟨0,rfl⟩,internalCycles_zero,
        internalPiece_zero_of_ne _ _ (fun hq => h (Or.inl hq)) (fun hq => h (Or.inr hq))]
  | succ n =>
      by_cases hn : Even n
      · have hs : q ≠ -2*((n+1:ℕ):ℤ) := by
          simpa only [InternalSupport,ite_eq_left hn] using h
        rw [internalBoundaries_odd _ _ (by simp [Nat.even_add_one,hn]) h2,
          internalCycles_odd _ _ hn]
        by_cases he : q = -2*((n+1:ℕ):ℤ)-2
        · rw [ite_eq_left he,he,internalPiece_epsilon]
        · rw [ite_eq_right he,internalPiece_zero_of_ne _ _ hs he]
      · have he : q ≠ -2*((n+1:ℕ):ℤ)-2 := by
          simpa only [InternalSupport,ite_eq_right hn] using h
        rw [internalBoundaries_even _ _ (by simp [Nat.even_add_one,hn]),
          internalCycles_positiveEven _ _ hn h2]
        by_cases hs : q = -2*((n+1:ℕ):ℤ)
        · rw [hs,internalPiece_scalar,scalarLine_inf_epsilonLine]
        · rw [internalPiece_zero_of_ne _ _ hs he,bot_inf_eq]

private theorem nextDifferential_eq_zero_of_two_eq_zero (h2 : (2 : k) = 0) (n : ℕ) :
    nextDifferential (k := k) n = 0 := by
  rw [nextDifferential, postTensorComplex_d_succ, twiceEps_eq_zero_of_two_eq_zero h2, ite_self]

/-- Each homogeneous component survives unchanged when the specialized maps vanish. -/
def internalHomology_of_two_eq_zero (h2 : (2 : k) = 0) (n : ℕ) (q : ℤ) :
    internalHomology (k := k) n q ≃ₗ[k] internalPiece (k := k) n q := by
  apply internalHomologyEquivOfBoundariesZero
  · cases n with
    | zero => exact internalCycles_zero q
    | succ n =>
        simp [internalCycles, previousDifferential, nextDifferential_eq_zero_of_two_eq_zero h2]
  · simp [internalBoundaries, nextDifferential_eq_zero_of_two_eq_zero h2]

/-- The scalar class survives in shift `-2n` in every homological degree. -/
def internalHomology_scalar_of_two_eq_zero (h2 : (2 : k) = 0) (n : ℕ) :
    internalHomology (k := k) n (-2 * (n : ℤ)) ≃ₗ[k] k :=
  (internalHomology_of_two_eq_zero h2 n _).trans
    ((LinearEquiv.ofEq _ _ (internalPiece_scalar n)).trans scalarLineEquiv)

/-- The epsilon class survives in shift `-2n-2` in every homological degree. -/
def internalHomology_epsilon_of_two_eq_zero (h2 : (2 : k) = 0) (n : ℕ) :
    internalHomology (k := k) n (-2 * (n : ℤ) - 2) ≃ₗ[k] k :=
  (internalHomology_of_two_eq_zero h2 n _).trans
    ((LinearEquiv.ofEq _ _ (internalPiece_epsilon n)).trans epsilonLineEquiv)

/-- All other homogeneous middle Tor components vanish in characteristic two. -/
theorem internalHomology_off_support_of_two_eq_zero (h2 : (2 : k) = 0) (n : ℕ) (q : ℤ)
    (hs : q ≠ -2 * (n : ℤ)) (he : q ≠ -2 * (n : ℤ) - 2) :
    Subsingleton (internalHomology (k := k) n q) := by
  suffices Subsingleton (internalPiece (k := k) n q) from
    (internalHomology_of_two_eq_zero h2 n q).injective.subsingleton
  rw [internalPiece_zero_of_ne n q hs he]
  infer_instance

end

end Categorification.Webster.LabelTwo
