/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleAllDownMap
import Categorification.Diagrams.KL3.Upward

/-!
# The matrix map on all-down diagrams

Webster, arXiv:1309.3796v2, §4.5, Definition 4.27 and Lemma 4.28.
A linear functor translating ordinary KLR diagrams to signed diagrams
induces an algebra homomorphism into the matrix algebra on ordered all-down
boundaries. In a product of translated matrices the terms with disordered
middle boundary vanish because the signed diagrams preserve the list of reds.
-/

noncomputable section
namespace Categorification.Stendhal.DoubleDiagram

open KLR KLR.Diagram CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams TypeA
open scoped Classical

variable {I X Y : Type*} {C : CartanDatum I} [AddCommGroup X] [AddCommGroup Y]
    {RD : WeightDatum C X Y} {ℓ : ℕ}
    {Λ : Fin ℓ → {x : X // ∀ i, 0 ≤ RD.pair (RD.iY i) x}}
    {k : Type*} [CommRing k] (P : Presentation (signature RD (Subtype.val ∘ Λ)) k)
    {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "Ord" => {s : Seq μ // IsRedOrdered s}

/-- The signed object for a loading, before imposing its red order. -/
abbrev signedSeqObj (s : Seq μ) :=
  P.obj (obj RD (Subtype.val ∘ Λ) 0 ((word s).map DoubleStrand.down))

/-- Pass a signed morphism between ordered sequences to the quotient by
violated boundaries. -/
def signedDownEntry (s t : Ord) :
    (signedSeqObj P s.val ⟶ signedSeqObj P t.val) →ₗ[k] (downObj P s ⟶ downObj P t) where
  toFun f := (violatingFunctor P _).map (InducedCategory.homMk f)
  map_add' f g := (violatingFunctor P _).map_add
    (f := InducedCategory.homMk (X := downTriple RD Λ s) (Y := downTriple RD Λ t) f)
    (g := InducedCategory.homMk (X := downTriple RD Λ s) (Y := downTriple RD Λ t) g)
  map_smul' c f := (violatingFunctor P _).map_smul c
    (InducedCategory.homMk (X := downTriple RD Λ s) (Y := downTriple RD Λ t) f)

private theorem signedDownEntry_comp (s t u : Ord)
    (f : signedSeqObj P s.val ⟶ signedSeqObj P t.val)
    (g : signedSeqObj P t.val ⟶ signedSeqObj P u.val) :
    signedDownEntry P s u (f ≫ g) = signedDownEntry P s t f ≫ signedDownEntry P t u g :=
  (violatingFunctor P _).map_comp
    (InducedCategory.homMk (X := downTriple RD Λ s) (Y := downTriple RD Λ t) f)
    (InducedCategory.homMk (X := downTriple RD Λ t) (Y := downTriple RD Λ u) g)

private theorem signedDownEntry_id (s : Ord) :
    signedDownEntry P s s (𝟙 _) = 𝟙 _ := (violatingFunctor P _).map_id (downTriple RD Λ s)

private theorem ordered_sum (s u : Ord) (f g : MatEnd (signedSeqObj P (ν := ν))) :
    (f * g) s.val u.val = ∑ t : Ord, g s.val t.val ≫ f t.val u.val := by
  rw [MatEnd.mul_apply]
  let term := fun t : Seq μ => g s.val t ≫ f t u.val
  change ∑ t, term t = ∑ t : Ord, term t.val
  rw [← Finset.sum_subtype (Finset.univ.filter IsRedOrdered) (fun _ => by simp) term]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro t _ ht
  have hno : ¬ IsRedOrdered t := by simpa using ht
  change g s.val t ≫ f t u.val = 0
  have hg : g s.val t = 0 := hom_eq_zero_of_ordered_unordered P s.property hno _
  exact (congrArg (fun z => z ≫ f t u.val) hg).trans (Limits.zero_comp)

/-- Restriction to the principal ordered submatrix followed by the violating
quotient is an algebra homomorphism on matrices of signed all-down diagrams. -/
def downMatrixRestriction : MatEnd (signedSeqObj P (ν := ν)) →ₐ[k] downwardMatrix P ν where
  toFun f s t := signedDownEntry P s t (f s.val t.val)
  map_one' := by
    apply MatEnd.ext
    intro s t
    change signedDownEntry P s t ((1 : MatEnd (signedSeqObj P)) s.val t.val) = _
    by_cases h : s = t
    · subst t; rw [MatEnd.one_apply_self, signedDownEntry_id, MatEnd.one_apply_self]
    · rw [MatEnd.one_apply_of_ne (fun he => h (Subtype.ext he)), map_zero, MatEnd.one_apply_of_ne h]
  map_mul' f g := by
    apply MatEnd.ext
    intro s u
    change signedDownEntry P s u ((f * g) s.val u.val) = _
    change signedDownEntry P s u ((f * g) s.val u.val) =
      ∑ t : Ord, signedDownEntry P s t (g s.val t.val) ≫ signedDownEntry P t u (f t.val u.val)
    rw [ordered_sum, map_sum]
    exact Finset.sum_congr rfl fun t _ => signedDownEntry_comp P s t u _ _
  map_zero' := MatEnd.ext fun s t => map_zero (signedDownEntry P s t)
  map_add' f g := MatEnd.ext fun s t => map_add (signedDownEntry P s t) _ _
  commutes' r := by
    apply MatEnd.ext
    intro s t
    change signedDownEntry P s t ((algebraMap k (MatEnd (signedSeqObj P)) r) s.val t.val) = _
    simp only [Algebra.algebraMap_eq_smul_one, MatEnd.smul_apply, map_smul]
    congr 1
    by_cases h : s = t
    · subst t; rw [MatEnd.one_apply_self, MatEnd.one_apply_self, signedDownEntry_id]
    · rw [MatEnd.one_apply_of_ne (fun he => h (Subtype.ext he)), map_zero, MatEnd.one_apply_of_ne h]

section Functor

variable (R : I ⊕ Fin ℓ → I ⊕ Fin ℓ → MvPolynomial (Fin 2) k)
private abbrev ordinaryObj (s : Seq μ) := (KLR.Diagram.pres k R).obj (KLR.Diagram.ob (word s))
local notation "W" => ordinaryObj (ν := ν) R

private def changeMatrixObjects {ι D : Type*} [Fintype ι] [DecidableEq ι]
    [Category D] [Preadditive D] [Linear k D] {U V : ι → D} (h : ∀ i, U i = V i) :
    MatEnd U ≃ₐ[k] MatEnd V := (funext h) ▸ (AlgEquiv.refl : MatEnd U ≃ₐ[k] MatEnd U)

private theorem changeMatrixObjects_apply {ι D : Type*} [Fintype ι] [DecidableEq ι]
    [Category D] [Preadditive D] [Linear k D] {U V : ι → D} (h : ∀ i, U i = V i)
    (f : MatEnd U) (i j : ι) : changeMatrixObjects (k := k) h f i j =
      eqToHom (h i).symm ≫ f i j ≫ eqToHom (h j) := by
  obtain rfl := funext h
  simp [changeMatrixObjects]

variable (F : (KLR.Diagram.pres k R).Presented ⥤ P.Presented) [F.Additive] [F.Linear k]
  (hobj : ∀ s : Seq (stendhalWeight ℓ ν), F.obj ((KLR.Diagram.pres k R).obj (KLR.Diagram.ob (word s))) = signedSeqObj P s)

/-- The ordinary KLR algebra acts by its translated diagram matrices on the
ordered all-down objects, modulo violated diagrams. -/
def downMatrixOfFunctor : KLRAlgebra k R μ →ₐ[k] downwardMatrix P ν :=
  let g : DiagR k R μ →ₐ[k] MatEnd (fun i => F.obj (W i)) := KL3.Diagram.matEndMap k F W
  let h : MatEnd (fun i => F.obj (W i)) ≃ₐ[k] MatEnd (signedSeqObj P (ν := ν)) :=
    changeMatrixObjects (U := fun i => F.obj (W i)) (V := signedSeqObj P) hobj
  (downMatrixRestriction P).comp (h.toAlgHom.comp (g.comp (diagREquiv k R μ).toAlgHom))

/-- The image of an individual ordinary Hom entry. -/
def downFunctorEntry (s t : Ord) (f : (W s.val ⟶ W t.val)) : downObj P s ⟶ downObj P t :=
  signedDownEntry P s t (eqToHom (hobj s.val).symm ≫ F.map f ≫ eqToHom (hobj t.val))

theorem downMatrixOfFunctor_apply (r : KLRAlgebra k R μ) (s t : Ord) :
    downMatrixOfFunctor P R F hobj r s t =
      downFunctorEntry P R F hobj s t (diagREquiv k R μ r s.val t.val) := by
  change signedDownEntry P s t (changeMatrixObjects hobj _ s.val t.val) = _
  rw [changeMatrixObjects_apply]
  rfl

omit [F.Linear k] in
@[simp] theorem downFunctorEntry_zero (s t : Ord) :
    downFunctorEntry P R F hobj s t 0 = 0 := by simp [downFunctorEntry]

omit [F.Additive] [F.Linear k] in
@[simp] theorem downFunctorEntry_id (s : Ord) :
    downFunctorEntry P R F hobj s s (𝟙 _) = 𝟙 _ := by
  simp [downFunctorEntry, signedDownEntry_id]

/-- Identity diagrams become the ordered boundary idempotents. -/
theorem downMatrixOfFunctor_e (a : Seq μ) :
    downMatrixOfFunctor P R F hobj (KLRAlgebra.e a) = downE P a := by
  apply MatEnd.ext
  intro s t
  rw [downMatrixOfFunctor_apply, diagREquiv_e, DiagR.E]
  by_cases hs : s.val = a
  · subst a
    rw [downE_of_ordered]
    by_cases ht : t = s
    · subst t; simp
    · rw [MatEnd.single_apply_of_ne _ (fun h => ht (Subtype.ext h.2)),
        downFunctorEntry_zero, MatEnd.single_apply_of_ne _ (fun h => ht h.2)]
  · rw [MatEnd.single_apply_of_ne _ (fun h => hs h.1), downFunctorEntry_zero]
    by_cases ha : IsRedOrdered a
    · rw [downE, dite_eq_left ha]
      exact (MatEnd.single_apply_of_ne _ (fun h => hs (congrArg Subtype.val h.1))).symm
    · rw [downE_of_unordered P a ha, MatEnd.zero_apply]

private theorem strandSum_entry {j : Seq μ → Seq μ}
    (f : ∀ i : Seq μ, W i ⟶ W (j i)) (s t : Seq μ) :
    (∑ i : Seq μ, MatEnd.single i (j i) (f i) : DiagR k R μ) s t =
      MatEnd.single s (j s) (f s) s t := by
  rw [MatEnd.sum_apply, Finset.sum_eq_single s]
  · intro i _ hi; exact MatEnd.single_apply_of_ne _ (fun h => hi h.1.symm)
  · simp

/-- Once individual dots translate to the signed dot layers (zero on red),
the affine dot generator becomes the diagonal sum of these layers. -/
theorem downMatrixOfFunctor_x (a : Fin (Multiset.card μ))
    (hdot : ∀ s : Ord, downFunctorEntry P R F hobj s s (dotE k R s.val a) = downDot P s a) :
    downMatrixOfFunctor P R F hobj (KLRAlgebra.x a) = downX P a := by
  apply MatEnd.ext
  intro s t
  rw [downMatrixOfFunctor_apply, diagREquiv_x, DiagR.X, strandSum_entry R (j := fun i => i) (fun i => dotE k R i a) s.val t.val]
  by_cases h : s = t
  · subst t
    rw [MatEnd.single_apply_self, downX_apply_self, hdot]
  · rw [MatEnd.single_apply_of_ne _ (fun e => h (Subtype.ext e.2.symm)),
      downFunctorEntry_zero, downX_apply_of_ne P a h]

/-- A crossing matrix is determined by the one potentially nonzero entry
in each row. The equality of target sequences supplies its boundary transport. -/
theorem downMatrixOfFunctor_ψ (j : ℕ)
    (hcross : ∀ (s t : Ord) (h : t.val = sadj (Multiset.card μ) j • s.val),
      downFunctorEntry P R F hobj s t
        (crossE k R s.val j ≫ eqToHom (congrArg W h.symm)) = downCross P s t j) :
    downMatrixOfFunctor P R F hobj (KLRAlgebra.ψ j) = downΨ P j := by
  apply MatEnd.ext
  intro s t
  rw [downMatrixOfFunctor_apply, diagREquiv_ψ, DiagR.Ψ, strandSum_entry]
  by_cases h : t.val = sadj (Multiset.card μ) j • s.val
  · rw [MatEnd.single_apply, dite_eq_left ⟨rfl, h⟩]
    change downFunctorEntry P R F hobj s t _ = downCross P s t j
    simp only [eqToHom_refl, Category.id_comp]
    exact hcross s t h
  · rw [MatEnd.single_apply_of_ne _ (fun e => h e.2), downFunctorEntry_zero,
      downΨ_apply_of_ne P j h]

end Functor

end Categorification.Stendhal.DoubleDiagram
