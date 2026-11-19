/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SymmetrySigmaPresented
import Categorification.Diagrams.KLR.Comparison
import Categorification.Diagrams.KL3.Upward

/-!
# The signed reflection of diagrams is the vertical flip `σ`

Khovanov–Lauda, arXiv:0803.4121v2 (KL I), end of §2.1. On the diagrammatic KLR algebra
`DiagR = ⨁_{i, j} Hom(word i, word j)`, the signed reflection of the presented KLR category
(`KSig.ksP`), with the sequences reindexed by `Seq.rev`, is the vertical flip `σ` of the KLR
algebra (`KLRAlgebra.sigma`) under the identification `diagREquiv`
(`KSig.ksMat_comp_toDiagFree`). It is used in the proof of Webster, arXiv:1309.3796v3,
Lemma 4.29.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams Presentation KLR.Diagram MatEnd TypeA

universe w u

section Reindex

variable (k : Type*) [CommRing k] {𝒞 𝒟 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  [Category 𝒟] [Preadditive 𝒟] [Linear k 𝒟] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linear functor and a reindexing of the summands induce an algebra homomorphism of
matrix algebras of morphisms: `(f i j) ↦ (F (f (σ i) (σ j)))`, up to the given identifications
of objects. -/
def matEndReindex (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (Z : ι → 𝒞) (Z' : ι → 𝒟)
    (σ : ι ≃ ι) (h : ∀ i, F.obj (Z (σ i)) = Z' i) : MatEnd Z →ₐ[k] MatEnd Z' where
  toFun f i j := eqToHom (h i).symm ≫ F.map (f (σ i) (σ j)) ≫ eqToHom (h j)
  map_one' := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [one_apply_of_ne hij, one_apply_of_ne (σ.injective.ne hij)]
  map_mul' f g := by
    ext i l
    simp only [mul_apply, Functor.map_sum, Functor.map_comp, Preadditive.sum_comp,
      Preadditive.comp_sum]
    rw [← σ.sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  map_zero' := by ext; simp
  map_add' f g := by ext; simp
  commutes' r := by
    ext i j
    simp only [Algebra.algebraMap_eq_smul_one, MatEnd.smul_apply, Functor.map_smul,
      Linear.smul_comp, Linear.comp_smul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [one_apply_of_ne hij, one_apply_of_ne (σ.injective.ne hij)]

theorem matEndReindex_apply (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (Z : ι → 𝒞) (Z' : ι → 𝒟)
    (σ : ι ≃ ι) (h : ∀ i, F.obj (Z (σ i)) = Z' i) (f : MatEnd Z) (i j : ι) :
    matEndReindex k F Z Z' σ h f i j = eqToHom (h i).symm ≫ F.map (f (σ i) (σ j)) ≫
      eqToHom (h j) := rfl

theorem matEndReindex_single (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (Z : ι → 𝒞)
    (Z' : ι → 𝒟) (σ : ι ≃ ι) (h : ∀ i, F.obj (Z (σ i)) = Z' i) (a c : ι)
    (f : Z (σ a) ⟶ Z (σ c)) :
    matEndReindex k F Z Z' σ h (single (σ a) (σ c) f) =
      single a c (eqToHom (h a).symm ≫ F.map f ≫ eqToHom (h c)) := by
  ext i j
  rw [matEndReindex_apply]
  by_cases hij : i = a ∧ j = c
  · obtain ⟨rfl, rfl⟩ := hij; simp
  · rw [single_apply_of_ne _ hij, single_apply_of_ne, F.map_zero, Limits.zero_comp,
      Limits.comp_zero]
    exact fun h' => hij ⟨σ.injective h'.1, σ.injective h'.2⟩

theorem matEndReindex_single' (F : 𝒞 ⥤ 𝒟) [F.Additive] [F.Linear k] (Z : ι → 𝒞)
    (Z' : ι → 𝒟) (σ : ι ≃ ι) (h : ∀ i, F.obj (Z (σ i)) = Z' i) (a c : ι) {b : ι}
    (hc : σ c = b) (f : Z (σ a) ⟶ Z b) :
    matEndReindex k F Z Z' σ h (single (σ a) b f) =
      single a c (eqToHom (h a).symm ≫ F.map f ≫
        eqToHom ((congrArg (fun t => F.obj (Z t)) hc).symm.trans (h c))) := by
  subst hc; exact matEndReindex_single k F Z Z' σ h a c f

end Reindex

namespace KSig

variable {I : Type u} [DecidableEq I] {k : Type w} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

omit [DecidableEq I] in
theorem word_rev (i : KLR.Seq ν) : word i.rev = (word i).reverse := by
  apply List.ext_getElem
  · simp
  · intro t h₁ h₂
    simp only [getElem_word, List.getElem_reverse, length_word, KLR.Seq.rev_apply]
    refine congrArg i.1 (Fin.ext ?_)
    simp only [Fin.val_rev]
    simp at h₁
    omega

/-- The reversal of sequences as a permutation. -/
def revPerm : KLR.Seq ν ≃ KLR.Seq ν :=
  ⟨KLR.Seq.rev, KLR.Seq.rev, KLR.Seq.rev_rev, KLR.Seq.rev_rev⟩

theorem ksP_obj_word (hQ : KLR.KLRSymm Q) (i : KLR.Seq ν) :
    (ksP Q hQ).obj ((KLR.Diagram.pres k Q).obj (KLR.Diagram.ob (word (revPerm i)))) =
      (KLR.Diagram.pres k Q).obj (KLR.Diagram.ob (word i)) := by
  rw [ksP_obj]
  exact congrArg _ (KLR.Diagram.obj_ext (by simp [kobj, revPerm, word_rev]))

variable (k Q ν) in
/-- **The signed reflection on the diagrammatic KLR algebra**: `ksP` applied entrywise,
with the sequences reversed. -/
def ksMat (hQ : KLR.KLRSymm Q) : DiagR k Q ν →ₐ[k] DiagR k Q ν :=
  matEndReindex k (ksP Q hQ) _ _ revPerm (ksP_obj_word hQ)

omit [DecidableEq I] in
theorem kobj_word_rev (i : KLR.Seq ν) :
    kobj (KLR.Diagram.ob (word (revPerm i))) = KLR.Diagram.ob (word i) :=
  KLR.Diagram.obj_ext (by simp [kobj, revPerm, word_rev])

omit [DecidableEq I] in
theorem eqToHom_diag_eqToHom {a b a' b' : Obj (KLR.Diagram.sig I)} (d : a ⟶ b) (ha : a = a')
    (hb : b = b') (h₁ : (KLR.Diagram.pres k Q).obj a' = (KLR.Diagram.pres k Q).obj a)
    (h₂ : (KLR.Diagram.pres k Q).obj b = (KLR.Diagram.pres k Q).obj b') :
    eqToHom h₁ ≫ (KLR.Diagram.pres k Q).diag d ≫ eqToHom h₂ =
      (KLR.Diagram.pres k Q).diag (Diagram.cast d ha hb) := by
  subst ha hb; simp

/-- The signed reflection of a dot on strand `a` of the reversed sequence is the dot on the
mirror strand `a.rev`. -/
theorem ksP_dotE (hQ : KLR.KLRSymm Q) (i : KLR.Seq ν) (a : Fin m) :
    eqToHom (ksP_obj_word hQ i).symm ≫ (ksP Q hQ).map (dotE k Q (revPerm i) a) ≫
      eqToHom (ksP_obj_word hQ i) = dotE k Q i a.rev := by
  have hs : ksgn (Diagram.layers (dotD (revPerm i) a)) = 1 := by simp [ksgn, ksg]
  rw [dotE, ksP_diag, hs, Int.cast_one, one_smul]
  refine (eqToHom_diag_eqToHom _ (kobj_word_rev i) (kobj_word_rev i) _ _).trans ?_
  apply Presentation.diag_eq_of_layers_eq
  simp only [Diagram.layers_cast, ksD, Diagram.layers_mk, layers_dotD, List.map_cons,
    List.map_nil]
  congr 1
  have hw : word (revPerm i) = (word i).reverse := word_rev i
  have ha := a.isLt
  apply KLR.Diagram.layer_ext
  · simp only [klay, KLR.Diagram.lay_left, KLR.Diagram.lay_right, hw, List.drop_reverse,
      List.reverse_reverse, length_word, Fin.val_rev]
  · rfl
  · simp only [klay, KLR.Diagram.lay_left, KLR.Diagram.lay_right, hw, List.take_reverse,
      List.reverse_reverse, length_word, Fin.val_rev]
    congr 1; omega

omit [DecidableEq I] in
theorem rev_sadj_smul_mirror {j : ℕ} (h : j + 1 < m) (i : KLR.Seq ν) :
    revPerm (sadj m (m - 2 - j) • i) = sadj m j • revPerm i := by
  have := KLR.KLRAlgebra.rev_sadj_smul (show m - 2 - j + 1 < m by omega) i
  rw [show m - 2 - (m - 2 - j) = j by omega] at this
  exact this.symm

omit [DecidableEq I] in
theorem kobj_word_sadj_rev {j : ℕ} (h : j + 1 < m) (i : KLR.Seq ν) :
    kobj (KLR.Diagram.ob (word (sadj m j • revPerm i))) =
      KLR.Diagram.ob (word (sadj m (m - 2 - j) • i)) := by
  rw [← rev_sadj_smul_mirror h]; exact kobj_word_rev _

/-- The signed reflection of the crossing of strands `j`, `j + 1` of the reversed sequence is,
up to the sign `-1` when the two strands have the same colour, the crossing of the mirror
strands `m - 2 - j`, `m - 1 - j`. -/
theorem ksP_crossE (hQ : KLR.KLRSymm Q) (i : KLR.Seq ν) {j : ℕ} (h : j + 1 < m)
    (H : (ksP Q hQ).obj ((KLR.Diagram.pres k Q).obj
        (KLR.Diagram.ob (word (sadj m j • revPerm i)))) =
      (KLR.Diagram.pres k Q).obj (KLR.Diagram.ob (word (sadj m (m - 2 - j) • i)))) :
    eqToHom (ksP_obj_word hQ i).symm ≫ (ksP Q hQ).map (crossE k Q (revPerm i) j) ≫
      eqToHom H = KLR.KLRAlgebra.sgn k j (revPerm i) • crossE k Q i (m - 2 - j) := by
  have h' : m - 2 - j + 1 < m := by omega
  rw [crossE_def _ h, crossE_def _ h', ksP_diag, Linear.smul_comp, Linear.comp_smul,
    KLR.KLRAlgebra.sgn_of_lt h]
  congr 1
  · simp only [layers_crossD, ksgn, ksg, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, KLR.Diagram.lay]
    split_ifs <;> simp
  refine (eqToHom_diag_eqToHom _ (kobj_word_rev i) (kobj_word_sadj_rev h i) _ _).trans ?_
  apply Presentation.diag_eq_of_layers_eq
  simp only [Diagram.layers_cast, ksD, Diagram.layers_mk, layers_crossD, List.map_cons,
    List.map_nil]
  congr 1
  have hw : word (revPerm i) = (word i).reverse := word_rev i
  apply KLR.Diagram.layer_ext
  · simp only [klay, KLR.Diagram.lay_left, KLR.Diagram.lay_right, hw, List.drop_reverse,
      List.reverse_reverse, length_word]
    congr 1; omega
  · simp only [klay, KLR.Diagram.lay, kgen]
    congr 1 <;> exact congrArg i.1 (Fin.ext (by simp; omega))
  · simp only [klay, KLR.Diagram.lay_left, KLR.Diagram.lay_right, hw, List.take_reverse,
      List.reverse_reverse, length_word]
    congr 1; omega

theorem ksMat_E (hQ : KLR.KLRSymm Q) (i : KLR.Seq ν) :
    ksMat k Q ν hQ (DiagR.E (revPerm i)) = DiagR.E i := by
  rw [DiagR.E, ksMat, matEndReindex_single, DiagR.E]; simp

theorem ksMat_X (hQ : KLR.KLRSymm Q) (a : Fin m) :
    ksMat k Q ν hQ (DiagR.X a) = DiagR.X a.rev := by
  conv_lhs => rw [DiagR.X, ← Equiv.sum_comp revPerm, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ksMat, matEndReindex_single, ksP_dotE]

theorem ksMat_Ψ_mul_E (hQ : KLR.KLRSymm Q) {j : ℕ} (h : j + 1 < m) (i : KLR.Seq ν) :
    ksMat k Q ν hQ (DiagR.Ψ j) * DiagR.E i =
      KLR.KLRAlgebra.sgn k j (revPerm i) • (DiagR.Ψ (m - 2 - j) * DiagR.E i) := by
  conv_lhs => rw [← ksMat_E hQ i, ← map_mul, DiagR.E, DiagR.Ψ_mul_single, Category.id_comp,
    ksMat, matEndReindex_single' k _ _ _ revPerm _ i (sadj m (m - 2 - j) • i)
      (rev_sadj_smul_mirror h i), ksP_crossE hQ i h]
  rw [DiagR.E, DiagR.Ψ_mul_single, Category.id_comp, single_smul]

/-- **The signed reflection of diagrams is the vertical flip `σ`** (KL I, arXiv:0803.4121v2,
end of §2.1): on generators of the free algebra, applying the signed reflection entrywise to
the diagram of a word agrees with the diagram of `σ` of the word. -/
theorem ksMat_comp_toDiagFree (hQ : KLR.KLRSymm Q) :
    (ksMat k Q ν hQ).comp (toDiagFree k Q ν) =
      (diagREquiv k Q ν).toAlgHom.comp (KLR.KLRAlgebra.sigmaFree k Q ν) := by
  apply FreeAlgebra.hom_ext
  funext g
  cases g with
  | idem i =>
    obtain ⟨i, rfl⟩ := revPerm.surjective i
    change ksMat k Q ν hQ (toDiagFree k Q ν (KLR.fe k ν _)) =
      diagREquiv k Q ν (KLR.KLRAlgebra.sigmaFree k Q ν (KLR.fe k ν _))
    rw [toDiagFree_fe, KLR.KLRAlgebra.sigmaFree_fe, diagREquiv_e, ksMat_E]
    exact congrArg _ (KLR.Seq.rev_rev i).symm
  | dot a =>
    change ksMat k Q ν hQ (toDiagFree k Q ν (KLR.fx k ν a)) =
      diagREquiv k Q ν (KLR.KLRAlgebra.sigmaFree k Q ν (KLR.fx k ν a))
    rw [toDiagFree_fx, KLR.KLRAlgebra.sigmaFree_fx, diagREquiv_x, ksMat_X]
  | cross j =>
    change ksMat k Q ν hQ (toDiagFree k Q ν (KLR.fψ k ν j)) =
      diagREquiv k Q ν (KLR.KLRAlgebra.sigmaFree k Q ν (KLR.fψ k ν j))
    rw [toDiagFree_fψ, KLR.KLRAlgebra.sigmaFree_fψ]
    by_cases h : j + 1 < m
    · apply DiagR.ext_E
      intro i
      rw [ksMat_Ψ_mul_E hQ h i, ← diagREquiv_e i, ← map_mul]
      conv_rhs => rw [show i = (revPerm i).rev from (KLR.Seq.rev_rev i).symm]
      rw [KLR.KLRAlgebra.sigmaψ_mul_e_rev h, map_smul, map_mul, diagREquiv_ψ,
        show (revPerm i).rev = i from KLR.Seq.rev_rev i, diagREquiv_e]
    · rw [DiagR.Ψ_of_le (by omega), KLR.KLRAlgebra.sigmaψ_of_le (by omega), map_zero, map_zero]

end KSig

end Categorification.KL3.Diagram

end
