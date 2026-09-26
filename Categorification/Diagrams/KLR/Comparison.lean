/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.Soundness
import Categorification.KLR.BasisTheorem
import StringDiagrams.Generation

/-!
# The diagrammatic KLR algebra is the KLR algebra

For a weight `ν`, the algebra `DiagR k Q ν = ⨁_{i, j ∈ Seq ν} Hom(word i, word j)` of the
presented diagrammatic category `pres k Q` is isomorphic to the KLR algebra
`KLRAlgebra k Q ν` of `Categorification.KLR.Basic`:

* `toDiagR : KLRAlgebra k Q ν →ₐ[k] DiagR k Q ν` sends `e i`, `x a`, `ψ j` to the identity
  diagram of `i`, the dot on strand `a` and the crossing of strands `j`, `j + 1` (summed over
  all sequences); it is well defined because every relation `Rel` holds diagrammatically
  (`DiagR.dot_cross_left`, `DiagR.cross_sq`, `DiagR.braid`, …).
* `ofDiagR : DiagR k Q ν →ₐ[k] KLRAlgebra k Q ν` comes from the soundness theorem
  `StringDiagrams.Presentation.lift`: the category `Tgt k Q ν`, whose morphisms `a ⟶ b` are
  the elements of `ε b · R(ν) · ε a` (`ε a` is the idempotent of the word `a`, zero if `a` is
  not a sequence of weight `ν`), receives a functor from the free 2-category sending a dot or
  a crossing layer at position `p` to `x_p ε` or `ψ_p ε`; it kills every whiskered relation and
  every instance of the interchange law.
* `diagREquiv : KLRAlgebra k Q ν ≃ₐ[k] DiagR k Q ν`, the headline isomorphism: the two maps
  are inverse on generators, and `toDiagR` is surjective because every diagram is a composite
  of dot and crossing layers.

Consequently the basis theorem of `R(ν)` transfers to the diagrammatic algebra.
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory StringDiagrams TypeA KLRAlgebra MatEnd DiagR

universe u

variable {I : Type u} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

/-! ## From the KLR algebra to diagrams -/

variable (k Q ν) in
/-- Images of the generators of `R(ν)`. -/
def genImg : KLR.Gen ν → DiagR k Q ν
  | .idem i => E i
  | .dot a => X a
  | .cross j => Ψ j

variable (k Q ν) in
/-- The comparison map on the free algebra. -/
def toDiagFree : FreeAlgebra k (KLR.Gen ν) →ₐ[k] DiagR k Q ν :=
  FreeAlgebra.lift k (genImg k Q ν)

@[simp] theorem toDiagFree_fe (i : Seq ν) : toDiagFree k Q ν (fe k ν i) = E i := by
  simp [toDiagFree, genImg]

@[simp] theorem toDiagFree_fx (a : Fin m) : toDiagFree k Q ν (fx k ν a) = X a := by
  simp [toDiagFree, genImg]

@[simp] theorem toDiagFree_fψ (j : ℕ) : toDiagFree k Q ν (fψ k ν j) = Ψ j := by
  simp [toDiagFree, genImg]

theorem toDiagFree_rel {a b : FreeAlgebra k (KLR.Gen ν)} (h : KLR.Rel k Q ν a b) :
    toDiagFree k Q ν a = toDiagFree k Q ν b := by
  cases h with
  | idem_mul i j =>
    simp only [map_mul, toDiagFree_fe, E_mul_E]
    split_ifs <;> simp
  | idem_sum => simp [map_sum, sum_E]
  | dot_idem a i => simp [X_mul_E]
  | cross_idem j i => simp [Ψ_mul_E]
  | cross_zero j h => simp [Ψ_of_le h]
  | dot_dot a b => simp [X_mul_X]
  | cross_cross j l h => simp [Ψ_mul_Ψ h]
  | dot_cross a j h₁ h₂ => simp [X_mul_Ψ a j h₁ h₂]
  | dot_cross_left j h i =>
    simp only [map_mul, map_sub, toDiagFree_fe, toDiagFree_fx, toDiagFree_fψ,
      DiagR.dot_cross_left h i]
    split_ifs <;> simp
  | dot_cross_right j h i =>
    simp only [map_mul, map_sub, toDiagFree_fe, toDiagFree_fx, toDiagFree_fψ,
      DiagR.dot_cross_right h i]
    split_ifs <;> simp
  | cross_sq j h i =>
    simp only [map_mul, toDiagFree_fe, toDiagFree_fψ, DiagR.cross_sq h i]
    split_ifs
    · simp
    · rw [map_mul, AlgHom.map_ncEval, toDiagFree_fe]
      congr 2
      funext t; fin_cases t <;> simp
  | braid j h i =>
    simp only [map_mul, map_sub, toDiagFree_fe, toDiagFree_fψ, DiagR.braid h i]
    split_ifs
    · rw [map_mul, AlgHom.map_ncEval, toDiagFree_fe]
      congr 2
      funext t; fin_cases t <;> simp
    · simp

variable (k Q ν) in
/-- The comparison homomorphism `R(ν) → DiagR`. -/
def toDiagR : KLRAlgebra k Q ν →ₐ[k] DiagR k Q ν :=
  RingQuot.liftAlgHom k ⟨toDiagFree k Q ν, fun _ _ h => toDiagFree_rel h⟩

@[simp] theorem toDiagR_mk (a : FreeAlgebra k (KLR.Gen ν)) :
    toDiagR k Q ν (mk k Q ν a) = toDiagFree k Q ν a :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ a

@[simp] theorem toDiagR_e (i : Seq ν) : toDiagR k Q ν (e i) = E i := by
  rw [e, toDiagR_mk, toDiagFree_fe]

@[simp] theorem toDiagR_x (a : Fin m) : toDiagR k Q ν (x a) = X a := by
  rw [KLRAlgebra.x, toDiagR_mk, toDiagFree_fx]

@[simp] theorem toDiagR_ψ (j : ℕ) : toDiagR k Q ν (ψ j) = Ψ j := by
  rw [KLRAlgebra.ψ, toDiagR_mk, toDiagFree_fψ]

/-! ## From diagrams to the KLR algebra -/

theorem Tgt.sum_val {a b : Tgt k Q ν} {α : Type*} (s : Finset α) (f : α → (a ⟶ b)) :
    (∑ t ∈ s, f t).1 = ∑ t ∈ s, (f t).1 := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons t s ht ih => rw [Finset.sum_cons, Finset.sum_cons, Tgt.add_val, ih]

/-- The value in `R(ν)` of a morphism `word i ⟶ word j` of the presented category. -/
abbrev evalV {i j : Seq ν} (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j))) :
    KLRAlgebra k Q ν :=
  ((evalFunctor k Q ν).map f).1

theorem evalV_mul_e {i j : Seq ν}
    (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j))) :
    evalV f * e i = evalV f := by
  rw [← ε_ob (k := k) (Q := Q) i]
  exact Tgt.val_mul_ε ((evalFunctor k Q ν).map f)

theorem e_mul_evalV {i j : Seq ν}
    (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j))) :
    e j * evalV f = evalV f := by
  rw [← ε_ob (k := k) (Q := Q) j]
  exact Tgt.ε_mul_val ((evalFunctor k Q ν).map f)

theorem evalV_mul_evalV_of_ne {i j j' l : Seq ν}
    (f : (pres k Q).obj (ob (word j)) ⟶ (pres k Q).obj (ob (word l)))
    (g : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j'))) (h : j ≠ j') :
    evalV f * evalV g = 0 := by
  rw [← evalV_mul_e f, ← e_mul_evalV g, mul_assoc, ← mul_assoc (e j), e_mul_e, if_neg h,
    zero_mul, mul_zero]

theorem evalV_comp {i j l : Seq ν}
    (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j)))
    (g : (pres k Q).obj (ob (word j)) ⟶ (pres k Q).obj (ob (word l))) :
    evalV (f ≫ g) = evalV g * evalV f := by
  rw [evalV, Functor.map_comp, Tgt.comp_val]

theorem evalV_diag {i j : Seq ν} (d : ob (word i) ⟶ ob (word j)) :
    evalV ((pres k Q).diag d) = evalL k Q ν (Diagram.layers d) * e i := by
  rw [evalV, evalFunctor_diag, ε_ob]

variable (k Q ν) in
/-- Evaluation of a matrix of diagrams, as a linear map. -/
def ofDiagRₗ : DiagR k Q ν →ₗ[k] KLRAlgebra k Q ν where
  toFun f := ∑ i, ∑ j, evalV (f i j)
  map_add' f g := by
    simp only [MatEnd.add_apply, evalV, Functor.map_add, Tgt.add_val, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [MatEnd.smul_apply, evalV, Functor.map_smul, Tgt.smul_val, Finset.smul_sum,
      RingHom.id_apply]

theorem ofDiagRₗ_apply (f : DiagR k Q ν) : ofDiagRₗ k Q ν f = ∑ i, ∑ j, evalV (f i j) := rfl

theorem ofDiagRₗ_single (i j : Seq ν)
    (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j))) :
    ofDiagRₗ k Q ν (single i j f) = evalV f := by
  rw [ofDiagRₗ_apply, Finset.sum_eq_single i, Finset.sum_eq_single j, single_apply_self]
  · intro l _ hl
    rw [single_apply_of_ne _ (fun h => hl h.2), evalV, Functor.map_zero, Tgt.zero_val]
  · simp
  · intro l _ hl
    refine Finset.sum_eq_zero fun l' _ => ?_
    rw [single_apply_of_ne _ (fun h => hl h.1), evalV, Functor.map_zero, Tgt.zero_val]
  · simp

theorem ofDiagRₗ_one : ofDiagRₗ k Q ν 1 = 1 := by
  rw [one_eq_sum_single, map_sum, ← sum_e (k := k) (Q := Q) (ν := ν)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofDiagRₗ_single, evalV, CategoryTheory.Functor.map_id, Tgt.id_val]
  exact ε_ob i

theorem ofDiagRₗ_mul (f g : DiagR k Q ν) :
    ofDiagRₗ k Q ν (f * g) = ofDiagRₗ k Q ν f * ofDiagRₗ k Q ν g := by
  have hsum : ∀ i l, evalV ((f * g) i l) = ∑ j, evalV (f j l) * evalV (g i j) := by
    intro i l
    rw [mul_apply, evalV, CategoryTheory.Functor.map_sum, Tgt.sum_val]
    exact Finset.sum_congr rfl fun j _ => evalV_comp _ _
  have h : ∀ i j', ∑ j, ∑ l, evalV (f j l) * evalV (g i j') =
      ∑ l, evalV (f j' l) * evalV (g i j') := by
    intro i j'
    rw [Finset.sum_eq_single j']
    · intro j _ hj
      exact Finset.sum_eq_zero fun l _ => evalV_mul_evalV_of_ne _ _ hj
    · simp
  simp only [ofDiagRₗ_apply, hsum, Finset.sum_mul, Finset.mul_sum, h]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

variable (k Q ν) in
/-- The comparison homomorphism `DiagR → R(ν)`, evaluating diagrams (soundness). -/
def ofDiagR : DiagR k Q ν →ₐ[k] KLRAlgebra k Q ν :=
  AlgHom.ofLinearMap (ofDiagRₗ k Q ν) ofDiagRₗ_one ofDiagRₗ_mul

theorem ofDiagR_single (i j : Seq ν)
    (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j))) :
    ofDiagR k Q ν (single i j f) = evalV f := ofDiagRₗ_single i j f

theorem ofDiagR_E (i : Seq ν) : ofDiagR k Q ν (E i) = e i := by
  rw [E_eq, ofDiagR_single, evalV, CategoryTheory.Functor.map_id, Tgt.id_val]
  exact ε_ob i

theorem ofDiagR_X (a : Fin m) : ofDiagR k Q ν (X a) = x a := by
  rw [X, map_sum, ← mul_one (x a), ← sum_e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofDiagR_single, dotE, evalV_diag, layers_dotD, evalL_cons, evalL_nil, one_mul, genL_lay,
    genAt_dot, length_take_word i a.2.le, xN_of_lt a.2]

theorem ofDiagR_Ψ (j : ℕ) : ofDiagR k Q ν (Ψ j) = ψ j := by
  by_cases h : j + 1 < m
  · rw [Ψ, map_sum, ← mul_one (ψ j), ← sum_e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofDiagR_single, crossE_def _ h, evalV_diag, layers_crossD, evalL_cons, evalL_nil,
      one_mul, genL_lay, genAt_cross, length_take_word i (by omega)]
  · rw [Ψ_of_le (by omega), map_zero, ψ_eq_zero j (by omega)]

theorem ofDiagR_comp_toDiagR : (ofDiagR k Q ν).comp (toDiagR k Q ν) = AlgHom.id k _ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext g
  simp only [Function.comp_apply, AlgHom.comp_toLinearMap, LinearMap.coe_comp,
    AlgHom.toLinearMap_apply, AlgHom.id_comp]
  change ofDiagR k Q ν (toDiagR k Q ν (mk k Q ν (FreeAlgebra.ι k g))) = mk k Q ν (FreeAlgebra.ι k g)
  cases g with
  | idem i => exact (congrArg _ (toDiagR_e i)).trans (ofDiagR_E i)
  | dot a => exact (congrArg _ (toDiagR_x a)).trans (ofDiagR_X a)
  | cross j => exact (congrArg _ (toDiagR_ψ j)).trans (ofDiagR_Ψ j)

theorem ofDiagR_toDiagR (r : KLRAlgebra k Q ν) : ofDiagR k Q ν (toDiagR k Q ν r) = r :=
  congrArg (fun φ : KLRAlgebra k Q ν →ₐ[k] KLRAlgebra k Q ν => φ r) ofDiagR_comp_toDiagR

theorem toDiagR_injective : Function.Injective (toDiagR k Q ν) :=
  Function.LeftInverse.injective ofDiagR_toDiagR

/-! ## Surjectivity: diagrams are generated by dots and crossings -/

variable (k Q ν) in
/-- The induction predicate for surjectivity of `toDiagR`: a morphism out of the word of a
sequence into a word that is not the word of a sequence vanishes, and a morphism between
words of sequences lies in the image of `toDiagR`. -/
def InImage {a b : Obj (sig I)} (f : (pres k Q).obj a ⟶ (pres k Q).obj b) : Prop :=
  (∀ i : Seq ν, a = ob (word i) → (∀ j : Seq ν, b ≠ ob (word j)) → f = 0) ∧
  ∀ (i j : Seq ν) (ha : a = ob (word i)) (hb : b = ob (word j)),
    (single i j (eqToHom (congrArg (pres k Q).obj ha.symm) ≫ f ≫
      eqToHom (congrArg (pres k Q).obj hb)) : DiagR k Q ν) ∈ (toDiagR k Q ν).range

theorem single_dotE_mem (i : Seq ν) (a : Fin m) :
    (single i i (dotE k Q i a) : DiagR k Q ν) ∈ (toDiagR k Q ν).range :=
  (AlgHom.mem_range _).2
    ⟨x a * e i, by rw [map_mul, toDiagR_x, toDiagR_e, E_eq, X_mul_single, Category.id_comp]⟩

theorem single_crossE_mem (i : Seq ν) (j : ℕ) :
    (single i (sadj m j • i) (crossE k Q i j) : DiagR k Q ν) ∈ (toDiagR k Q ν).range :=
  (AlgHom.mem_range _).2
    ⟨ψ j * e i, by rw [map_mul, toDiagR_ψ, toDiagR_e, E_eq, Ψ_mul_single, Category.id_comp]⟩

theorem inImage_layer (L : Layer (sig I)) (hv : L.Valid) :
    InImage k Q ν ((pres k Q).diag (Diagram.ofLayer L hv)) := by
  have key : ∀ i : Seq ν, L.dom = ob (word i) →
      ∃ j : Seq ν, L.cod = ob (word j) ∧ ∀ (hb : L.cod = ob (word j)) (ha : L.dom = ob (word i)),
        (single i j (eqToHom (congrArg (pres k Q).obj ha.symm) ≫
          (pres k Q).diag (Diagram.ofLayer L hv) ≫ eqToHom (congrArg (pres k Q).obj hb)) :
            DiagR k Q ν) ∈ (toDiagR k Q ν).range := by
    intro i ha
    have hw : word i = L.left ++ L.gen.dom ++ L.right := (congrArg Obj.word ha).symm
    obtain ⟨⟨⟩, l, g, r⟩ := L
    dsimp only at hw
    cases g with
    | dot c =>
      have hlen := length_eq_of_word hw
      simp only [Gen.dom_dot, List.length_singleton] at hlen
      have hp : l.length < m := by omega
      have h0 : i.1 ⟨l.length, hp⟩ = c := by
        simpa using apply_eq_of_word hw 0 (by simp) (by omega)
      have hL : (⟨(), l, .dot c, r⟩ : Layer (sig I)) =
          lay ((word i).take l.length) (.dot (i.1 ⟨l.length, hp⟩))
            ((word i).drop (l.length + 1)) :=
        eq_lay_of_dom _ (by rw [ha]; exact (word_split i ⟨l.length, hp⟩).symm)
          (by simp; omega) (by rw [h0])
      refine ⟨i, ha.trans (by rfl), fun hb ha' => ?_⟩
      rw [← diag_cast (Q := Q), show (pres k Q).diag (Diagram.cast (Diagram.ofLayer _ hv) ha' hb) =
        dotE k Q i ⟨l.length, hp⟩ from (pres k Q).diag_eq_of_layers_eq (by simp [hL])]
      exact single_dotE_mem i _
    | cross c d =>
      have hlen := length_eq_of_word hw
      simp only [Gen.dom_cross, List.length_cons, List.length_nil] at hlen
      have hp : l.length + 1 < m := by omega
      have h0 : i.1 ⟨l.length, by omega⟩ = c := by
        simpa using apply_eq_of_word hw 0 (by simp) (by omega)
      have h1 : i.1 ⟨l.length + 1, hp⟩ = d := by
        simpa using apply_eq_of_word hw 1 (by simp) (by omega)
      have hL : (⟨(), l, .cross c d, r⟩ : Layer (sig I)) =
          lay ((word i).take l.length) (.cross (i.1 ⟨l.length, by omega⟩) (i.1 ⟨l.length + 1, hp⟩))
            ((word i).drop (l.length + 2)) :=
        eq_lay_of_dom _ (by rw [ha]; exact (word_split₂ i hp).symm) (by simp; omega)
          (by rw [h0, h1])
      have hc : (Layer.cod ⟨(), l, .cross c d, r⟩ : Obj (sig I)) =
          ob (word (sadj m l.length • i)) := by
        rw [hL]; exact obj_ext (by rw [word_sadj i hp]; rfl)
      refine ⟨sadj m l.length • i, hc, fun hb ha' => ?_⟩
      rw [← diag_cast (Q := Q), show (pres k Q).diag (Diagram.cast (Diagram.ofLayer _ hv) ha' hb) =
        crossE k Q i l.length from by
          rw [crossE_def _ hp]; exact (pres k Q).diag_eq_of_layers_eq (by simp [hL])]
      exact single_crossE_mem i _
  refine ⟨fun i ha hne => ?_, fun i j ha hb => ?_⟩
  · obtain ⟨j, hj, -⟩ := key i ha
    exact absurd hj (hne j)
  · obtain ⟨j', hj', hmem⟩ := key i ha
    obtain rfl : j = j' := word_injective (by rw [← ob_word (word j), ← hb, hj', ob_word])
    exact hmem hb ha

theorem inImage {a b : Obj (sig I)} (f : (pres k Q).obj a ⟶ (pres k Q).obj b) :
    InImage k Q ν f := by
  induction f using (pres k Q).hom_induction_layers with
  | nil h =>
    rename_i a b
    subst h
    refine ⟨fun i ha hne => absurd ha (hne i), fun i j ha hb => ?_⟩
    obtain rfl : i = j := word_injective (by rw [← ob_word (word i), ← ha, hb, ob_word])
    subst ha
    simp only [eqToHom_refl, Presentation.diag_id, Category.id_comp]
    exact (AlgHom.mem_range _).2 ⟨e i, by rw [toDiagR_e, E_eq]⟩
  | layer L hv => exact inImage_layer L hv
  | comp f g hf hg =>
    rename_i a b c
    refine ⟨fun i ha hne => ?_, fun i l ha hc => ?_⟩
    · by_cases hb : ∃ j : Seq ν, b = ob (word j)
      · obtain ⟨j, hj⟩ := hb
        rw [hg.1 j hj hne, Limits.comp_zero]
      · rw [hf.1 i ha (fun j hj => hb ⟨j, hj⟩), Limits.zero_comp]
    · by_cases hb : ∃ j : Seq ν, b = ob (word j)
      · obtain ⟨j, hj⟩ := hb
        have e : eqToHom (congrArg (pres k Q).obj ha.symm) ≫ (f ≫ g) ≫
            eqToHom (congrArg (pres k Q).obj hc) =
            (eqToHom (congrArg (pres k Q).obj ha.symm) ≫ f ≫ eqToHom (congrArg (pres k Q).obj hj)) ≫
              (eqToHom (congrArg (pres k Q).obj hj.symm) ≫ g ≫
                eqToHom (congrArg (pres k Q).obj hc)) := by
          simp
        rw [e, ← single_mul_single]
        exact Subalgebra.mul_mem _ (hg.2 j l hj hc) (hf.2 i j ha hj)
      · rw [hf.1 i ha (fun j hj => hb ⟨j, hj⟩), Limits.zero_comp, Limits.zero_comp,
          Limits.comp_zero, single_zero]
        exact Subalgebra.zero_mem _
  | zero =>
    refine ⟨fun _ _ _ => rfl, fun i j ha hb => ?_⟩
    rw [Limits.zero_comp, Limits.comp_zero, single_zero]
    exact Subalgebra.zero_mem _
  | add f g hf hg =>
    refine ⟨fun i ha hne => by rw [hf.1 i ha hne, hg.1 i ha hne, add_zero], fun i j ha hb => ?_⟩
    rw [Preadditive.add_comp, Preadditive.comp_add, single_add]
    exact Subalgebra.add_mem _ (hf.2 i j ha hb) (hg.2 i j ha hb)
  | smul r f hf =>
    refine ⟨fun i ha hne => by rw [hf.1 i ha hne, smul_zero], fun i j ha hb => ?_⟩
    rw [Linear.smul_comp, Linear.comp_smul, single_smul]
    exact Subalgebra.smul_mem _ (hf.2 i j ha hb) r

theorem single_mem_range (i j : Seq ν)
    (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j))) :
    (single i j f : DiagR k Q ν) ∈ (toDiagR k Q ν).range := by
  simpa using (inImage f).2 i j rfl rfl

theorem toDiagR_surjective : Function.Surjective (toDiagR k Q ν) := by
  intro M
  have : M ∈ (toDiagR k Q ν).range := by
    rw [eq_sum_single M]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => single_mem_range i j _
  exact (AlgHom.mem_range _).1 this

/-! ## The isomorphism -/

theorem toDiagR_comp_ofDiagR : (toDiagR k Q ν).comp (ofDiagR k Q ν) = AlgHom.id k _ := by
  ext M
  obtain ⟨r, rfl⟩ := toDiagR_surjective M
  simp [ofDiagR_toDiagR]

variable (k Q ν) in
/-- **The diagrammatic KLR algebra is the KLR algebra.** For any commutative ring `k`, any
`Q : I → I → k[u, v]` and any weight `ν`, the algebra `⨁_{i, j ∈ Seq ν} Hom(word i, word j)`
of the category presented by dots and crossings coloured by `I`, subject to the local KLR
relations (KL I (2.3)–(2.8), KL II §3) and the interchange law, is isomorphic to
`KLRAlgebra k Q ν`, via `e i ↦` identity of `i`, `x a ↦` dot on strand `a`, `ψ j ↦` crossing
of strands `j`, `j + 1`. -/
def diagREquiv : KLRAlgebra k Q ν ≃ₐ[k] DiagR k Q ν :=
  AlgEquiv.ofAlgHom (toDiagR k Q ν) (ofDiagR k Q ν) toDiagR_comp_ofDiagR ofDiagR_comp_toDiagR

@[simp] theorem diagREquiv_apply (r : KLRAlgebra k Q ν) :
    diagREquiv k Q ν r = toDiagR k Q ν r := rfl

@[simp] theorem diagREquiv_symm_apply (M : DiagR k Q ν) :
    (diagREquiv k Q ν).symm M = ofDiagR k Q ν M := rfl

theorem diagREquiv_e (i : Seq ν) : diagREquiv k Q ν (e i) = E i := toDiagR_e i
theorem diagREquiv_x (a : Fin m) : diagREquiv k Q ν (x a) = X a := toDiagR_x a
theorem diagREquiv_ψ (j : ℕ) : diagREquiv k Q ν (ψ j) = Ψ j := toDiagR_ψ j

/-- Each Hom space `Hom(word i, word j)` of the presented category is the corner
`e_j R(ν) e_i` (evaluation is injective on it). -/
theorem evalV_injective (i j : Seq ν) :
    Function.Injective (evalV (k := k) (Q := Q) (i := i) (j := j)) := by
  intro f g h
  have hf := ofDiagR_single (k := k) (Q := Q) i j f
  have hg := ofDiagR_single (k := k) (Q := Q) i j g
  have : (single i j f : DiagR k Q ν) = single i j g :=
    (diagREquiv k Q ν).symm.injective
      (by rw [diagREquiv_symm_apply, diagREquiv_symm_apply, hf, hg, h])
  simpa using congrArg (fun M : DiagR k Q ν => M i j) this

/-! ## Faithfulness: the basis theorem for diagrams -/

section Basis

open Equiv MvPolynomial

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
  (hρ : ∀ w, TypeA.IsReduced (Multiset.card ν) (ρ w) ∧ TypeA.wordProd (Multiset.card ν) (ρ w) = w)

/-- **KL I, Theorem 2.5, diagrammatically.** The diagrams `ψ_{ρ w} x^u 1_i` form a `k`-basis
of the diagrammatic KLR algebra. -/
noncomputable def diagBasis : Basis (Seq ν × Perm (Fin m) × (Fin m →₀ ℕ)) k (DiagR k Q ν) :=
  (KLRAlgebra.basis hPQ hP ρ hρ).map (diagREquiv k Q ν).toLinearEquiv

theorem diagBasis_apply (b : Seq ν × Perm (Fin m) × (Fin m →₀ ℕ)) :
    diagBasis hPQ hP ρ hρ b =
      toDiagR k Q ν (ψw (ρ b.2.1)) * toDiagR k Q ν (pol (monomial b.2.2 1)) * E b.1 := by
  simp [diagBasis, KLRAlgebra.basis_apply]

end Basis

end Categorification.KLR.Diagram

end
