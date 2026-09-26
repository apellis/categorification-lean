/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.Basic
import Categorification.Diagrams.KLR.MatEnd

/-!
# The diagrammatic algebra `R(ν)`

For a weight `ν`, the diagrammatic KLR algebra is `⨁_{i, j ∈ Seq ν} Hom(i, j)`, the
morphisms of the presented category `pres k Q` between the objects given by sequences of
weight `ν`, with multiplication given by composition (`DiagR k Q ν`, a `MatEnd`).

## Main definitions

* `word i`: the list of colours of a sequence `i`.
* `dotE i a`, `crossE i j`: a dot on strand `a`, and the crossing of strands `j` and `j + 1`,
  on the object `word i`.
* `DiagR k Q ν`, with elements `E i` (identity of `word i`), `X a` (a dot on strand `a`,
  summed over all sequences) and `Ψ j` (the crossing of strands `j`, `j + 1`, summed over all
  sequences, zero if out of range).
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory StringDiagrams TypeA

universe u

variable {I : Type u} {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- Closes the side goals `(l.take p).length = p` of the positional relations. -/
macro "len_tac" : tactic => `(tactic| first | (simp; done) | (simp; omega))

/-! ## Words of sequences -/

/-- The list of colours `i₁ ⋯ i_m` of a sequence. -/
def word (i : Seq ν) : List I := List.ofFn i.1

@[simp] theorem length_word (i : Seq ν) : (word i).length = m := by simp [word]

@[simp] theorem getElem_word (i : Seq ν) (t : ℕ) (h : t < (word i).length) :
    (word i)[t] = i.1 ⟨t, by simpa using h⟩ := by
  simp [word]

theorem word_injective : Function.Injective (word (ν := ν)) := by
  intro i j h
  exact Subtype.ext (List.ofFn_injective h)

theorem take_append_drop_get {α : Type*} (l : List α) (p : ℕ) (h : p < l.length) :
    l.take p ++ [l[p]] ++ l.drop (p + 1) = l := by
  rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop, List.take_append_drop]

theorem take_append_drop_get₂ {α : Type*} (l : List α) (p : ℕ) (h : p + 1 < l.length) :
    l.take p ++ [l[p], l[p + 1]] ++ l.drop (p + 2) = l := by
  rw [List.append_assoc, List.cons_append, List.singleton_append, List.getElem_cons_drop,
    List.getElem_cons_drop, List.take_append_drop]

theorem sadj_symm (n j : ℕ) : (sadj n j).symm = sadj n j := by
  rw [← Equiv.Perm.inv_def, sadj_inv]

@[simp] theorem sadj_smul_apply (i : Seq ν) (j : ℕ) (a : Fin m) :
    (sadj m j • i).1 a = i.1 (sadj m j a) := by
  rw [Seq.smul_apply, sadj_symm]

theorem word_split (i : Seq ν) (a : Fin m) :
    (word i).take a ++ [i.1 a] ++ (word i).drop (a + 1) = word i := by
  have := take_append_drop_get (word i) a (by simp)
  simp only [getElem_word] at this
  exact this

theorem word_split₂ (i : Seq ν) {j : ℕ} (h : j + 1 < m) :
    (word i).take j ++ [i.1 ⟨j, by omega⟩, i.1 ⟨j + 1, h⟩] ++ (word i).drop (j + 2) =
      word i := by
  have := take_append_drop_get₂ (word i) j (by simpa using h)
  simp only [getElem_word] at this
  exact this

/-- The word of `s_j • i` is that of `i` with the letters at positions `j`, `j + 1`
exchanged. -/
theorem word_sadj (i : Seq ν) {j : ℕ} (h : j + 1 < m) :
    word (sadj m j • i) =
      (word i).take j ++ [i.1 ⟨j + 1, h⟩, i.1 ⟨j, by omega⟩] ++ (word i).drop (j + 2) := by
  apply List.ext_getElem
  · simp only [length_word, List.length_append, List.length_take, List.length_cons,
      List.length_nil, List.length_drop]
    omega
  · intro t h₁ h₂
    have ht : t < m := by simpa using h₁
    have hl : ((word i).take j ++ [i.1 ⟨j + 1, h⟩, i.1 ⟨j, by omega⟩]).length = j + 2 := by
      simp only [List.length_append, List.length_take, length_word, List.length_cons,
        List.length_nil]
      omega
    rw [getElem_word, sadj_smul_apply, List.getElem_append]
    rcases swapNat_cases j t with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨h₁', h₂', -⟩
    · rw [dif_pos (by omega), List.getElem_append_right (by simp)]
      simp only [List.length_take, length_word, show min t m = t by omega, Nat.sub_self,
        List.getElem_cons_zero]
      rw [sadj_apply_left h]
    · rw [dif_pos (by omega), List.getElem_append_right (by simp)]
      simp only [List.length_take, length_word, show min j m = j by omega,
        show j + 1 - j = 1 by omega, List.getElem_cons_succ, List.getElem_cons_zero]
      rw [sadj_apply_right h]
    · rw [sadj_apply_of_ne _ h₁' h₂']
      rcases Nat.lt_or_ge t j with hlt | hge
      · rw [dif_pos (by omega), List.getElem_append_left (by len_tac)]
        simp
      · rw [dif_neg (by rw [hl]; omega)]
        simp only [List.getElem_drop, getElem_word, List.length_append, List.length_take,
          length_word, List.length_cons, List.length_nil]
        exact congrArg i.1 (Fin.ext (by simp only; omega))

theorem sadj_smul_eq_self (i : Seq ν) {j : ℕ} (h : j + 1 < m)
    (he : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩) : sadj m j • i = i := by
  apply Subtype.ext
  funext t
  rw [sadj_smul_apply]
  rcases swapNat_cases j t with ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨h₁, h₂, -⟩
  · rw [show t = ⟨j, by omega⟩ from Fin.ext h₁, sadj_apply_left h]; exact he.symm
  · rw [show t = ⟨j + 1, h⟩ from Fin.ext h₁, sadj_apply_right h]; exact he
  · rw [sadj_apply_of_ne _ h₁ h₂]

theorem sadj_smul_val (i : Seq ν) {j t : ℕ} (hj : j + 1 < m) (ht : t < m) :
    (sadj m j • i).1 ⟨t, ht⟩ = i.1 ⟨swapNat j t, by
      rcases swapNat_cases j t with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, -, h⟩ <;> omega⟩ := by
  rw [sadj_smul_apply]
  exact congrArg i.1 (Fin.ext (sadj_val_of_lt hj _))

theorem sadj_smul_injective (j : ℕ) : Function.Injective (sadj m j • · : Seq ν → Seq ν) :=
  MulAction.injective _

@[simp] theorem sadj_smul_sadj_smul (i : Seq ν) (j : ℕ) : sadj m j • sadj m j • i = i := by
  rw [← mul_smul, sadj_mul_self, one_smul]

theorem sadj_braid_smul (i : Seq ν) {j : ℕ} (h : j + 2 < m) :
    sadj m (j + 1) • sadj m j • sadj m (j + 1) • i = sadj m j • sadj m (j + 1) • sadj m j • i := by
  simp only [← mul_smul, ← mul_assoc]
  rw [sadj_braid h]

theorem sadj_braid_smul_eq_self (i : Seq ν) {j : ℕ} (h : j + 2 < m)
    (he : i.1 ⟨j, by omega⟩ = i.1 ⟨j + 2, h⟩) :
    sadj m j • sadj m (j + 1) • sadj m j • i = i := by
  have h1 : j + 1 < m := by omega
  have h2 : j + 1 + 1 < m := by omega
  apply Subtype.ext
  funext t
  simp only [sadj_smul_apply]
  have key : ((sadj m j (sadj m (j + 1) (sadj m j t)) : Fin m) : ℕ) =
      swapNat j (swapNat (j + 1) (swapNat j t)) := by
    rw [sadj_val_of_lt h1, sadj_val_of_lt h2, sadj_val_of_lt h1]
  have hv : ∀ u v : Fin m, (u : ℕ) = v → i.1 u = i.1 v := fun u v huv => congrArg _ (Fin.ext huv)
  by_cases ht : (t : ℕ) = j
  · rw [hv _ ⟨j + 2, h⟩ (by rw [key]; simp only [swapNat, ht]; split_ifs <;> omega), ← he]
    exact hv _ _ ht.symm
  · by_cases ht' : (t : ℕ) = j + 2
    · rw [hv _ ⟨j, by omega⟩ (by rw [key]; simp only [swapNat, ht']; split_ifs <;> omega), he]
      exact hv _ _ ht'.symm
    · exact hv _ _ (by rw [key]; unfold swapNat; split_ifs <;> omega)

/-! ## Dots and crossings on the object of a sequence -/

/-- A dot on strand `a` of the object `word i`, in the free 2-category. -/
def dotD (i : Seq ν) (a : Fin m) : ob (word i) ⟶ ob (word i) :=
  dl ((word i).take a) (.dot (i.1 a)) ((word i).drop (a + 1)) (word_split i a) (word_split i a)

/-- The crossing of strands `j` and `j + 1` of the object `word i`, in the free 2-category. -/
def crossD (i : Seq ν) {j : ℕ} (h : j + 1 < m) : ob (word i) ⟶ ob (word (sadj m j • i)) :=
  dl ((word i).take j) (.cross (i.1 ⟨j, by omega⟩) (i.1 ⟨j + 1, h⟩)) ((word i).drop (j + 2))
    (word_split₂ i h) (by rw [word_sadj i h]; rfl)

@[simp] theorem layers_dotD (i : Seq ν) (a : Fin m) :
    Diagram.layers (dotD i a) =
      [lay ((word i).take a) (.dot (i.1 a)) ((word i).drop (a + 1))] := rfl

@[simp] theorem layers_crossD (i : Seq ν) {j : ℕ} (h : j + 1 < m) :
    Diagram.layers (crossD i h) =
      [lay ((word i).take j) (.cross (i.1 ⟨j, by omega⟩) (i.1 ⟨j + 1, h⟩))
        ((word i).drop (j + 2))] := rfl

variable (k Q) in
/-- A dot on strand `a` of the object `word i`. -/
def dotE (i : Seq ν) (a : Fin m) : End ((pres k Q).obj (ob (word i))) :=
  (pres k Q).diag (dotD i a)

variable (k Q) in
/-- The crossing of strands `j` and `j + 1` of the object `word i` (zero if `j + 1 ≥ m`). -/
def crossE (i : Seq ν) (j : ℕ) :
    (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word (sadj m j • i))) :=
  if h : j + 1 < m then (pres k Q).diag (crossD i h) else 0

theorem crossE_def (i : Seq ν) {j : ℕ} (h : j + 1 < m) :
    crossE k Q i j = (pres k Q).diag (crossD i h) := dif_pos h

theorem crossE_of_le (i : Seq ν) {j : ℕ} (h : m ≤ j + 1) : crossE k Q i j = 0 :=
  dif_neg (by omega)

theorem diag_eqToHom {a b : Obj (sig I)} (h : a = b) :
    (pres k Q).diag (eqToHom h) = eqToHom (congrArg (pres k Q).obj h) := by
  subst h; exact (pres k Q).diag_id _

theorem diag_cast {a b a' b' : Obj (sig I)} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    (pres k Q).diag (Diagram.cast f ha hb) =
      eqToHom (congrArg (pres k Q).obj ha.symm) ≫ (pres k Q).diag f ≫
        eqToHom (congrArg (pres k Q).obj hb) := by
  subst ha hb; simp

theorem diag_comp_eqToHom {a b b' : Obj (sig I)} (f : a ⟶ b) (h : b = b')
    {h' : (pres k Q).obj b = (pres k Q).obj b'} :
    (pres k Q).diag f ≫ eqToHom h' = (pres k Q).diag (Diagram.cast f rfl h) := by
  subst h; simp

theorem length_take_word (i : Seq ν) {t : ℕ} (h : t ≤ m) : ((word i).take t).length = t := by
  simp; omega

/-! ## The algebra `DiagR` -/

variable [DecidableEq I]

variable (k Q ν) in
/-- The diagrammatic KLR algebra `⨁_{i, j ∈ Seq ν} Hom(word i, word j)`. -/
abbrev DiagR : Type _ := MatEnd (fun i : Seq ν => (pres k Q).obj (ob (word i)))

namespace DiagR

open MatEnd

/-- The identity diagram of the sequence `i`. -/
def E (i : Seq ν) : DiagR k Q ν := single i i (𝟙 _)

/-- A dot on strand `a`, summed over all sequences. -/
def X (a : Fin m) : DiagR k Q ν := ∑ i, single i i (dotE k Q i a)

/-- The crossing of strands `j` and `j + 1`, summed over all sequences (zero if
`j + 1 ≥ m`). -/
def Ψ (j : ℕ) : DiagR k Q ν := ∑ i, single i (sadj m j • i) (crossE k Q i j)

variable {i j l : Seq ν}

theorem E_mul_single_self (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j))) :
    (E j : DiagR k Q ν) * single i j f = single i j f := by
  rw [E, single_mul_single, Category.comp_id]

theorem E_mul_single_of_ne
    (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j))) (h : j ≠ l) :
    (E l : DiagR k Q ν) * single i j f = 0 :=
  single_mul_single_of_ne _ _ h

theorem X_mul_single (a : Fin m)
    (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j))) :
    (X a : DiagR k Q ν) * single i j f = single i j (f ≫ dotE k Q j a) := by
  rw [X, Finset.sum_mul, Finset.sum_eq_single j, single_mul_single]
  · intro l _ hl; exact single_mul_single_of_ne _ _ (Ne.symm hl)
  · simp

theorem Ψ_mul_single (t : ℕ)
    (f : (pres k Q).obj (ob (word i)) ⟶ (pres k Q).obj (ob (word j))) :
    (Ψ t : DiagR k Q ν) * single i j f = single i (sadj m t • j) (f ≫ crossE k Q j t) := by
  rw [Ψ, Finset.sum_mul, Finset.sum_eq_single j, single_mul_single]
  · intro l _ hl; exact single_mul_single_of_ne _ _ (Ne.symm hl)
  · simp

theorem E_eq (i : Seq ν) : (E i : DiagR k Q ν) = single i i (𝟙 _) := rfl

theorem E_mul_E (i j : Seq ν) : (E i * E j : DiagR k Q ν) = if i = j then E i else 0 := by
  split_ifs with h
  · subst h; exact E_mul_single_self _
  · exact E_mul_single_of_ne _ (Ne.symm h)

theorem sum_E : (∑ i, E i : DiagR k Q ν) = 1 := (one_eq_sum_single).symm

theorem ext_E {f g : DiagR k Q ν} (h : ∀ i, f * E i = g * E i) : f = g := by
  rw [← mul_one f, ← mul_one g, ← sum_E, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i

theorem X_mul_E (a : Fin m) (i : Seq ν) : (X a * E i : DiagR k Q ν) = E i * X a := by
  rw [E_eq, X_mul_single, Category.id_comp, X, Finset.mul_sum, Finset.sum_eq_single i,
    ← E_eq, E_mul_single_self]
  · intro l _ hl; exact E_mul_single_of_ne _ hl
  · simp

theorem Ψ_mul_E (t : ℕ) (i : Seq ν) :
    (Ψ t * E i : DiagR k Q ν) = E (sadj m t • i) * Ψ t := by
  rw [E_eq i, Ψ_mul_single, Category.id_comp, Ψ, Finset.mul_sum, Finset.sum_eq_single i,
    E_mul_single_self]
  · intro l _ hl; exact E_mul_single_of_ne _ (fun h => hl (sadj_smul_injective t h))
  · simp

theorem Ψ_of_le {t : ℕ} (h : m ≤ t + 1) : (Ψ t : DiagR k Q ν) = 0 := by
  simp [Ψ, crossE_of_le _ h]

/-! ### Isotopy relations, from the interchange law -/

omit [DecidableEq I] in
theorem dotE_comm (i : Seq ν) (a b : Fin m) :
    dotE k Q i a ≫ dotE k Q i b = dotE k Q i b ≫ dotE k Q i a := by
  wlog hab : a < b generalizing a b
  · rcases lt_or_eq_of_le (not_lt.1 hab) with h | rfl
    · exact (this b a h).symm
    · rfl
  simp only [dotE, ← Presentation.diag_comp]
  exact interchange_pos Q (g := .dot (i.1 a)) (h := .dot (i.1 b)) (p := a) (q := b)
    (by simp [Gen.arity]; omega) _ _ rfl rfl
    (by len_tac) rfl (by len_tac) rfl (by len_tac) rfl (by len_tac) rfl

theorem X_mul_X (a b : Fin m) : (X a * X b : DiagR k Q ν) = X b * X a := by
  refine ext_E fun i => ?_
  simp only [mul_assoc, E_eq, X_mul_single, Category.id_comp, dotE_comm]

omit [DecidableEq I] in
theorem crossE_comm (i : Seq ν) {j l : ℕ} (h : j + 1 < l)
    (hs : sadj m j • sadj m l • i = sadj m l • sadj m j • i) :
    crossE k Q i j ≫ crossE k Q (sadj m j • i) l =
      crossE k Q i l ≫ crossE k Q (sadj m l • i) j ≫ eqToHom (by rw [hs]) := by
  by_cases hl : l + 1 < m
  · have hj : j + 1 < m := by omega
    simp only [crossE_def _ hj, crossE_def _ hl]
    rw [← Category.assoc, ← Presentation.diag_comp, ← Presentation.diag_comp,
      diag_comp_eqToHom _ (congrArg (fun s => ob (word s)) hs)]
    have h1 : l ≠ j := by omega
    have h2 : l ≠ j + 1 := by omega
    have h3 : l + 1 ≠ j := by omega
    have h4 : l + 1 ≠ j + 1 := by omega
    have h5 : j ≠ l := by omega
    have h6 : j ≠ l + 1 := by omega
    have h7 : j + 1 ≠ l := by omega
    have h8 : j + 1 ≠ l + 1 := by omega
    exact interchange_pos Q (g := .cross (i.1 ⟨j, by omega⟩) (i.1 ⟨j + 1, hj⟩))
      (h := .cross (i.1 ⟨l, by omega⟩) (i.1 ⟨l + 1, hl⟩)) (p := j) (q := l)
      (by simp [Gen.arity]; omega) _ _ rfl rfl
      (by len_tac) rfl (by len_tac) (by simp [sadj_symm, sadj_apply_of_ne, h1, h2, h3, h4])
      (by len_tac) rfl (by len_tac) (by simp [sadj_symm, sadj_apply_of_ne, h5, h6, h7, h8])
  · rw [crossE_of_le _ (show m ≤ l + 1 by omega), crossE_of_le _ (show m ≤ l + 1 by omega)]
    simp

theorem Ψ_mul_Ψ {j l : ℕ} (h : j + 1 < l) : (Ψ j * Ψ l : DiagR k Q ν) = Ψ l * Ψ j := by
  refine ext_E fun i => ?_
  have hs : sadj m j • sadj m l • i = sadj m l • sadj m j • i := by
    rw [← mul_smul, ← mul_smul, sadj_comm m (Or.inl h)]
  simp only [mul_assoc, E_eq, Ψ_mul_single, Category.id_comp]
  rw [crossE_comm i h hs, ← Category.assoc, single_eqToHom _ hs]

omit [DecidableEq I] in
theorem dotE_crossE (i : Seq ν) (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    dotE k Q i a ≫ crossE k Q i j = crossE k Q i j ≫ dotE k Q (sadj m j • i) a := by
  by_cases hj : j + 1 < m
  · have ha : (sadj m j • i).1 a = i.1 a := by
      rw [sadj_smul_apply, sadj_apply_of_ne _ h₁ h₂]
    simp only [crossE_def _ hj, dotE, ← Presentation.diag_comp]
    rcases Nat.lt_or_gt_of_ne h₁ with hlt | hgt
    · exact interchange_pos Q (g := .dot (i.1 a))
        (h := .cross (i.1 ⟨j, by omega⟩) (i.1 ⟨j + 1, hj⟩)) (p := a) (q := j)
        (by simp [Gen.arity]; omega) _ _ rfl rfl
        (by len_tac) rfl (by len_tac) rfl (by len_tac) rfl (by len_tac)
        (by simp [ha])
    · exact (interchange_pos Q (g := .cross (i.1 ⟨j, by omega⟩) (i.1 ⟨j + 1, hj⟩))
        (h := .dot (i.1 a)) (p := j) (q := a)
        (by simp [Gen.arity]; omega) _ _ rfl rfl
        (by len_tac) rfl (by len_tac) (by simp [ha]) (by len_tac) rfl
        (by len_tac) rfl).symm
  · simp [crossE_of_le _ (show m ≤ j + 1 by omega)]

theorem X_mul_Ψ (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    (X a * Ψ j : DiagR k Q ν) = Ψ j * X a := by
  refine ext_E fun i => ?_
  simp only [mul_assoc, E_eq, X_mul_single, Ψ_mul_single, Category.id_comp,
    dotE_crossE i a j h₁ h₂]

/-! ### The local relations -/

theorem single_ncEval (i : Seq ν) {n : ℕ} (a : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    single i i (ncEval (A := End ((pres k Q).obj (ob (word i)))) (fun t => dotE k Q i (a t)) p) =
      ncEval (fun t => (X (a t) : DiagR k Q ν)) p * E i := by
  let φ : End ((pres k Q).obj (ob (word i))) →ₗ[k] DiagR k Q ν :=
    singleₗ (X := fun i : Seq ν => (pres k Q).obj (ob (word i))) k i i
  refine ncEval_of_mul φ (fun f g => ?_) (e := E i) rfl _ _ (fun t => ?_) (fun t => X_mul_E _ i) p
  · show (single i i (g ≫ f) : DiagR k Q ν) = single i i f * single i i g
    rw [single_mul_single]
  · show (single i i (dotE k Q i (a t)) : DiagR k Q ν) = _
    rw [E_eq, X_mul_single, Category.id_comp]

theorem dot_cross_left {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    ((X ⟨j, by omega⟩ * Ψ j - Ψ j * X ⟨j + 1, h⟩) * E i : DiagR k Q ν) =
      if i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩ then E i else 0 := by
  simp only [sub_mul, mul_assoc, E_eq, X_mul_single, Ψ_mul_single, Category.id_comp,
    ← single_sub]
  rw [crossE_def _ h, dotE, dotE, ← Presentation.diag_comp, ← Presentation.diag_comp]
  split_ifs with he
  · have hs := sadj_smul_eq_self i h he
    rw [← single_eqToHom _ hs, Preadditive.sub_comp,
      diag_comp_eqToHom _ (congrArg (fun s => ob (word s)) hs),
      diag_comp_eqToHom _ (congrArg (fun s => ob (word s)) hs)]
    refine congrArg (single i i) ?_
    refine slideLEq_pos Q (p := j) (c := i.1 ⟨j, by omega⟩)
      (Diagram.cast (crossD i h ≫ dotD (sadj m j • i) ⟨j, by omega⟩) rfl
        (congrArg (fun s => ob (word s)) hs))
      (Diagram.cast (dotD i ⟨j + 1, h⟩ ≫ crossD i h) rfl (congrArg (fun s => ob (word s)) hs))
      rfl ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_
    all_goals first | len_tac | simp [he, hs]
  · rw [slideLNe_pos Q he (p := j) (crossD i h ≫ dotD (sadj m j • i) ⟨j, by omega⟩)
      (dotD i ⟨j + 1, h⟩ ≫ crossD i h) rfl (by len_tac) rfl (by len_tac)
      (by simp [sadj_symm, sadj_apply_left h]) rfl (by len_tac) rfl (by len_tac) rfl,
      sub_self, single_zero]

theorem dot_cross_right {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    ((Ψ j * X ⟨j, by omega⟩ - X ⟨j + 1, h⟩ * Ψ j) * E i : DiagR k Q ν) =
      if i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩ then E i else 0 := by
  simp only [sub_mul, mul_assoc, E_eq, X_mul_single, Ψ_mul_single, Category.id_comp,
    ← single_sub]
  rw [crossE_def _ h, dotE, dotE, ← Presentation.diag_comp, ← Presentation.diag_comp]
  split_ifs with he
  · have hs := sadj_smul_eq_self i h he
    rw [← single_eqToHom _ hs, Preadditive.sub_comp,
      diag_comp_eqToHom _ (congrArg (fun s => ob (word s)) hs),
      diag_comp_eqToHom _ (congrArg (fun s => ob (word s)) hs)]
    refine congrArg (single i i) ?_
    refine slideREq_pos Q (p := j) (c := i.1 ⟨j, by omega⟩)
      (Diagram.cast (dotD i ⟨j, by omega⟩ ≫ crossD i h) rfl (congrArg (fun s => ob (word s)) hs))
      (Diagram.cast (crossD i h ≫ dotD (sadj m j • i) ⟨j + 1, h⟩) rfl
        (congrArg (fun s => ob (word s)) hs))
      rfl ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_ ?_
    all_goals first | len_tac | simp [he, hs]
  · rw [slideRNe_pos Q he (p := j) (dotD i ⟨j, by omega⟩ ≫ crossD i h)
      (crossD i h ≫ dotD (sadj m j • i) ⟨j + 1, h⟩) rfl (by len_tac) rfl (by len_tac) rfl
      rfl (by len_tac) rfl (by len_tac) (by simp [sadj_symm, sadj_apply_right h]),
      sub_self, single_zero]

theorem cross_sq {j : ℕ} (h : j + 1 < m) (i : Seq ν) :
    (Ψ j * Ψ j * E i : DiagR k Q ν) =
      if i.1 ⟨j, by omega⟩ = i.1 ⟨j + 1, h⟩ then 0 else
        ncEval ![X ⟨j, by omega⟩, X ⟨j + 1, h⟩] (Q (i.1 ⟨j, by omega⟩) (i.1 ⟨j + 1, h⟩)) *
          E i := by
  have hs : sadj m j • sadj m j • i = i := sadj_smul_sadj_smul i j
  simp only [mul_assoc, E_eq, Ψ_mul_single, Category.id_comp]
  rw [← single_eqToHom _ hs, crossE_def _ h, crossE_def _ h, ← Presentation.diag_comp,
    diag_comp_eqToHom _ (congrArg (fun s => ob (word s)) hs)]
  split_ifs with he
  · rw [sqEq_pos Q (p := j) (c := i.1 ⟨j, by omega⟩)
      (Diagram.cast (crossD i h ≫ crossD (sadj m j • i) h) rfl
        (congrArg (fun s => ob (word s)) hs)) rfl (by len_tac) (by simp [he]) (by len_tac)
      (by simp [he, sadj_symm, sadj_apply_left h, sadj_apply_right h]), single_zero]
  · rw [sqNe_pos Q he (p := j)
      (Diagram.cast (crossD i h ≫ crossD (sadj m j • i) h) rfl
        (congrArg (fun s => ob (word s)) hs)) (dotD i ⟨j, by omega⟩) (dotD i ⟨j + 1, h⟩)
      rfl (by len_tac) rfl (by len_tac)
      (by simp [sadj_symm, sadj_apply_left h, sadj_apply_right h]) rfl (by len_tac) rfl rfl
      (by len_tac) rfl]
    have e₁ : (![(pres k Q).diag (dotD i ⟨j, by omega⟩), (pres k Q).diag (dotD i ⟨j + 1, h⟩)] :
        Fin 2 → End ((pres k Q).obj (ob (word i)))) =
        fun t => dotE k Q i (![⟨j, by omega⟩, ⟨j + 1, h⟩] t) := by
      funext t; fin_cases t <;> rfl
    have e₂ : (![X ⟨j, by omega⟩, X ⟨j + 1, h⟩] : Fin 2 → DiagR k Q ν) =
        fun t => X (![⟨j, by omega⟩, ⟨j + 1, h⟩] t) := by
      funext t; fin_cases t <;> rfl
    rw [e₁, single_ncEval, e₂, E_eq]

theorem braid {j : ℕ} (h : j + 2 < m) (i : Seq ν) :
    ((Ψ j * Ψ (j + 1) * Ψ j - Ψ (j + 1) * Ψ j * Ψ (j + 1)) * E i : DiagR k Q ν) =
      if i.1 ⟨j, by omega⟩ = i.1 ⟨j + 2, h⟩ ∧ i.1 ⟨j, by omega⟩ ≠ i.1 ⟨j + 1, by omega⟩ then
        ncEval ![X ⟨j, by omega⟩, X ⟨j + 1, by omega⟩, X ⟨j + 2, h⟩]
          (qbar (Q (i.1 ⟨j, by omega⟩) (i.1 ⟨j + 1, by omega⟩))) * E i
      else 0 := by
  have h1 : j + 1 < m := by omega
  have h2 : j + 1 + 1 < m := by omega
  have hb := sadj_braid_smul i h
  have e₂ : (⟨j + 1 + 1, h2⟩ : Fin m) = ⟨j + 2, h⟩ := rfl
  simp only [sub_mul, mul_assoc, E_eq, Ψ_mul_single, Category.id_comp]
  rw [← single_eqToHom _ hb, ← single_sub, crossE_def _ h1, crossE_def _ h1, crossE_def _ h1,
    crossE_def _ h2, crossE_def _ h2, crossE_def _ h2, ← Presentation.diag_comp,
    ← Presentation.diag_comp, ← Presentation.diag_comp, ← Presentation.diag_comp,
    diag_comp_eqToHom _ (congrArg (fun s => ob (word s)) hb)]
  have n₀ : j ≠ j + 1 := by omega
  have n₁ : j ≠ j + 1 + 1 := by omega
  have n₂ : j + 1 ≠ j + 1 + 1 := by omega
  have n₃ : j + 1 + 1 ≠ j := by omega
  have n₄ : j + 1 + 1 ≠ j + 1 := by omega
  have n₅ : j + 1 ≠ j := by omega
  split_ifs with he
  · have ht := sadj_braid_smul_eq_self i h he.1
    rw [← single_eqToHom _ ht, Preadditive.sub_comp,
      diag_comp_eqToHom _ (congrArg (fun s => ob (word s)) ht),
      diag_comp_eqToHom _ (congrArg (fun s => ob (word s)) ht)]
    rw [braidQ_pos Q he.2 (p := j)
      (Diagram.cast ((crossD i h1 ≫ crossD (sadj m j • i) h2) ≫
        crossD (sadj m (j + 1) • sadj m j • i) h1) rfl (congrArg (fun s => ob (word s)) ht))
      (Diagram.cast (Diagram.cast ((crossD i h2 ≫ crossD (sadj m (j + 1) • i) h1) ≫
        crossD (sadj m j • sadj m (j + 1) • i) h2) rfl (congrArg (fun s => ob (word s)) hb))
        rfl (congrArg (fun s => ob (word s)) ht))
      (dotD i ⟨j, by omega⟩) (dotD i ⟨j + 1, h1⟩) (dotD i ⟨j + 2, h⟩)
      rfl (by len_tac) rfl (by len_tac)
      (by simp [sadj_symm, sadj_apply_left h1, sadj_apply_left h2, sadj_apply_right h1,
        sadj_apply_right h2, sadj_apply_of_ne, n₀, n₁, n₂, n₃, n₄, n₅, e₂, he.1])
      (by len_tac)
      (by simp [sadj_symm, sadj_apply_left h1, sadj_apply_left h2, sadj_apply_right h1,
        sadj_apply_right h2, sadj_apply_of_ne, n₀, n₁, n₂, n₃, n₄, n₅, e₂, he.1])
      rfl (by len_tac) (by simp [he.1]) (by len_tac)
      (by simp [sadj_symm, sadj_apply_left h1, sadj_apply_left h2, sadj_apply_right h1,
        sadj_apply_right h2, sadj_apply_of_ne, n₀, n₁, n₂, n₃, n₄, n₅, e₂, he.1])
      (by len_tac)
      (by simp [sadj_symm, sadj_apply_left h1, sadj_apply_left h2, sadj_apply_right h1,
        sadj_apply_right h2, sadj_apply_of_ne, n₀, n₁, n₂, n₃, n₄, n₅, e₂, he.1])
      rfl (by len_tac) rfl rfl (by len_tac) rfl rfl (by len_tac) (by simp [he.1])]
    have e₁ : (![(pres k Q).diag (dotD i ⟨j, by omega⟩), (pres k Q).diag (dotD i ⟨j + 1, h1⟩),
        (pres k Q).diag (dotD i ⟨j + 2, h⟩)] : Fin 3 → End ((pres k Q).obj (ob (word i)))) =
        fun t => dotE k Q i (![⟨j, by omega⟩, ⟨j + 1, h1⟩, ⟨j + 2, h⟩] t) := by
      funext t; fin_cases t <;> rfl
    have e₂ : (![X ⟨j, by omega⟩, X ⟨j + 1, h1⟩, X ⟨j + 2, h⟩] : Fin 3 → DiagR k Q ν) =
        fun t => X (![⟨j, by omega⟩, ⟨j + 1, h1⟩, ⟨j + 2, h⟩] t) := by
      funext t; fin_cases t <;> rfl
    rw [e₁, single_ncEval, e₂, E_eq]
  · rw [braid_pos Q he (p := j)
      ((crossD i h1 ≫ crossD (sadj m j • i) h2) ≫ crossD (sadj m (j + 1) • sadj m j • i) h1)
      (Diagram.cast ((crossD i h2 ≫ crossD (sadj m (j + 1) • i) h1) ≫
        crossD (sadj m j • sadj m (j + 1) • i) h2) rfl (congrArg (fun s => ob (word s)) hb))
      rfl (by len_tac) rfl (by len_tac)
      (by simp [sadj_symm, sadj_apply_left h1, sadj_apply_left h2, sadj_apply_right h1,
        sadj_apply_right h2, sadj_apply_of_ne, n₀, n₁, n₂, n₃, n₄, n₅, e₂])
      (by len_tac)
      (by simp [sadj_symm, sadj_apply_left h1, sadj_apply_left h2, sadj_apply_right h1,
        sadj_apply_right h2, sadj_apply_of_ne, n₀, n₁, n₂, n₃, n₄, n₅, e₂])
      rfl (by len_tac) rfl (by len_tac)
      (by simp [sadj_symm, sadj_apply_left h1, sadj_apply_left h2, sadj_apply_right h1,
        sadj_apply_right h2, sadj_apply_of_ne, n₀, n₁, n₂, n₃, n₄, n₅, e₂])
      (by len_tac)
      (by simp [sadj_symm, sadj_apply_left h1, sadj_apply_left h2, sadj_apply_right h1,
        sadj_apply_right h2, sadj_apply_of_ne, n₀, n₁, n₂, n₃, n₄, n₅, e₂]),
      sub_self, single_zero]

end DiagR

end Categorification.KLR.Diagram

end
