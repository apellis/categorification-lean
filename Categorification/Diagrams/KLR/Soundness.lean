/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KLR.DiagR

/-!
# Soundness: KLR diagrams evaluate in `R(ν)`

We interpret the free 2-category on the KLR signature in the `k`-linear category `Tgt k Q ν`
built from the KLR algebra `R(ν) = KLRAlgebra k Q ν`:

* objects are words `a` of colours; `ε a ∈ R(ν)` is the idempotent `e_i` if `a` is the word of
  the sequence `i` of weight `ν`, and `0` otherwise;
* morphisms `a ⟶ b` are the elements `r` with `ε b * r * ε a = r`; composition is
  multiplication (`f ≫ g = g * f`) and the identity of `a` is `ε a`.

A layer with a dot (resp. a crossing) `p` strands from the left goes to `x_p ε` (resp.
`ψ_p ε`) (`interp`). This interpretation kills every whiskered defining relation and every
instance of the interchange law (`respects`), because the relations of `R(ν)` hold after
multiplication by each idempotent `e_i`. Hence it descends to the presented category
(`StringDiagrams.Presentation.lift`).
-/

noncomputable section

namespace Categorification.KLR.Diagram

open CategoryTheory StringDiagrams TypeA KLRAlgebra

universe u

variable {I : Type u} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

/-! ## Idempotents of words -/

variable (k Q ν) in
/-- The idempotent of a word: `e_i` if the word is that of the sequence `i` of weight `ν`,
and `0` if there is no such sequence. -/
def ε (a : Obj (sig I)) : KLRAlgebra k Q ν :=
  ∑ i ∈ Finset.univ.filter (fun i : Seq ν => word i = a.word), e i

theorem ε_eq (a : Obj (sig I)) :
    ε k Q ν a = ∑ i ∈ Finset.univ.filter (fun i : Seq ν => word i = a.word), e i := rfl

theorem ε_mul_e (a : Obj (sig I)) (s : Seq ν) :
    ε k Q ν a * e s = if word s = a.word then e s else 0 := by
  rw [ε, Finset.sum_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single s]
    · exact e_mul_self s
    · intro t _ ht; rw [e_mul_e, if_neg ht]
    · intro hs; exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ s, h⟩) hs
  · refine Finset.sum_eq_zero fun t ht => ?_
    rw [e_mul_e, if_neg]
    rintro rfl; exact h (Finset.mem_filter.1 ht).2

theorem e_mul_ε (a : Obj (sig I)) (s : Seq ν) :
    e s * ε k Q ν a = if word s = a.word then e s else 0 := by
  rw [ε, Finset.mul_sum]
  split_ifs with h
  · rw [Finset.sum_eq_single s]
    · exact e_mul_self s
    · intro t _ ht; rw [e_mul_e, if_neg (Ne.symm ht)]
    · intro hs; exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ s, h⟩) hs
  · refine Finset.sum_eq_zero fun t ht => ?_
    rw [e_mul_e, if_neg]
    rintro rfl; exact h (Finset.mem_filter.1 ht).2

theorem ε_mul_ε (a : Obj (sig I)) : ε k Q ν a * ε k Q ν a = ε k Q ν a := by
  rw [ε_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [← ε_eq, e_mul_ε, if_pos (Finset.mem_filter.1 hs).2]

theorem ε_ob (i : Seq ν) : ε k Q ν (ob (word i)) = e i := by
  rw [ε, Finset.sum_eq_single i]
  · intro t ht hti; exact absurd (word_injective (Finset.mem_filter.1 ht).2) hti
  · simp

theorem mul_ε_eq_zero {a : Obj (sig I)} {r : KLRAlgebra k Q ν}
    (h : ∀ s : Seq ν, word s = a.word → r * e s = 0) : r * ε k Q ν a = 0 := by
  rw [ε, Finset.mul_sum]
  exact Finset.sum_eq_zero fun s hs => h s (Finset.mem_filter.1 hs).2

/-! ## Generators at a position -/

variable (k Q ν) in
/-- The dot on strand `p` (zero if `p ≥ m`). -/
def xN (p : ℕ) : KLRAlgebra k Q ν := if h : p < m then x ⟨p, h⟩ else 0

theorem xN_of_lt {p : ℕ} (h : p < m) : xN k Q ν p = x ⟨p, h⟩ := dif_pos h

theorem xN_mul_e (p : ℕ) (s : Seq ν) : xN k Q ν p * e s = e s * xN k Q ν p := by
  unfold xN; split_ifs <;> simp [x_mul_e]

theorem xN_commute_ε (p : ℕ) (a : Obj (sig I)) : Commute (xN k Q ν p) (ε k Q ν a) := by
  show _ * _ = _ * _
  rw [ε, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => xN_mul_e p s

theorem xN_mul_xN (p q : ℕ) : xN k Q ν p * xN k Q ν q = xN k Q ν q * xN k Q ν p := by
  unfold xN; split_ifs <;> simp [x_mul_x]

theorem xN_mul_ψ (p j : ℕ) (h₁ : p ≠ j) (h₂ : p ≠ j + 1) :
    xN k Q ν p * ψ j = ψ j * xN k Q ν p := by
  unfold xN; split_ifs with h
  · exact x_mul_ψ _ j h₁ h₂
  · simp

variable (k Q ν) in
/-- The image of a generator placed `p` strands from the left. -/
def genAt : Gen I → ℕ → KLRAlgebra k Q ν
  | .dot _, p => xN k Q ν p
  | .cross _ _, p => ψ p

@[simp] theorem genAt_dot (c : I) (p : ℕ) : genAt k Q ν (.dot c) p = xN k Q ν p := rfl
@[simp] theorem genAt_cross (c d : I) (p : ℕ) : genAt k Q ν (.cross c d) p = ψ p := rfl

theorem genAt_comm (g h : Gen I) {p q : ℕ} (hpq : p + g.arity ≤ q) :
    genAt k Q ν h q * genAt k Q ν g p = genAt k Q ν g p * genAt k Q ν h q := by
  cases g with
  | dot c =>
    have hpq' : p + 1 ≤ q := hpq
    cases h with
    | dot d => exact xN_mul_xN q p
    | cross d e =>
      have := xN_mul_ψ (k := k) (Q := Q) (ν := ν) p q (by omega) (by omega)
      exact this.symm
  | cross c d =>
    have hpq' : p + 2 ≤ q := hpq
    cases h with
    | dot e => exact xN_mul_ψ q p (by omega) (by omega)
    | cross e f =>
      have := ψ_mul_ψ (k := k) (Q := Q) (ν := ν) p q (by omega)
      exact this.symm

variable (k Q ν) in
/-- The image of a layer (without idempotent). -/
def genL (L : Layer (sig I)) : KLRAlgebra k Q ν := genAt k Q ν L.gen L.left.length

@[simp] theorem genL_lay (l : List I) (g : Gen I) (r : List I) :
    genL k Q ν (lay l g r) = genAt k Q ν g l.length := rfl

@[simp] theorem genL_whisker (L : Layer (sig I)) (u : Obj (sig I)) (v : List I) :
    genL k Q ν (L.whisker u v) = genAt k Q ν L.gen (u.word.length + L.left.length) := by
  simp [genL, Layer.whisker]

omit [DecidableEq I] in
/-- Splitting the word of a sequence. -/
theorem length_eq_of_word {s : Seq ν} {u l v : List I} (h : word s = u ++ l ++ v) :
    u.length + l.length + v.length = m := by
  have := congrArg List.length h
  simp at this
  omega

omit [DecidableEq I] in
theorem apply_eq_of_word {s : Seq ν} {u l v : List I} (h : word s = u ++ l ++ v) (t : ℕ)
    (ht : t < l.length) (hm : u.length + t < m) : s.1 ⟨u.length + t, hm⟩ = l[t] := by
  have e := congrArg (fun w => w[u.length + t]?) h
  simp only [List.append_assoc] at e
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left ht, List.getElem?_eq_getElem ht,
    List.getElem?_eq_getElem (by simpa using hm), getElem_word] at e
  exact Option.some.inj e

theorem genL_mul_ε (L : Layer (sig I)) :
    ε k Q ν L.cod * genL k Q ν L * ε k Q ν L.dom = genL k Q ν L * ε k Q ν L.dom := by
  rw [ε_eq L.dom, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hw : word s = L.left ++ L.gen.dom ++ L.right := (Finset.mem_filter.1 hs).2
  obtain ⟨⟨⟩, l, g, r⟩ := L
  dsimp only at hw
  cases g with
  | dot c =>
    have hw' : word s = (Layer.cod ⟨(), l, .dot c, r⟩ : Obj (sig I)).word := hw
    simp only [genL, genAt_dot]
    rw [mul_assoc, xN_mul_e, ← mul_assoc, ε_mul_e, if_pos hw']
  | cross c d =>
    simp only [genL, genAt_cross]
    rw [mul_assoc]
    have hlen := length_eq_of_word hw
    simp only [Gen.dom_cross, List.length_cons, List.length_nil] at hlen
    have hp : l.length + 1 < m := by omega
    have h0 := apply_eq_of_word hw 0 (by simp) (by omega)
    have h1 := apply_eq_of_word hw 1 (by simp) (by omega)
    simp only [Nat.add_zero, Gen.dom_cross, List.getElem_cons_zero,
      List.getElem_cons_succ] at h0 h1
    rw [ψ_mul_e, ← mul_assoc, ε_mul_e, if_pos]
    show word _ = l ++ [d, c] ++ r
    rw [word_sadj s hp, hw]
    simp [h0, h1, List.take_left', List.drop_left']

/-! ## The target category -/

variable (k Q ν) in
/-- The `k`-linear category of words, with morphisms `a ⟶ b` the elements of
`ε b · R(ν) · ε a`. -/
@[nolint unusedArguments]
def Tgt (_k : Type*) [CommRing _k] (_Q : I → I → MvPolynomial (Fin 2) _k) (_ν : Multiset I) :
    Type u :=
  Obj (sig I)

variable (k Q ν) in
/-- The morphisms `a ⟶ b` of `Tgt`: elements `r` with `ε b * r * ε a = r`. -/
def homSub (a b : Obj (sig I)) : Submodule k (KLRAlgebra k Q ν) where
  carrier := {r | ε k Q ν b * r * ε k Q ν a = r}
  add_mem' {r s} hr hs := by
    simp only [Set.mem_setOf_eq] at *; rw [mul_add, add_mul, hr, hs]
  zero_mem' := by simp
  smul_mem' c r hr := by
    simp only [Set.mem_setOf_eq] at *; rw [mul_smul_comm, smul_mul_assoc, hr]

theorem homSub_left {a b : Obj (sig I)} {r : KLRAlgebra k Q ν} (hr : r ∈ homSub k Q ν a b) :
    ε k Q ν b * r = r := by
  have h : ε k Q ν b * r * ε k Q ν a = r := hr
  rw [← h, ← mul_assoc, ← mul_assoc, ε_mul_ε]

theorem homSub_right {a b : Obj (sig I)} {r : KLRAlgebra k Q ν} (hr : r ∈ homSub k Q ν a b) :
    r * ε k Q ν a = r := by
  have h : ε k Q ν b * r * ε k Q ν a = r := hr
  rw [← h, mul_assoc, ε_mul_ε]

instance : Category (Tgt k Q ν) where
  Hom a b := homSub k Q ν a b
  id a := ⟨ε k Q ν a, show _ * _ * _ = _ by rw [ε_mul_ε, ε_mul_ε]⟩
  comp {a b c} f g := ⟨g.1 * f.1, show _ * _ * _ = _ by
    rw [← mul_assoc, homSub_left g.2, mul_assoc, homSub_right f.2]⟩
  id_comp f := Subtype.ext (homSub_right f.2)
  comp_id f := Subtype.ext (homSub_left f.2)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

namespace Tgt

@[simp] theorem id_val (a : Tgt k Q ν) : (𝟙 a : a ⟶ a).1 = ε k Q ν a := rfl

@[simp] theorem comp_val {a b c : Tgt k Q ν} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = g.1 * f.1 := rfl

@[simp] theorem eqToHom_val {a b : Tgt k Q ν} (h : a = b) :
    (eqToHom h : a ⟶ b).1 = ε k Q ν a := by
  subst h; rfl

end Tgt

instance : Preadditive (Tgt k Q ν) where
  homGroup a b := inferInstanceAs (AddCommGroup (homSub k Q ν a b))
  add_comp _ _ _ _ _ _ := Subtype.ext (mul_add _ _ _)
  comp_add _ _ _ _ _ _ := Subtype.ext (add_mul _ _ _)

instance : Linear k (Tgt k Q ν) where
  homModule a b := inferInstanceAs (Module k (homSub k Q ν a b))
  smul_comp _ _ _ r f g := Subtype.ext (mul_smul_comm r g.1 f.1)
  comp_smul _ _ _ f r g := Subtype.ext (smul_mul_assoc r g.1 f.1)

namespace Tgt

@[simp] theorem add_val {a b : Tgt k Q ν} (f g : a ⟶ b) : (f + g).1 = f.1 + g.1 := rfl
@[simp] theorem sub_val {a b : Tgt k Q ν} (f g : a ⟶ b) : (f - g).1 = f.1 - g.1 := rfl
@[simp] theorem zero_val {a b : Tgt k Q ν} : (0 : a ⟶ b).1 = 0 := rfl
@[simp] theorem smul_val {a b : Tgt k Q ν} (r : k) (f : a ⟶ b) : (r • f).1 = r • f.1 := rfl

theorem val_mul_ε {a b : Tgt k Q ν} (f : a ⟶ b) : f.1 * ε k Q ν a = f.1 := homSub_right f.2

theorem ε_mul_val {a b : Tgt k Q ν} (f : a ⟶ b) : ε k Q ν b * f.1 = f.1 := homSub_left f.2

end Tgt

/-! ## The interpretation -/

variable (k Q ν) in
/-- Dots and crossings go to `x_p ε` and `ψ_p ε`. -/
def interp : Interpretation (sig I) (Tgt k Q ν) where
  obj a := a
  layer L _ := ⟨genL k Q ν L * ε k Q ν L.dom, show _ * _ * _ = _ by
    rw [← mul_assoc, genL_mul_ε, mul_assoc, ε_mul_ε]⟩

variable (k Q ν) in
/-- The product of the images of a list of layers, bottom layer rightmost. -/
def evalL : List (Layer (sig I)) → KLRAlgebra k Q ν
  | [] => 1
  | L :: ls => evalL ls * genL k Q ν L

@[simp] theorem evalL_nil : evalL k Q ν [] = 1 := rfl
@[simp] theorem evalL_cons (L : Layer (sig I)) (ls : List (Layer (sig I))) :
    evalL k Q ν (L :: ls) = evalL k Q ν ls * genL k Q ν L := rfl

theorem interp_map_val {a b : Obj (sig I)} (f : a ⟶ b) :
    ((interp k Q ν).functor.map f).1 = evalL k Q ν (Diagram.layers f) * ε k Q ν a := by
  obtain ⟨ls, h⟩ := f
  induction ls generalizing a with
  | nil =>
    show (eqToHom (congrArg (interp k Q ν).obj h)).1 = _
    rw [Tgt.eqToHom_val]
    exact (one_mul _).symm
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have := ih (a := L.cod) hc
    show ((interp k Q ν).functor.map (Diagram.mk (L :: ls) ⟨hv, rfl, hc⟩)).1 = _
    rw [Interpretation.functor_map_mk_cons]
    simp only [Tgt.comp_val, Tgt.eqToHom_val]
    change ((interp k Q ν).functor.map ⟨ls, hc⟩).1 * (genL k Q ν L * ε k Q ν L.dom) *
      ε k Q ν L.dom = _
    rw [this]
    change evalL k Q ν ls * _ * _ * _ = evalL k Q ν ls * genL k Q ν L * _
    rw [mul_assoc (evalL k Q ν ls), ← mul_assoc (ε k Q ν L.cod), genL_mul_ε, mul_assoc,
      mul_assoc, ε_mul_ε, ← mul_assoc]

/-! ## Whiskered diagrams -/

omit [DecidableEq I] in
@[simp] theorem layers_id' (a : Obj (sig I)) : Diagram.layers (𝟙 a) = [] := rfl

theorem whisker_of_val {a b : Obj (sig I)} (d : a ⟶ b) (u : Obj (sig I)) (v : List I)
    (hw : a.WhiskerOK u v) :
    ((freeLift k (interp k Q ν).functor).map (LinDiagram.whisker (LinDiagram.of d) u v hw)).1 =
      evalL k Q ν ((Diagram.layers d).map (·.whisker u v)) * ε k Q ν (a.whisker u v) := by
  rw [LinDiagram.whisker_of, freeLift_map_of, interp_map_val, Diagram.layers_whisker]

variable (k Q ν) in
/-- Whiskering followed by the interpretation, on endomorphisms, as a linear map. -/
def whiskVal (w u : Obj (sig I)) (v : List I) (hw : w.WhiskerOK u v) :
    End (Free.of k w) →ₗ[k] KLRAlgebra k Q ν where
  toFun f := ((freeLift k (interp k Q ν).functor).map (LinDiagram.whisker f u v hw)).1
  map_add' f g := by
    show ((freeLift k (interp k Q ν).functor).map (LinDiagram.whisker (f + g) u v hw)).1 = _
    rw [LinDiagram.whisker_add, CategoryTheory.Functor.map_add, Tgt.add_val]
  map_smul' r f := by
    show ((freeLift k (interp k Q ν).functor).map (LinDiagram.whisker (r • f) u v hw)).1 = _
    rw [LinDiagram.whisker_smul, CategoryTheory.Functor.map_smul, Tgt.smul_val]
    rfl

theorem whiskVal_lpoly (w u : Obj (sig I)) (v : List I) (hw : w.WhiskerOK u v) {n : ℕ}
    (y : Fin n → (w ⟶ w)) (z : Fin n → KLRAlgebra k Q ν)
    (hy : ∀ t, evalL k Q ν ((Diagram.layers (y t)).map (·.whisker u v)) = z t)
    (hz : ∀ t, Commute (z t) (ε k Q ν (w.whisker u v))) (p : MvPolynomial (Fin n) k) :
    ((freeLift k (interp k Q ν).functor).map (LinDiagram.whisker (lpoly k y p) u v hw)).1 =
      ncEval z p * ε k Q ν (w.whisker u v) := by
  refine ncEval_of_mul (whiskVal k Q ν w u v hw) (fun f g => ?_) (e := ε k Q ν (w.whisker u v))
    ?_ _ z (fun t => ?_) hz p
  · show ((freeLift k (interp k Q ν).functor).map (LinDiagram.whisker (g ≫ f) u v hw)).1 = _
    rw [LinDiagram.whisker_comp _ _ _ _ hw hw, Functor.map_comp, Tgt.comp_val]
    rfl
  · show ((freeLift k (interp k Q ν).functor).map
      (LinDiagram.whisker (𝟙 (Free.of k w)) u v hw)).1 = _
    rw [show LinDiagram.whisker (𝟙 (Free.of k w)) u v hw = 𝟙 _ from
      LinDiagram.whisker_single _ _ _ _ _, CategoryTheory.Functor.map_id, Tgt.id_val]
    rfl
  · show ((freeLift k (interp k Q ν).functor).map
      (LinDiagram.whisker (LinDiagram.of (y t)) u v hw)).1 = _
    rw [whisker_of_val, hy]

omit [DecidableEq I] in
theorem seq_two {s : Seq ν} {u v : List I} {c d : I} (hs : word s = u ++ [c, d] ++ v) :
    ∃ h : u.length + 1 < m, s.1 ⟨u.length, by omega⟩ = c ∧ s.1 ⟨u.length + 1, h⟩ = d := by
  have hl := length_eq_of_word hs
  simp only [List.length_cons, List.length_nil] at hl
  refine ⟨by omega, ?_, ?_⟩
  · simpa using apply_eq_of_word hs 0 (by simp) (by omega)
  · simpa using apply_eq_of_word hs 1 (by simp) (by omega)

omit [DecidableEq I] in
theorem seq_three {s : Seq ν} {u v : List I} {c d e : I} (hs : word s = u ++ [c, d, e] ++ v) :
    ∃ h : u.length + 2 < m, s.1 ⟨u.length, by omega⟩ = c ∧
      s.1 ⟨u.length + 1, by omega⟩ = d ∧ s.1 ⟨u.length + 2, h⟩ = e := by
  have hl := length_eq_of_word hs
  simp only [List.length_cons, List.length_nil] at hl
  refine ⟨by omega, ?_, ?_, ?_⟩
  · simpa using apply_eq_of_word hs 0 (by simp) (by omega)
  · simpa using apply_eq_of_word hs 1 (by simp) (by omega)
  · simpa using apply_eq_of_word hs 2 (by simp) (by omega)

/-! ## Soundness -/

theorem respects_rel (r : Rel I) (u : Obj (sig I)) (v : List I)
    (hw : (Rel.dom r).WhiskerOK u v) :
    ((freeLift k (interp k Q ν).functor).map
      (LinDiagram.whisker (relation k Q r) u v hw)).1 = 0 := by
  cases r with
  | sqEq c =>
    simp only [relation, whisker_of_val]
    refine mul_ε_eq_zero fun s hs => ?_
    obtain ⟨hm, h0, h1⟩ := seq_two (s := s) (u := u.word) (v := v) (c := c) (d := c)
      (by simpa [Rel.dom] using hs)
    simp [ψ_sq _ hm s, h0, h1]
  | sqNe c d hcd =>
    simp only [relation, LinDiagram.whisker_sub, Functor.map_sub, Tgt.sub_val, whisker_of_val]
    rw [whiskVal_lpoly _ u v hw _ ![xN k Q ν u.word.length, xN k Q ν (u.word.length + 1)]
      (fun t => by fin_cases t <;> simp) (fun t => by fin_cases t <;> exact xN_commute_ε _ _),
      ← sub_mul]
    refine mul_ε_eq_zero fun s hs => ?_
    obtain ⟨hm, h0, h1⟩ := seq_two (s := s) (u := u.word) (v := v) (c := c) (d := d)
      (by simpa [Rel.dom] using hs)
    have e₁ : (![xN k Q ν u.word.length, xN k Q ν (u.word.length + 1)] : Fin 2 → _) =
        ![x ⟨u.word.length, by omega⟩, x ⟨u.word.length + 1, hm⟩] := by
      rw [xN_of_lt (by omega), xN_of_lt hm]
    simp only [List.map_cons, List.map_nil, evalL_cons, evalL_nil, genL_whisker, one_mul,
      sub_mul, e₁, layers_dl, Diagram.layers_comp, List.cons_append, List.nil_append]
    simp [ψ_sq _ hm s, h0, h1, hcd]
  | slideLEq c =>
    simp only [relation, LinDiagram.whisker_sub, Functor.map_sub, Tgt.sub_val, whisker_of_val,
      ← sub_mul]
    refine mul_ε_eq_zero fun s hs => ?_
    obtain ⟨hm, h0, h1⟩ := seq_two (s := s) (u := u.word) (v := v) (c := c) (d := c)
      (by simpa [Rel.dom] using hs)
    have key := KLRAlgebra.dot_cross_left (k := k) (Q := Q) _ hm s
    rw [if_pos (h0.trans h1.symm), sub_mul] at key
    simp only [List.map_cons, List.map_nil, evalL_cons, evalL_nil, genL_whisker, one_mul,
      sub_mul, layers_dl, Diagram.layers_comp, layers_id', Rel.dom, Rel.cod, List.cons_append,
      List.nil_append, lay_gen, lay_left, genAt_dot, genAt_cross, List.length_nil,
      List.length_cons, List.length_singleton, add_zero, Nat.add_zero, zero_add]
    rw [xN_of_lt (by omega), xN_of_lt hm, key, sub_self]
  | slideLNe c d hcd =>
    simp only [relation, LinDiagram.whisker_sub, Functor.map_sub, Tgt.sub_val, whisker_of_val,
      ← sub_mul]
    refine mul_ε_eq_zero fun s hs => ?_
    obtain ⟨hm, h0, h1⟩ := seq_two (s := s) (u := u.word) (v := v) (c := c) (d := d)
      (by simpa [Rel.dom] using hs)
    have key := KLRAlgebra.dot_cross_left (k := k) (Q := Q) _ hm s
    rw [if_neg (by simpa [Seq.lbl, h0, h1] using hcd), sub_mul] at key
    simp only [List.map_cons, List.map_nil, evalL_cons, evalL_nil, genL_whisker, one_mul,
      sub_mul, layers_dl, Diagram.layers_comp, layers_id', Rel.dom, Rel.cod, List.cons_append,
      List.nil_append, lay_gen, lay_left, genAt_dot, genAt_cross, List.length_nil,
      List.length_cons, List.length_singleton, add_zero, Nat.add_zero, zero_add]
    rw [xN_of_lt (by omega), xN_of_lt hm, key]
  | slideREq c =>
    simp only [relation, LinDiagram.whisker_sub, Functor.map_sub, Tgt.sub_val, whisker_of_val,
      ← sub_mul]
    refine mul_ε_eq_zero fun s hs => ?_
    obtain ⟨hm, h0, h1⟩ := seq_two (s := s) (u := u.word) (v := v) (c := c) (d := c)
      (by simpa [Rel.dom] using hs)
    have key := KLRAlgebra.dot_cross_right (k := k) (Q := Q) _ hm s
    rw [if_pos (h0.trans h1.symm), sub_mul] at key
    simp only [List.map_cons, List.map_nil, evalL_cons, evalL_nil, genL_whisker, one_mul,
      sub_mul, layers_dl, Diagram.layers_comp, layers_id', Rel.dom, Rel.cod, List.cons_append,
      List.nil_append, lay_gen, lay_left, genAt_dot, genAt_cross, List.length_nil,
      List.length_cons, List.length_singleton, add_zero, Nat.add_zero, zero_add]
    rw [xN_of_lt (by omega), xN_of_lt hm, key, sub_self]
  | slideRNe c d hcd =>
    simp only [relation, LinDiagram.whisker_sub, Functor.map_sub, Tgt.sub_val, whisker_of_val,
      ← sub_mul]
    refine mul_ε_eq_zero fun s hs => ?_
    obtain ⟨hm, h0, h1⟩ := seq_two (s := s) (u := u.word) (v := v) (c := c) (d := d)
      (by simpa [Rel.dom] using hs)
    have key := KLRAlgebra.dot_cross_right (k := k) (Q := Q) _ hm s
    rw [if_neg (by simpa [Seq.lbl, h0, h1] using hcd), sub_mul] at key
    simp only [List.map_cons, List.map_nil, evalL_cons, evalL_nil, genL_whisker, one_mul,
      sub_mul, layers_dl, Diagram.layers_comp, layers_id', Rel.dom, Rel.cod, List.cons_append,
      List.nil_append, lay_gen, lay_left, genAt_dot, genAt_cross, List.length_nil,
      List.length_cons, List.length_singleton, add_zero, Nat.add_zero, zero_add]
    rw [xN_of_lt (by omega), xN_of_lt hm, key]
  | braid c d e h =>
    simp only [relation, LinDiagram.whisker_sub, Functor.map_sub, Tgt.sub_val, whisker_of_val,
      ← sub_mul]
    refine mul_ε_eq_zero fun s hs => ?_
    obtain ⟨hm, h0, h1, h2⟩ := seq_three (s := s) (u := u.word) (v := v) (c := c) (d := d)
      (e := e) (by simpa [Rel.dom] using hs)
    have key := KLRAlgebra.braid (k := k) (Q := Q) _ hm s
    rw [if_neg (by simpa [Seq.lbl, h0, h1, h2] using h), sub_mul] at key
    simp only [List.map_cons, List.map_nil, evalL_cons, evalL_nil, genL_whisker, one_mul,
      sub_mul, layers_dl, Diagram.layers_comp, layers_id', Rel.dom, Rel.cod, List.cons_append,
      List.nil_append, lay_gen, lay_left, genAt_dot, genAt_cross, List.length_nil,
      List.length_cons, List.length_singleton, add_zero, Nat.add_zero, zero_add]
    simpa only [mul_assoc] using key
  | braidQ c d hcd =>
    simp only [relation, LinDiagram.whisker_sub, Functor.map_sub, Tgt.sub_val, whisker_of_val]
    rw [whiskVal_lpoly _ u v hw _ ![xN k Q ν u.word.length, xN k Q ν (u.word.length + 1),
      xN k Q ν (u.word.length + 2)]
      (fun t => by fin_cases t <;> simp) (fun t => by fin_cases t <;> exact xN_commute_ε _ _),
      ← sub_mul, ← sub_mul]
    refine mul_ε_eq_zero fun s hs => ?_
    obtain ⟨hm, h0, h1, h2⟩ := seq_three (s := s) (u := u.word) (v := v) (c := c) (d := d)
      (e := c) (by simpa [Rel.dom] using hs)
    have key := KLRAlgebra.braid (k := k) (Q := Q) _ hm s
    rw [if_pos (by simpa [Seq.lbl, h0, h1, h2] using hcd), sub_mul] at key
    have e₁ : (![xN k Q ν u.word.length, xN k Q ν (u.word.length + 1),
        xN k Q ν (u.word.length + 2)] : Fin 3 → _) =
        ![x ⟨u.word.length, by omega⟩, x ⟨u.word.length + 1, by omega⟩,
          x ⟨u.word.length + 2, hm⟩] := by
      rw [xN_of_lt (by omega), xN_of_lt (by omega), xN_of_lt hm]
    simp only [List.map_cons, List.map_nil, evalL_cons, evalL_nil, genL_whisker, one_mul,
      sub_mul, layers_dl, Diagram.layers_comp, layers_id', Rel.dom, Rel.cod, List.cons_append,
      List.nil_append, lay_gen, lay_left, genAt_dot, genAt_cross, List.length_nil,
      List.length_cons, List.length_singleton, add_zero, Nat.add_zero, zero_add]
    rw [e₁]
    simp only [Seq.lbl, h0, h1] at key
    rw [key, sub_self]

theorem respects_interchange (x : InterchangeData (sig I)) (hx : x.Valid) (u : Obj (sig I))
    (v : List I) (hw : x.dom.WhiskerOK u v) :
    ((freeLift k (interp k Q ν).functor).map
      (LinDiagram.whisker (InterchangeData.rel k hx) u v hw)).1 = 0 := by
  obtain ⟨st, g, mid, h⟩ := x
  have hs : ((InterchangeData.sign ⟨st, g, mid, h⟩ : ℤ) : k) = 1 := by
    simp [InterchangeData.sign]
  simp only [InterchangeData.rel, hs, one_smul, LinDiagram.whisker_sub, Functor.map_sub,
    Tgt.sub_val, whisker_of_val, ← sub_mul]
  simp only [InterchangeData.ghDiagram, InterchangeData.hgDiagram, InterchangeData.gh₁,
    InterchangeData.gh₂, InterchangeData.hg₁, InterchangeData.hg₂, Diagram.layers_mk,
    List.map_cons, List.map_nil, evalL_cons, evalL_nil, genL_whisker, one_mul,
    List.length_nil, List.length_append, sig_dom, sig_cod, Gen.dom_length, Gen.cod_length,
    add_zero]
  rw [genAt_comm g h (by omega), sub_self, zero_mul]

variable (k Q ν) in
/-- **Soundness.** The interpretation kills every whiskered relation and every whiskered
instance of the interchange law. -/
theorem respects : (pres k Q).Respects (interp k Q ν).functor where
  rel r u v hw := Subtype.ext (respects_rel r u v hw)
  interchange x hx u v hw := Subtype.ext (respects_interchange x hx u v hw)

variable (k Q ν) in
/-- The evaluation functor from the presented KLR category. -/
def evalFunctor : (pres k Q).Presented ⥤ Tgt k Q ν := (pres k Q).lift (respects k Q ν)

instance : (evalFunctor k Q ν).Linear k := Presentation.lift_linear _

instance : (evalFunctor k Q ν).Additive := Presentation.lift_additive _

theorem evalFunctor_diag {a b : Obj (sig I)} (f : a ⟶ b) :
    ((evalFunctor k Q ν).map ((pres k Q).diag f)).1 =
      evalL k Q ν (Diagram.layers f) * ε k Q ν a := by
  rw [evalFunctor, Presentation.lift_diag, interp_map_val]

end Categorification.KLR.Diagram

end
