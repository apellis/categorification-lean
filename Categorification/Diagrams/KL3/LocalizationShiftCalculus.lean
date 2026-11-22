/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.LocalizationShiftNormalForm

/-!
# A calculus of composites for the weight shift of `U′`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Proposition 3.30. Composites in `U′` of normal-form layers and integer powers of downward
dots, indexed by lists of steps (`DStep`), with the interchange laws needed to compute the
images of the defining relations under the weight shift: merging of dot powers, sliding of dot
powers past layers on either side, commutation of distant dots, and the description of the
image of a normal-form diagram as such a composite (`imgList_eq_zg`).
-/

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Categorification.KL3.Diagram
open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
universe w u v
variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k]

/-- A step of a composite in `U′`: a normal-form layer or an integer power of a downward dot. -/
inductive DStep (I : Type u) where
  | lay (x : LayerData I)
  | dot (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℤ)

namespace DStep

def dom : DStep I → List (Letter I)
  | lay x => x.1 ++ x.2.1.dom ++ x.2.2
  | dot u i v _ => u ++ [dn i] ++ v

def cod : DStep I → List (Letter I)
  | lay x => x.1 ++ x.2.1.cod ++ x.2.2
  | dot u i v _ => u ++ [dn i] ++ v

end DStep

/-- A list of steps composes from `s` to `t`. -/
def DChain : List (Letter I) → List (DStep I) → List (Letter I) → Prop
  | s, [], t => s = t
  | s, st :: L, t => s = st.dom ∧ DChain st.cod L t

theorem DChain.append {s r t : List (Letter I)} {A B : List (DStep I)} (hA : DChain s A r)
    (hB : DChain r B t) : DChain s (A ++ B) t := by
  induction A generalizing s with
  | nil => cases hA; exact hB
  | cons x A ih => exact ⟨hA.1, ih hA.2⟩

/-- The morphism of `U′` of one step. -/
def stepHom (ν : X) : (st : DStep I) → (lob RD k ν st.dom ⟶ lob RD k ν st.cod)
  | .lay x => ldg RD k ν _ _ [x]
  | .dot u i v n => zdot RD k ν u i v n

open Classical in
/-- The composite of a list of steps (zero if the steps do not compose from `s` to `t`). -/
def zg (ν : X) : (s t : List (Letter I)) → List (DStep I) → (lob RD k ν s ⟶ lob RD k ν t)
  | s, t, [] => if h : s = t then eqToHom (congrArg (lob RD k ν) h) else 0
  | s, t, st :: L => if h : s = st.dom then
      eqToHom (congrArg (lob RD k ν) h) ≫ stepHom RD k ν st ≫ zg ν st.cod t L else 0

variable {RD k}

theorem zg_nil (ν : X) (s : List (Letter I)) : zg RD k ν s s [] = 𝟙 _ := by simp [zg]

theorem zg_cons_self (ν : X) (t : List (Letter I)) (st : DStep I) (L : List (DStep I)) :
    zg RD k ν st.dom t (st :: L) = stepHom RD k ν st ≫ zg RD k ν st.cod t L := by
  simp [zg]

theorem eqToHom_zg (ν : X) {s s' : List (Letter I)} (t : List (Letter I)) (h : s = s')
    (L : List (DStep I)) :
    eqToHom (congrArg (lob RD k ν) h) ≫ zg RD k ν s' t L = zg RD k ν s t L := by
  subst h; simp

theorem zg_eqToHom (ν : X) (s : List (Letter I)) {t t' : List (Letter I)} (h : t = t')
    (L : List (DStep I)) :
    zg RD k ν s t L ≫ eqToHom (congrArg (lob RD k ν) h) = zg RD k ν s t' L := by
  subst h; simp

theorem zg_single (ν : X) (st : DStep I) : zg RD k ν st.dom st.cod [st] = stepHom RD k ν st := by
  rw [zg_cons_self, zg_nil, Category.comp_id]

theorem zg_append (ν : X) {s r : List (Letter I)} (t : List (Letter I)) {A : List (DStep I)}
    (B : List (DStep I)) (hA : DChain s A r) :
    zg RD k ν s t (A ++ B) = zg RD k ν s r A ≫ zg RD k ν r t B := by
  induction A generalizing s with
  | nil => cases hA; rw [List.nil_append, zg_nil, Category.id_comp]
  | cons x A ih =>
    obtain ⟨rfl, h₂⟩ := hA
    rw [List.cons_append, zg_cons_self, zg_cons_self, ih h₂, Category.assoc]

theorem zg_local (ν : X) {s r r' : List (Letter I)} (t : List (Letter I)) {A M M' : List (DStep I)}
    (B : List (DStep I)) (hA : DChain s A r) (hM : DChain r M r') (hM' : DChain r M' r')
    (e : zg RD k ν r r' M = zg RD k ν r r' M') :
    zg RD k ν s t (A ++ M ++ B) = zg RD k ν s t (A ++ M' ++ B) := by
  rw [List.append_assoc, List.append_assoc, zg_append ν t _ hA, zg_append ν t _ hA,
    zg_append ν t _ hM, zg_append ν t _ hM', e]

theorem dChain_lays {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    DChain s (ls.map .lay) t := by
  induction ls generalizing s with
  | nil => exact h
  | cons x ls ih => exact ⟨h.1, ih h.2⟩

theorem zg_lays (ν : X) {s t : List (Letter I)} {ls : List (LayerData I)} (h : SChain s ls t) :
    zg RD k ν s t (ls.map .lay) = ldg RD k ν s t ls := by
  induction ls generalizing s with
  | nil => cases h; rw [List.map_nil, zg_nil, ldg_nil]
  | cons x ls ih =>
    obtain ⟨rfl, h₂⟩ := h
    rw [List.map_cons]
    change zg RD k ν (DStep.lay x).dom t _ = _
    rw [zg_cons_self]; erw [ih h₂]
    exact ldg_comp RD k (sChain_single x) h₂

theorem zg_dot_add (ν : X) (t : List (Letter I)) (u : List (Letter I)) (i : I)
    (v : List (Letter I)) (m n : ℤ) (L : List (DStep I)) :
    zg RD k ν (u ++ [dn i] ++ v) t (.dot u i v m :: .dot u i v n :: L) =
      zg RD k ν (u ++ [dn i] ++ v) t (.dot u i v (n + m) :: L) := by
  change zg RD k ν (DStep.dot u i v m).dom t _ = zg RD k ν (DStep.dot u i v (n + m)).dom t _
  rw [zg_cons_self, zg_cons_self]
  change zdot RD k ν u i v m ≫ zg RD k ν (DStep.dot u i v n).dom t _ = _
  rw [zg_cons_self]
  show zdot RD k ν u i v m ≫ zdot RD k ν u i v n ≫ _ = zdot RD k ν u i v (n + m) ≫ _
  rw [zdot_add, Category.assoc]; rfl

theorem zg_dot_zero (ν : X) (t : List (Letter I)) (u : List (Letter I)) (i : I)
    (v : List (Letter I)) (L : List (DStep I)) :
    zg RD k ν (u ++ [dn i] ++ v) t (.dot u i v 0 :: L) = zg RD k ν (u ++ [dn i] ++ v) t L := by
  change zg RD k ν (DStep.dot u i v 0).dom t _ = _
  rw [zg_cons_self]
  show zdot RD k ν u i v 0 ≫ _ = _
  rw [zdot_zero, Category.id_comp]; rfl

theorem zg_cons (ν : X) {s : List (Letter I)} (t : List (Letter I)) {st : DStep I}
    (L : List (DStep I)) (h : s = st.dom) :
    zg RD k ν s t (st :: L) =
      eqToHom (congrArg (lob RD k ν) h) ≫ stepHom RD k ν st ≫ zg RD k ν st.cod t L := by
  subst h; rw [zg_cons_self, eqToHom_refl, Category.id_comp]

theorem zg_nil' (ν : X) {s t : List (Letter I)} (h : s = t) :
    zg RD k ν s t [] = eqToHom (congrArg (lob RD k ν) h) := by
  subst h; rw [zg_nil, eqToHom_refl]

theorem zg_cons_not (ν : X) {s : List (Letter I)} (t : List (Letter I)) {st : DStep I}
    (L : List (DStep I)) (h : ¬ s = st.dom) : zg RD k ν s t (st :: L) = 0 := by
  rw [zg.eq_2]; exact dite_eq_right h

theorem zg_steps_eq (ν : X) (s t : List (Letter I)) {L L' : List (DStep I)} (h : L = L') :
    zg RD k ν s t L = zg RD k ν s t L' := by rw [h]

theorem zg_lays_zero (ν : X) {s t : List (Letter I)} {ls : List (LayerData I)}
    (h : ¬ SChain s ls t) : zg RD k ν s t (ls.map .lay) = 0 := by
  induction ls generalizing s with
  | nil => rw [List.map_nil, zg.eq_1]; exact dite_eq_right h
  | cons x ls ih =>
    rw [List.map_cons]
    by_cases h1 : s = (DStep.lay x).dom
    · rw [zg_cons ν t _ h1]; erw [ih (fun h2 => h ⟨h1, h2⟩)]
      rw [Limits.comp_zero, Limits.comp_zero]
    · exact zg_cons_not ν t _ h1

theorem zg_lays_all (ν : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    zg RD k ν s t (ls.map .lay) = ldg RD k ν s t ls := by
  by_cases h : SChain s ls t
  · exact zg_lays ν h
  · rw [zg_lays_zero ν h, ldg, dg_of_not h, Functor.map_zero]

theorem zg_dot_one (ν : X) (s t u : List (Letter I)) (i : I) (v : List (Letter I))
    (L : List (DStep I)) :
    zg RD k ν s t (.dot u i v 1 :: L) = zg RD k ν s t (.lay (u, .dot (dn i), v) :: L) := by
  by_cases h : s = u ++ [dn i] ++ v
  · rw [zg_cons ν t L (st := .dot u i v 1) h, zg_cons ν t L (st := .lay (u, .dot (dn i), v)) h]
    show _ ≫ zdot RD k ν u i v 1 ≫ _ = _ ≫ ldg RD k ν _ _ [(u, .dot (dn i), v)] ≫ _
    rw [zdot_one, ldot, ← ldg_of]; rfl
  · rw [zg_cons_not ν t L (st := .dot u i v 1) h,
      zg_cons_not ν t L (st := .lay (u, .dot (dn i), v)) h]

/-! ### Integer powers of dots past morphisms -/

theorem units_val_zpow_comp {𝒞 : Type*} [Category 𝒞] {p q : 𝒞} (U : (End p)ˣ)
    (W : (End q)ˣ)
    (f : p ⟶ q) (h : U.val ≫ f = f ≫ W.val) (n : ℤ) :
    (U ^ n).val ≫ f = f ≫ (W ^ n).val := by
  have hN : ∀ m : ℕ, (U ^ m).val ≫ f = f ≫ (W ^ m).val := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, pow_zero, Units.val_one, Units.val_one, End.one_def, End.one_def,
        Category.id_comp, Category.comp_id]
    | succ m ih =>
      rw [pow_succ, pow_succ, Units.val_mul, Units.val_mul, End.mul_def, End.mul_def,
        Category.assoc, ih, ← Category.assoc, h, Category.assoc]
  have hinv : ∀ (U' : (End p)ˣ) (W' : (End q)ˣ), U'.val ≫ f = f ≫ W'.val →
      (U'⁻¹).val ≫ f = f ≫ (W'⁻¹).val := by
    intro U' W' h'
    have e1 : W'.val ≫ (W'⁻¹).val = 𝟙 _ := by
      rw [← End.mul_def, ← Units.val_mul, inv_mul_cancel, Units.val_one, End.one_def]
    have e2 : (U'⁻¹).val ≫ U'.val = 𝟙 _ := by
      rw [← End.mul_def, ← Units.val_mul, mul_inv_cancel, Units.val_one, End.one_def]
    calc (U'⁻¹).val ≫ f = (U'⁻¹).val ≫ f ≫ W'.val ≫ (W'⁻¹).val := by
          rw [e1, Category.comp_id]
      _ = (U'⁻¹).val ≫ (U'.val ≫ f) ≫ (W'⁻¹).val := by rw [h', Category.assoc]
      _ = f ≫ (W'⁻¹).val := by simp only [← Category.assoc, e2, Category.id_comp]
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hN m
  | negSucc m => rw [zpow_negSucc, zpow_negSucc]; exact hinv _ _ (hN (m + 1))

theorem zdot_comp_of_one (ν : X) {A B A' B' : List (Letter I)} {i j : I}
    (f : lob RD k ν (A ++ [dn i] ++ B) ⟶ lob RD k ν (A' ++ [dn j] ++ B'))
    (h : zdot RD k ν A i B 1 ≫ f = f ≫ zdot RD k ν A' j B' 1) (n : ℤ) :
    zdot RD k ν A i B n ≫ f = f ≫ zdot RD k ν A' j B' n := by
  rw [zdot, zdot, zpow_one, zpow_one] at h
  exact units_val_zpow_comp _ _ f h n

theorem zg_dot_cons (ν : X) (t A : List (Letter I)) (i : I) (B : List (Letter I)) (n : ℤ)
    (M : List (DStep I)) :
    zg RD k ν (A ++ [dn i] ++ B) t (.dot A i B n :: M) =
      zdot RD k ν A i B n ≫ zg RD k ν (A ++ [dn i] ++ B) t M :=
  zg_cons_self (st := .dot A i B n) ν t M

theorem zg_append_dot (ν : X) {s : List (Letter I)} (A : List (Letter I)) (i : I)
    (B : List (Letter I)) (n : ℤ) {M : List (DStep I)} (hM : DChain s M (A ++ [dn i] ++ B)) :
    zg RD k ν s (A ++ [dn i] ++ B) (M ++ [.dot A i B n]) =
      zg RD k ν s (A ++ [dn i] ++ B) M ≫ zdot RD k ν A i B n := by
  rw [zg_append ν _ _ hM]; exact congrArg _ (zg_single (st := .dot A i B n) ν)

/-- A dot that commutes with a step list `M` for one power commutes for every integer power. -/
theorem zg_dot_comm (ν : X) {A B A' B' : List (Letter I)} {i j : I} (M : List (DStep I))
    (hM : DChain (A ++ [dn i] ++ B) M (A' ++ [dn j] ++ B'))
    (h1 : zg RD k ν (A ++ [dn i] ++ B) (A' ++ [dn j] ++ B') (.dot A i B 1 :: M) =
      zg RD k ν (A ++ [dn i] ++ B) (A' ++ [dn j] ++ B') (M ++ [.dot A' j B' 1])) (n : ℤ) :
    zg RD k ν (A ++ [dn i] ++ B) (A' ++ [dn j] ++ B') (.dot A i B n :: M) =
      zg RD k ν (A ++ [dn i] ++ B) (A' ++ [dn j] ++ B') (M ++ [.dot A' j B' n]) := by
  rw [zg_dot_cons, zg_append_dot ν _ _ _ _ hM] at h1 ⊢
  exact zdot_comp_of_one ν _ h1 n

theorem zg_eq_transport (ν : X) {s s' t t' : List (Letter I)} {L L' : List (DStep I)}
    (hs : s = s') (ht : t = t') (e : zg RD k ν s t L = zg RD k ν s t L') :
    zg RD k ν s' t' L = zg RD k ν s' t' L' := by
  subst hs ht; exact e

theorem zg_cons_tail (ν : X) (s t : List (Letter I)) (st : DStep I) {L L' : List (DStep I)}
    (h : ∀ s', zg RD k ν s' t L = zg RD k ν s' t L') :
    zg RD k ν s t (st :: L) = zg RD k ν s t (st :: L') := by
  rw [zg.eq_2, zg.eq_2, h]

/-! ### Interchange of steps -/

/-- The interchange law for two layers, as step lists. -/
theorem zg_swap (ν : X) (s t a m b : List (Letter I)) (g h : Shape I) :
    zg RD k ν s t [.lay (a, g, m ++ h.dom ++ b), .lay (a ++ g.cod ++ m, h, b)] =
      zg RD k ν s t [.lay (a ++ g.dom ++ m, h, b), .lay (a, g, m ++ h.cod ++ b)] :=
  (zg_lays_all ν s t [_, _]).trans (
    (congrArg (toLoc RD k).map (dg_swap RD k ν s t a m b g h)).trans
    (zg_lays_all ν s t [_, _]).symm)

theorem zg_slideR_one (ν : X) (s t a m b : List (Letter I)) (g : Shape I) (i : I) :
    zg RD k ν s t [.dot (a ++ g.dom ++ m) i b 1, .lay (a, g, m ++ [dn i] ++ b)] =
      zg RD k ν s t [.lay (a, g, m ++ [dn i] ++ b), .dot (a ++ g.cod ++ m) i b 1] := by
  rw [zg_dot_one, zg_cons_tail ν s t _ (fun s' => zg_dot_one ν s' t (a ++ g.cod ++ m) i b [])]
  exact (zg_swap ν s t a m b g (.dot (dn i))).symm

theorem zg_slideL_one (ν : X) (s t a m b : List (Letter I)) (h : Shape I) (i : I) :
    zg RD k ν s t [.dot a i (m ++ h.dom ++ b) 1, .lay (a ++ [dn i] ++ m, h, b)] =
      zg RD k ν s t [.lay (a ++ [dn i] ++ m, h, b), .dot a i (m ++ h.cod ++ b) 1] := by
  rw [zg_dot_one, zg_cons_tail ν s t _ (fun s' => zg_dot_one ν s' t a i (m ++ h.cod ++ b) [])]
  exact zg_swap ν s t a m b (.dot (dn i)) h

theorem zg_dotComm_one (ν : X) (s t a m b : List (Letter I)) (i j : I) :
    zg RD k ν s t [.dot a i (m ++ [dn j] ++ b) 1, .dot (a ++ [dn i] ++ m) j b 1] =
      zg RD k ν s t [.dot (a ++ [dn i] ++ m) j b 1, .dot a i (m ++ [dn j] ++ b) 1] := by
  rw [zg_dot_one, zg_cons_tail ν s t _ (fun s' => zg_dot_one ν s' t (a ++ [dn i] ++ m) j b []),
    zg_dot_one, zg_cons_tail ν s t _ (fun s' => zg_dot_one ν s' t a i (m ++ [dn j] ++ b) [])]
  exact zg_swap ν s t a m b (.dot (dn i)) (.dot (dn j))

/-- **Sliding dots to the right of a layer** past it. -/
theorem zg_slideR (ν : X) (a m b : List (Letter I)) (g : Shape I) (i : I) (n : ℤ) :
    zg RD k ν ((a ++ g.dom ++ m) ++ [dn i] ++ b) ((a ++ g.cod ++ m) ++ [dn i] ++ b)
        [.dot (a ++ g.dom ++ m) i b n, .lay (a, g, m ++ [dn i] ++ b)] =
      zg RD k ν ((a ++ g.dom ++ m) ++ [dn i] ++ b) ((a ++ g.cod ++ m) ++ [dn i] ++ b)
        [.lay (a, g, m ++ [dn i] ++ b), .dot (a ++ g.cod ++ m) i b n] :=
  zg_dot_comm ν [.lay (a, g, m ++ [dn i] ++ b)]
    ⟨by simp [DStep.dom], by simp [DStep.cod, DChain]⟩ (zg_slideR_one ν _ _ a m b g i) n

/-- **Sliding dots to the left of a layer** past it. -/
theorem zg_slideL (ν : X) (a m b : List (Letter I)) (h : Shape I) (i : I) (n : ℤ) :
    zg RD k ν (a ++ [dn i] ++ (m ++ h.dom ++ b)) (a ++ [dn i] ++ (m ++ h.cod ++ b))
        [.dot a i (m ++ h.dom ++ b) n, .lay (a ++ [dn i] ++ m, h, b)] =
      zg RD k ν (a ++ [dn i] ++ (m ++ h.dom ++ b)) (a ++ [dn i] ++ (m ++ h.cod ++ b))
        [.lay (a ++ [dn i] ++ m, h, b), .dot a i (m ++ h.cod ++ b) n] :=
  zg_dot_comm ν [.lay (a ++ [dn i] ++ m, h, b)]
    ⟨by simp [DStep.dom], by simp [DStep.cod, DChain]⟩ (zg_slideL_one ν _ _ a m b h i) n

/-- **Dots on different strands commute.** -/
theorem zg_dotComm (ν : X) (a m b : List (Letter I)) (i j : I) (n n' : ℤ) :
    zg RD k ν (a ++ [dn i] ++ (m ++ [dn j] ++ b)) (a ++ [dn i] ++ (m ++ [dn j] ++ b))
        [.dot a i (m ++ [dn j] ++ b) n, .dot (a ++ [dn i] ++ m) j b n'] =
      zg RD k ν (a ++ [dn i] ++ (m ++ [dn j] ++ b)) (a ++ [dn i] ++ (m ++ [dn j] ++ b))
        [.dot (a ++ [dn i] ++ m) j b n', .dot a i (m ++ [dn j] ++ b) n] := by
  have e : a ++ [dn i] ++ (m ++ [dn j] ++ b) = (a ++ [dn i] ++ m) ++ [dn j] ++ b := by simp
  have h1 := zg_dot_comm (RD := RD) (k := k) ν [.dot (a ++ [dn i] ++ m) j b 1]
    ⟨by simp [DStep.dom], by simp [DStep.cod, DChain]⟩ (zg_dotComm_one ν _ _ a m b i j) n
  have h2 := zg_dot_comm (RD := RD) (k := k) ν [.dot a i (m ++ [dn j] ++ b) n]
    ⟨by simp [DStep.dom], by simp [DStep.cod, DChain]⟩ (zg_eq_transport ν e e h1).symm n'
  exact zg_eq_transport ν e.symm e.symm h2.symm

/-! ### Images of normal-form layers as step lists -/

section Images

variable (a b : I → ℤ)

/-- The steps of the image of a normal-form layer under the weight shift. -/
def layStep : LayerData I → List (DStep I)
  | (u, .dot l, v) => [.lay (u, .dot l, v)]
  | (u, .cross ε i j, v) => [.lay (u, .cross ε i j, v)]
  | (u, .cup (true, i), v) => [.lay (u, .cup (true, i), v), .dot (u ++ [up i]) i v (-a i)]
  | (u, .cup (false, i), v) => [.lay (u, .cup (false, i), v), .dot u i ([up i] ++ v) (-b i)]
  | (u, .cap (true, i), v) => [.dot u i ([up i] ++ v) (a i), .lay (u, .cap (true, i), v)]
  | (u, .cap (false, i), v) => [.dot (u ++ [up i]) i v (b i), .lay (u, .cap (false, i), v)]

theorem dChain_layStep (x : LayerData I) :
    DChain (x.1 ++ x.2.1.dom ++ x.2.2) (layStep a b x) (x.1 ++ x.2.1.cod ++ x.2.2) := by
  obtain ⟨u, g, v⟩ := x
  cases g with
  | dot l => exact ⟨rfl, rfl⟩
  | cross ε i j => exact ⟨rfl, rfl⟩
  | cup l =>
    obtain ⟨_ | _, i⟩ := l <;>
      simp [layStep, DChain, DStep.dom, DStep.cod, Letter.dual, up, dn]
  | cap l =>
    obtain ⟨_ | _, i⟩ := l <;>
      simp [layStep, DChain, DStep.dom, DStep.cod, Letter.dual, up, dn]

theorem imgLay_eq_zg (ν : X) (x : LayerData I) :
    imgLay RD k a b ν x = zg RD k ν (x.1 ++ x.2.1.dom ++ x.2.2) (x.1 ++ x.2.1.cod ++ x.2.2)
      (layStep a b x) := by
  obtain ⟨u, g, v⟩ := x
  cases g with
  | dot l => exact (zg_single (st := .lay (u, .dot l, v)) ν).symm
  | cross ε i j => exact (zg_single (st := .lay (u, .cross ε i j, v)) ν).symm
  | cup l =>
    obtain ⟨_ | _, i⟩ := l
    · show _ = zg RD k ν (u ++ [] ++ v) (u ++ [(false, i), Letter.dual (false, i)] ++ v)
        [.lay (u, .cup (false, i), v), .dot u i ([up i] ++ v) (-b i)]
      rw [zg_cons ν _ _ (s := u ++ [] ++ v) (st := .lay (u, .cup (false, i), v)) rfl,
        zg_cons ν _ [] (s := (DStep.lay (u, .cup (false, i), v)).cod)
          (st := .dot u i ([up i] ++ v) (-b i))
          (by simp [DStep.dom, DStep.cod, Letter.dual, up, dn]),
        zg_nil' ν (s := (DStep.dot u i ([up i] ++ v) (-b i)).cod)
          (t := u ++ [(false, i), Letter.dual (false, i)] ++ v)
          (by simp [DStep.cod, Letter.dual, up, dn])]
      simp only [imgLay, cupDecAt, eqToHom_refl, Category.id_comp]
      rfl
    · show _ = zg RD k ν (u ++ [] ++ v) (u ++ [(true, i), Letter.dual (true, i)] ++ v)
        [.lay (u, .cup (true, i), v), .dot (u ++ [up i]) i v (-a i)]
      rw [zg_cons ν _ _ (s := u ++ [] ++ v) (st := .lay (u, .cup (true, i), v)) rfl,
        zg_cons ν _ [] (s := (DStep.lay (u, .cup (true, i), v)).cod)
          (st := .dot (u ++ [up i]) i v (-a i))
          (by simp [DStep.dom, DStep.cod, Letter.dual, up, dn]),
        zg_nil' ν (s := (DStep.dot (u ++ [up i]) i v (-a i)).cod)
          (t := u ++ [(true, i), Letter.dual (true, i)] ++ v)
          (by simp [DStep.cod, Letter.dual, up, dn])]
      simp only [imgLay, cupDecAt, eqToHom_refl, Category.id_comp]
      rfl
  | cap l =>
    obtain ⟨_ | _, i⟩ := l
    · show _ = zg RD k ν (u ++ [Letter.dual (false, i), (false, i)] ++ v) (u ++ [] ++ v)
        [.dot (u ++ [up i]) i v (b i), .lay (u, .cap (false, i), v)]
      rw [zg_cons ν _ _ (s := u ++ [Letter.dual (false, i), (false, i)] ++ v)
          (st := .dot (u ++ [up i]) i v (b i))
          (by simp [DStep.dom, Letter.dual, up, dn]),
        zg_cons ν _ [] (s := (DStep.dot (u ++ [up i]) i v (b i)).cod)
          (st := .lay (u, .cap (false, i), v))
          (by simp [DStep.dom, DStep.cod, Letter.dual, up, dn]),
        zg_nil' ν (s := (DStep.lay (u, .cap (false, i), v)).cod) (t := u ++ [] ++ v) rfl]
      simp only [imgLay, capDecAt, eqToHom_refl, Category.comp_id, Category.assoc]
      rfl
    · show _ = zg RD k ν (u ++ [Letter.dual (true, i), (true, i)] ++ v) (u ++ [] ++ v)
        [.dot u i ([up i] ++ v) (a i), .lay (u, .cap (true, i), v)]
      rw [zg_cons ν _ _ (s := u ++ [Letter.dual (true, i), (true, i)] ++ v)
          (st := .dot u i ([up i] ++ v) (a i))
          (by simp [DStep.dom, Letter.dual, up, dn]),
        zg_cons ν _ [] (s := (DStep.dot u i ([up i] ++ v) (a i)).cod)
          (st := .lay (u, .cap (true, i), v))
          (by simp [DStep.dom, DStep.cod, Letter.dual, up, dn]),
        zg_nil' ν (s := (DStep.lay (u, .cap (true, i), v)).cod) (t := u ++ [] ++ v) rfl]
      simp only [imgLay, capDecAt, eqToHom_refl, Category.comp_id, Category.assoc]
      rfl

theorem imgList_eq_zg (ν : X) (ls : List (LayerData I)) {s t : List (Letter I)}
    (h : SChain s ls t) :
    imgList RD k a b ν ls h = zg RD k ν s t (ls.flatMap (layStep a b)) := by
  induction ls generalizing s with
  | nil => exact (zg_nil' ν h).symm
  | cons x ls ih =>
    obtain ⟨rfl, h₂⟩ := h
    rw [List.flatMap_cons, zg_append ν t _ (dChain_layStep a b x), ← ih h₂, ← imgLay_eq_zg]
    simp only [imgList, eqToHom_refl, Category.id_comp]

end Images

end Categorification.KL3.Diagram
