/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqFullCL
import Categorification.TwoRep.RouqKLRAction
import Categorification.Diagrams.CL.Specialize
import Categorification.Diagrams.BicatInterpAdmissibleDescent
import Categorification.KLR.Examples.Small

/-!
# `U` acts on upward words through the KLR action of a Rouquier family

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1: the
KLR algebra `R(ν)` maps to `END_U(E_ν 1_λ)` (`KL3.Diagram.toUEnd`); KL III uses this map in the
proof of the nondegeneracy theorem, Theorem 1.2. A Rouquier family `S` (`RouqFamily`) with
Brundan's upward KLR data (`BrundanUpKLR`, J. Brundan, arXiv:1501.00350v1, Definition 1.1,
(1.2)–(1.4)) and mixed inversion (`BrundanMixedInversion`, ibid., (1.7)) for the KL scalars is
a representation of KL III's `U` (`RouqFullCL`), and `R(ν)` acts on its words directly
(`RouqFamily.klrAct`). This file shows that the two actions of `R(ν)` agree.

## Main definitions and results

* `RouqFamily.upIso`: the image of the object `E_t 1_μ` of `U` under the admissible
  interpretation is the word of `t` in the family.
* `RouqFamily.upIso_dot`, `RouqFamily.upIso_cross`: under `upIso`, the dot on the `a`-th
  strand and the crossing of the strands `j`, `j + 1` of `E_t 1_μ` act as the dot `wordDot` and
  the crossing `wordCross` of the family.
* `RouqFamily.upEval`, `RouqFamily.upAct`: the evaluation of 2-morphisms of `U` between upward
  words, and the algebra homomorphism `END_U(⊕_t E_t 1_μ) → WordEnd S μ ν` it induces.
* `RouqFamily.upAct_comp_toUEnd`: `upAct ∘ toUEnd = klrAct`.

## Method

The images of a dot or a crossing on a weighted word (`wdot`, `wcross`) are brought to a normal
form: the image of the generator, whiskered by the free words of the strands to its right and
to its left, conjugated by images of free 2-morphisms (`wdot_wdl`, `wcross_wdl`). The free words
`gw` are built one strand at a time, as the weighted words are; `fwIso` compares them with the
words `fw` of the interpretation. Any two parallel free 2-morphisms have equal images, so all
comparisons are absorbed by the generic lemmas `conj_layer`, `conj_layer₂` and `conj_regroup`.
-/

noncomputable section

namespace Categorification.Diagrams.BicatInterp

open CategoryTheory Bicategory StringDiagrams

universe u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-- A well-formed word read from `s` and ending in `t`, as a 1-morphism of the free bicategory
built from the identity by composing one strand at a time. -/
def gw : (s : S.Region) → (w : List S.Colour) → (t : S.Region) → S.ok s w → S.endR s w = t →
    (fo t ⟶ fo s)
  | _, [], _, _, rfl => 𝟙 _
  | _, c :: w, t, h, e => gw (S.colourTgt c) w t h.2 e ≫ FreeBicategory.Hom.of ⟨c, rfl, h.1⟩

/-- The comparison of the two free words. -/
def fwIso : (s : S.Region) → (w : List S.Colour) → (t : S.Region) → (h : S.ok s w) →
    (e : S.endR s w = t) → (fw s w t h e ≅ gw s w t h e)
  | _, [], _, _, rfl => Iso.refl _
  | _, [_], _, _, rfl => (λ_ _).symm
  | _, c :: c' :: w, t, h, e =>
    whiskerRightIso (fwIso (S.colourTgt c) (c' :: w) t h.2 e) (FreeBicategory.Hom.of ⟨c, rfl, h.1⟩)


theorem gw_congr {s t : S.Region} {w w' : List S.Colour} (hw : w = w') (h : S.ok s w)
    (e : S.endR s w = t) (h' : S.ok s w') (e' : S.endR s w' = t) :
    gw s w t h e = gw s w' t h' e' := by
  subst hw; rfl

section Mid

variable {C : Type*} [Bicategory C] (M : Model S C) {a b c d e : FB S}

/-- Whiskering a whiskered generator image on the right regroups it. -/
theorem midK_whiskerRight (p : a ⟶ b) (q : c ⟶ d) (o : d ⟶ e) {x y : b ⟶ c}
    (g : M.lift.map x ⟶ M.lift.map y) :
    midK M p q g ▷ M.lift.map o =
      M.lift.map₂ ((α_ p (x ≫ q) o).hom ≫ p ◁ (α_ x q o).hom) ≫ midK M p (q ≫ o) g ≫
        M.lift.map₂ (p ◁ (α_ y q o).inv ≫ (α_ p (y ≫ q) o).inv) := by
  simp only [midK, PrelaxFunctor.map₂_comp, lift_map₂_whiskerLeft, lift_map₂_associator_hom,
    lift_map₂_associator_inv, lift_map_comp]
  bicategory

/-- A whiskered 2-morphism conjugated by images of free 2-morphisms does not depend on the
whiskering free 1-morphisms up to isomorphism. -/
theorem midK_conj_free {p p' : a ⟶ b} {q q' : c ⟶ d} {x y : b ⟶ c} (σ : p ≅ p') (τ : q ≅ q')
    (g : M.lift.map x ⟶ M.lift.map y) {W W' : a ⟶ d} (A : W ⟶ p ≫ (x ≫ q))
    (B : p ≫ (y ≫ q) ⟶ W') (A' : W ⟶ p' ≫ (x ≫ q')) (B' : p' ≫ (y ≫ q') ⟶ W') :
    M.lift.map₂ A ≫ midK M p q g ≫ M.lift.map₂ B =
      M.lift.map₂ A' ≫ midK M p' q' g ≫ M.lift.map₂ B' := by
  rw [mid_conj M σ τ g]
  simp only [Category.assoc, ← PrelaxFunctor.map₂_comp_assoc, ← PrelaxFunctor.map₂_comp]
  exact lift_conj_eq M _ _ _ _ _

/-- A layer image transported along free equalities and conjugated by a free isomorphism is in
normal form for any isomorphic whiskering 1-morphisms. -/
theorem conj_layer {Z G F₁ F₂ : a ⟶ d} {p p' : a ⟶ b} {q q' : c ⟶ d} {x y : b ⟶ c}
    (κ : Z ≅ G) (h₁ : Z = F₁) (e₁ : M.lift.map Z = M.lift.map F₁) (A : F₁ ⟶ p ≫ (x ≫ q))
    (g : M.lift.map x ⟶ M.lift.map y) (B : p ≫ (y ≫ q) ⟶ F₂) (h₂ : F₂ = Z)
    (e₂ : M.lift.map F₂ = M.lift.map Z) (σ : p ≅ p') (τ : q ≅ q') (φ : G ⟶ p' ≫ (x ≫ q'))
    (ψ : p' ≫ (y ≫ q') ⟶ G) :
    M.lift.map₂ κ.inv ≫ (eqToHom e₁ ≫ (M.lift.map₂ A ≫ midK M p q g ≫ M.lift.map₂ B) ≫
        eqToHom e₂) ≫ M.lift.map₂ κ.hom =
      M.lift.map₂ φ ≫ midK M p' q' g ≫ M.lift.map₂ ψ := by
  rw [eqToHom_lift M h₁ e₁, eqToHom_lift M h₂ e₂]
  calc _ = M.lift.map₂ (κ.inv ≫ eqToHom h₁ ≫ A) ≫ midK M p q g ≫
        M.lift.map₂ (B ≫ eqToHom h₂ ≫ κ.hom) := by
          simp only [PrelaxFunctor.map₂_comp, Category.assoc]
    _ = _ := midK_conj_free M σ τ g _ _ _ _

/-- A layer image between two free words, transported along free equalities and conjugated by
free isomorphisms, is in normal form for any isomorphic whiskering 1-morphisms. -/
theorem conj_layer₂ {Z Z' G G' G₁ F₁ F₂ : a ⟶ d} {p p' : a ⟶ b} {q q' : c ⟶ d} {x y : b ⟶ c}
    (κ : Z ≅ G) (κ' : Z' ≅ G') (h₁ : Z = F₁) (e₁ : M.lift.map Z = M.lift.map F₁)
    (A : F₁ ⟶ p ≫ (x ≫ q)) (g : M.lift.map x ⟶ M.lift.map y) (B : p ≫ (y ≫ q) ⟶ F₂)
    (h₂ : F₂ = Z') (e₂ : M.lift.map F₂ = M.lift.map Z') (σ : p ≅ p') (τ : q ≅ q')
    (φ : G ⟶ p' ≫ (x ≫ q')) (ψ : p' ≫ (y ≫ q') ⟶ G₁) (h₃ : G₁ = G')
    (e₃ : M.lift.map G₁ = M.lift.map G') :
    M.lift.map₂ κ.inv ≫ (eqToHom e₁ ≫ (M.lift.map₂ A ≫ midK M p q g ≫ M.lift.map₂ B) ≫
        eqToHom e₂) ≫ M.lift.map₂ κ'.hom =
      (M.lift.map₂ φ ≫ midK M p' q' g ≫ M.lift.map₂ ψ) ≫ eqToHom e₃ := by
  rw [eqToHom_lift M h₁ e₁, eqToHom_lift M h₂ e₂, eqToHom_lift M h₃ e₃]
  calc _ = M.lift.map₂ (κ.inv ≫ eqToHom h₁ ≫ A) ≫ midK M p q g ≫
        M.lift.map₂ (B ≫ eqToHom h₂ ≫ κ'.hom) := by
          simp only [PrelaxFunctor.map₂_comp, Category.assoc]
    _ = M.lift.map₂ φ ≫ midK M p' q' g ≫ M.lift.map₂ (ψ ≫ eqToHom h₃) :=
          midK_conj_free M σ τ g _ _ _ _
    _ = _ := by simp only [PrelaxFunctor.map₂_comp, Category.assoc]

/-- Regrouping images of free 2-morphisms around a 2-morphism. -/
theorem conj_regroup {x x₁ x₂ y₂ y₁ y : a ⟶ b} (A : x ⟶ x₁) (B : x₁ ⟶ x₂)
    (K : M.lift.map x₂ ⟶ M.lift.map y₂) (C : y₂ ⟶ y₁) (D : y₁ ⟶ y) (E : x ⟶ x₂) (F : y₂ ⟶ y) :
    M.lift.map₂ A ≫ (M.lift.map₂ B ≫ K ≫ M.lift.map₂ C) ≫ M.lift.map₂ D =
      M.lift.map₂ E ≫ K ≫ M.lift.map₂ F := by
  rw [lift_map₂_eq M E (A ≫ B), lift_map₂_eq M F (C ≫ D)]
  simp only [PrelaxFunctor.map₂_comp, Category.assoc]

end Mid

section Descent

variable {C : Type*} [Bicategory C] {M : Model S C} {k : Type*} [CommRing k]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Additive]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Additive]
  [∀ (a b c : C) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : C) (g : b ⟶ c), (postcomp a g).Linear k]
  (G : GenImg M) (P : Presentation S k)
  (hrel : ∀ (i : P.Rel) {s t : S.Region} (ha : Cond s t (P.dom i))
    (hb : Cond s t (P.cod i)), admissibleMap G ha hb (P.rel i) = 0)
  (heven : ∀ g, S.odd g = false)

theorem admissibleQuotientMap_add {s t : S.Region} {a b : Obj S} (ha : Cond s t a)
    (hb : Cond s t b) (f g : P.obj a ⟶ P.obj b) :
    admissibleQuotientMap G P hrel heven ha hb (f + g) =
      admissibleQuotientMap G P hrel heven ha hb f +
        admissibleQuotientMap G P hrel heven ha hb g :=
  (admissiblePresentedInterp G P hrel heven s t).map_add (X := ⟨P.obj a, ha⟩)
    (Y := ⟨P.obj b, hb⟩) (f := ObjectProperty.homMk f) (g := ObjectProperty.homMk g)

theorem admissibleQuotientMap_smul {s t : S.Region} {a b : Obj S} (ha : Cond s t a)
    (hb : Cond s t b) (r : k) (f : P.obj a ⟶ P.obj b) :
    admissibleQuotientMap G P hrel heven ha hb (r • f) =
      r • admissibleQuotientMap G P hrel heven ha hb f :=
  (admissiblePresentedInterp G P hrel heven s t).map_smul (X := ⟨P.obj a, ha⟩)
    (Y := ⟨P.obj b, hb⟩) r (ObjectProperty.homMk f)

end Descent

end Categorification.Diagrams.BicatInterp

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KL3.Diagram StringDiagrams Diagrams.BicatInterp

universe w v u u₁

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}

variable (RD) in
/-- The weighted word of upward strands of the colours `l`, with the weights of KL III's regions
(rightmost region `μ`). -/
def wdl (μ : X) : List I → List (I × X)
  | [] => []
  | c :: l => (c, wt RD μ (ups l)) :: wdl μ l

theorem wValid_wdl (μ : X) : ∀ (l : List I) {s : X}, wt RD μ (ups l) = s →
    wValid RD μ (wdl RD μ l) s
  | [], _, h => h
  | c :: l, _, h => ⟨wValid_wdl μ l rfl, by rw [← h]; simp [sh, add_comm]⟩

theorem ok_wd_ups (μ : X) : ∀ (l : List I) {s : X}, wt RD μ (ups l) = s →
    (psig RD).ok s (wd RD μ (ups l))
  | [], _, _ => trivial
  | _ :: l, _, h => ⟨h, ok_wd_ups μ l rfl⟩

theorem length_wd (μ : X) (t : List (Letter I)) : (wd RD μ t).length = t.length := by
  induction t with
  | nil => rfl
  | cons l t ih => simp [ih]

theorem wd_drop (μ : X) : ∀ (l : List (Letter I)) (n : ℕ), (wd RD μ l).drop n = wd RD μ (l.drop n)
  | [], n => by simp
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => wd_drop μ l n

theorem wd_take (μ : X) : ∀ (l : List (Letter I)) (n : ℕ),
    (wd RD μ l).take n = wd RD (KL3.Diagram.wt RD μ (l.drop n)) (l.take n)
  | [], n => by simp
  | _ :: _, 0 => rfl
  | x :: l, n + 1 => by
    rw [wd_cons, List.take_succ_cons, wd_take μ l n, List.drop_succ_cons, List.take_succ_cons,
      wd_cons, ← wt_append, List.take_append_drop]

theorem wdl_eq_canon (μ : X) : ∀ l : List I, wdl RD μ l = canon RD μ l
  | [] => rfl
  | c :: l => by
    rw [wdl, canon, wdl_eq_canon μ l, ctop_eq, wt_ups]
    simp [wsum, add_comm]

variable (RD) in
/-- The exchange of the strands at positions `j` and `j + 1` of a word of upward strands, as at
the top of an upward crossing: the region between them becomes the bottom region plus the strand
that moved down. -/
def cswap : ℕ → List (Col I X) → List (Col I X)
  | 0, c₁ :: c₂ :: L => ⟨c₂.l, sh RD c₁.l + c₂.r⟩ :: ⟨c₁.l, c₂.r⟩ :: L
  | j + 1, p :: L => p :: cswap j L
  | _, L => L

theorem wt_ups_lswap (μ : X) (j : ℕ) (l : List I) :
    KL3.Diagram.wt RD μ (ups (lswap j l)) = KL3.Diagram.wt RD μ (ups l) := by
  have h := ctop_lswap (RD := RD) 0 j l
  rw [ctop_eq, ctop_eq, zero_add, zero_add] at h
  rw [wt_ups, wt_ups, wsum, wsum, h]

/-- Exchanging two upward strands of a weighted word gives the weighted word of the exchanged
letters. -/
theorem cswap_wd (μ : X) : ∀ (j : ℕ) (l : List I),
    cswap RD j (wd RD μ (ups l)) = wd RD μ (ups (lswap j l))
  | 0, _ :: _ :: _ => rfl
  | j + 1, c :: l => by
    change (⟨up c, _⟩ : Col I X) :: cswap RD j (wd RD μ (ups l)) =
      ⟨up c, KL3.Diagram.wt RD μ (ups (lswap j l))⟩ :: wd RD μ (ups (lswap j l))
    rw [cswap_wd μ j l, wt_ups_lswap]
  | 0, [] => rfl
  | 0, [_] => rfl
  | _ + 1, [] => rfl

namespace RouqFamily

variable (S : RouqFamily (B := B) RD)

/-- **The image of an upward free word is the 1-morphism of its weighted word.** -/
theorem lift_gw (μ : X) : ∀ (l : List I) {s : X} (h : (psig RD).ok s (wd RD μ (ups l)))
    (e : (psig RD).endR s (wd RD μ (ups l)) = μ) (h' : wValid RD μ (wdl RD μ l) s),
    S.model.lift.map (gw s (wd RD μ (ups l)) μ h e) = S.wcell μ (wdl RD μ l) s h'
  | [], s, _, e, _ => by change s = μ at e; subst e; rfl
  | c :: l, s, h, e, h' => by
    change S.model.lift.map (gw _ (wd RD μ (ups l)) μ h.2 e) ≫ _ =
      S.wcell μ (wdl RD μ l) _ h'.1 ≫ _
    rw [lift_gw μ l h.2 e h'.1]
    rfl


theorem E_comp_E_congr {z x b b' y : X} (W : S.obj z ⟶ S.obj x) (c d : I) (eb : b = b')
    (h₁ : x + RD.iX c = b) (h₂ : b + RD.iX d = y) (h₁' : x + RD.iX c = b')
    (h₂' : b' + RD.iX d = y) :
    (W ≫ S.E c h₁) ≫ S.E d h₂ = (W ≫ S.E c h₁') ≫ S.E d h₂' := by
  subst eb; rfl

/-- The image of the free word at the top of an upward crossing is the 1-morphism of the
exchanged weighted word. -/
theorem lift_gw_cswap (μ : X) : ∀ (j : ℕ) (l : List I) {s : X}
    (h : (psig RD).ok s (cswap RD j (wd RD μ (ups l))))
    (e : (psig RD).endR s (cswap RD j (wd RD μ (ups l))) = μ)
    (h' : wValid RD μ (wswap RD j (wdl RD μ l)) s),
    S.model.lift.map (gw s (cswap RD j (wd RD μ (ups l))) μ h e) =
      S.wcell μ (wswap RD j (wdl RD μ l)) s h'
  | 0, [], _, h, e, h' => S.lift_gw μ [] h e h'
  | _ + 1, [], _, h, e, h' => S.lift_gw μ [] h e h'
  | 0, [c], _, h, e, h' => S.lift_gw μ [c] h e h'
  | 0, c :: d :: l, s, h, e, h' => by
    change (S.model.lift.map (gw _ (wd RD μ (ups l)) μ h.2.2 e) ≫ _) ≫ _ =
      (S.wcell μ (wdl RD μ l) _ h'.1.1 ≫ _) ≫ _
    rw [S.lift_gw μ l h.2.2 e h'.1.1]
    exact S.E_comp_E_congr _ c d (show (sh RD (up c) + KL3.Diagram.wt RD μ (ups l) : X) =
      KL3.Diagram.wt RD μ (ups l) + RD.iX c by simp [sh, add_comm]) _ _ _ _
  | j + 1, c :: l, s, h, e, h' => by
    change S.model.lift.map (gw _ (cswap RD j (wd RD μ (ups l))) μ h.2 e) ≫ _ =
      S.wcell μ (wswap RD j (wdl RD μ l)) _ h'.1 ≫ _
    rw [lift_gw_cswap μ j l h.2 e h'.1]
    rfl

/-- The free strand of a colour, between its own regions. -/
abbrev strandF (col : Col I X) :
    fo (S := psig RD) ((psig RD).colourTgt col) ⟶ fo ((psig RD).colourSrc col) :=
  FreeBicategory.Hom.of ⟨col, rfl, rfl⟩

variable (S : RouqFamily (B := B) RD) in
/-- The dot on an upward strand, as an endomorphism of the image of its free strand. -/
def dotF (c : I) (r : X) (hd : r + RD.iX c = (sh RD (up c) + r : X)) :
    S.model.lift.map (strandF (RD := RD) ⟨up c, r⟩) ⟶ S.model.lift.map (strandF ⟨up c, r⟩) :=
  S.dot c hd

/-- **The dot on the `a`-th strand of an upward word, in normal form**: the image of the dot
generator on the strand `col = ⟨+c, r⟩`, whiskered by the free words of the strands to its right
and to its left, conjugated by images of free 2-morphisms. -/
theorem wdot_wdl (μ : X) : ∀ (l : List I) (a : ℕ) (c : I)
    (_ : (wd RD μ (ups l)).drop a = ⟨up c, KL3.Diagram.wt RD μ (ups (l.drop (a + 1)))⟩ ::
      (wd RD μ (ups l)).drop (a + 1))
    {s : X} (h : (psig RD).ok s (wd RD μ (ups l)))
    (e : (psig RD).endR s (wd RD μ (ups l)) = μ) (h' : wValid RD μ (wdl RD μ l) s)
    (hP : (psig RD).ok ((psig RD).colourTgt ⟨up c, KL3.Diagram.wt RD μ (ups (l.drop (a + 1)))⟩)
      ((wd RD μ (ups l)).drop (a + 1)))
    (eP : (psig RD).endR ((psig RD).colourTgt ⟨up c, KL3.Diagram.wt RD μ (ups (l.drop (a + 1)))⟩)
      ((wd RD μ (ups l)).drop (a + 1)) = μ)
    (hQ : (psig RD).ok s ((wd RD μ (ups l)).take a))
    (eQ : (psig RD).endR s ((wd RD μ (ups l)).take a) =
      (psig RD).colourSrc ⟨up c, KL3.Diagram.wt RD μ (ups (l.drop (a + 1)))⟩)
    (hd : KL3.Diagram.wt RD μ (ups (l.drop (a + 1))) + RD.iX c =
      (sh RD (up c) + KL3.Diagram.wt RD μ (ups (l.drop (a + 1))) : X)),
    ∃ (φ : gw (S := psig RD) s (wd RD μ (ups l)) μ h e ⟶
        gw (S := psig RD) _ ((wd RD μ (ups l)).drop (a + 1)) μ hP eP ≫
          (strandF ⟨up c, KL3.Diagram.wt RD μ (ups (l.drop (a + 1)))⟩ ≫
            gw (S := psig RD) s ((wd RD μ (ups l)).take a) _ hQ eQ))
      (ψ : gw (S := psig RD) _ ((wd RD μ (ups l)).drop (a + 1)) μ hP eP ≫
          (strandF ⟨up c, KL3.Diagram.wt RD μ (ups (l.drop (a + 1)))⟩ ≫
            gw (S := psig RD) s ((wd RD μ (ups l)).take a) _ hQ eQ) ⟶
          gw (S := psig RD) s (wd RD μ (ups l)) μ h e),
      eqToHom (S.lift_gw μ l h e h') ≫ S.wdot μ a (wdl RD μ l) s h' ≫
          eqToHom (S.lift_gw μ l h e h').symm =
        S.model.lift.map₂ φ ≫
          midK S.model (gw (S := psig RD) _ ((wd RD μ (ups l)).drop (a + 1)) μ hP eP)
            (gw (S := psig RD) s ((wd RD μ (ups l)).take a) _ hQ eQ) (S.dotF c _ hd) ≫
          S.model.lift.map₂ ψ
  | [], _, _, hc, _, _, _, _, _, _, _, _, _ => by simp at hc
  | c' :: l, 0, c, hc, s, h, e, h', hP, eP, hQ, eQ, hd => by
    obtain rfl : c' = c := by
      simp only [List.drop_zero, wd, ups, List.map_cons, List.cons.injEq] at hc
      exact (Prod.mk.inj (congrArg Col.l hc.1)).2
    obtain rfl : (psig RD).colourSrc ⟨up c', KL3.Diagram.wt RD μ (ups l)⟩ = s := h.1
    refine ⟨_ ◁ (ρ_ (strandF (RD := RD) ⟨up c', KL3.Diagram.wt RD μ (ups l)⟩)).inv,
      _ ◁ (ρ_ (strandF (RD := RD) ⟨up c', KL3.Diagram.wt RD μ (ups l)⟩)).hom, ?_⟩
    have key : ∀ (W : S.obj μ ⟶ S.obj (KL3.Diagram.wt RD μ (ups l)))
        (E0 : S.model.lift.map (gw (S := psig RD) _ (wd RD μ (ups l)) μ hP eP) = W),
        eqToHom (congr_arg₂ (· ≫ ·) E0 rfl) ≫ (W ◁ S.dot c' hd) ≫
            eqToHom (congr_arg₂ (· ≫ ·) E0 rfl).symm =
          S.model.lift.map₂ (gw (S := psig RD) _ (wd RD μ (ups l)) μ hP eP ◁ (ρ_ _).inv) ≫
            midK S.model (gw (S := psig RD) _ (wd RD μ (ups l)) μ hP eP)
              (gw (S := psig RD) _ [] _ hQ eQ) (S.dotF c' _ hd) ≫
              S.model.lift.map₂ (gw (S := psig RD) _ (wd RD μ (ups l)) μ hP eP ◁ (ρ_ _).hom) := by
      rintro W rfl
      erw [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact (layerAt_right S.model _ (S.dotF c' _ hd)).symm
    exact key _ (S.lift_gw μ l hP eP h'.1)
  | c' :: l, a + 1, c, hc, s, h, e, h', hP, eP, hQ, eQ, hd => by
    obtain ⟨φ, ψ, H⟩ := wdot_wdl μ l a c hc h.2 e h'.1 hP eP hQ.2 eQ hd
    refine ⟨φ ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).hom,
      _ ◁ (α_ _ _ _).inv ≫ (α_ _ _ _).inv ≫ ψ ▷ _, ?_⟩
    have H' := congrArg (· ▷ S.model.lift.map (FreeBicategory.Hom.of
      (⟨⟨up c', KL3.Diagram.wt RD μ (ups l)⟩, rfl, h.1⟩ : rq (S := psig RD) _ ⟶ rq s))) H
    refine Eq.trans ?_ (H'.trans ?_)
    · erw [Bicategory.comp_whiskerRight, Bicategory.comp_whiskerRight,
        Bicategory.eqToHom_whiskerRight, Bicategory.eqToHom_whiskerRight]
      rfl
    · simp only [Bicategory.comp_whiskerRight]
      erw [← lift_map₂_whiskerRight, ← lift_map₂_whiskerRight, midK_whiskerRight]
      exact conj_regroup _ _ _ _ _ _ _ _

variable (S : RouqFamily (B := B) RD) in
/-- The upward crossing of the strands `⟨+c, sh d + ν⟩ ⟨+d, ν⟩`, between the images of the free
words of its boundaries. -/
def crossF (c d : I) (ν : X)
    (hy : (psig RD).colourSrc (⟨up d, sh RD (up c) + ν⟩ : Col I X) =
      (sh RD (up c) + (sh RD (up d) + ν) : X)) :
    S.model.lift.map (strandF (RD := RD) ⟨up d, ν⟩ ≫ strandF ⟨up c, sh RD (up d) + ν⟩) ⟶
      S.model.lift.map (strandF (RD := RD) ⟨up c, ν⟩ ≫ FreeBicategory.Hom.of
        (⟨⟨up d, sh RD (up c) + ν⟩, rfl, hy⟩ :
          rq (S := psig RD) (sh RD (up c) + ν) ⟶ rq (sh RD (up c) + (sh RD (up d) + ν)))) :=
  S.cross c d (cross_up_reg d ν) (cross_up_reg' c d rfl) (cross_up_reg c ν)
    (cross_up_swap c d rfl)

/-- **The crossing of the strands `j`, `j + 1` of an upward word, in normal form**: the image
of the crossing generator, whiskered by the free words of the strands to its right and to its
left, conjugated by images of free 2-morphisms. -/
theorem wcross_wdl (μ : X) : ∀ (l : List I) (j : ℕ) (c d : I)
    (_ : (wd RD μ (ups l)).drop j =
      ⟨up c, sh RD (up d) + KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))⟩ ::
        ⟨up d, KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))⟩ :: (wd RD μ (ups l)).drop (j + 2))
    {s : X} (h : (psig RD).ok s (wd RD μ (ups l)))
    (e : (psig RD).endR s (wd RD μ (ups l)) = μ) (h' : wValid RD μ (wdl RD μ l) s)
    (h₁ : (psig RD).ok s (cswap RD j (wd RD μ (ups l))))
    (e₁ : (psig RD).endR s (cswap RD j (wd RD μ (ups l))) = μ)
    (E₁ : S.model.lift.map (gw (S := psig RD) s (cswap RD j (wd RD μ (ups l))) μ h₁ e₁) =
      S.wcell μ (wswap RD j (wdl RD μ l)) s (wValid_wswap j _ h'))
    (hP : (psig RD).ok ((psig RD).colourTgt
        (⟨up d, KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))⟩ : Col I X))
      ((wd RD μ (ups l)).drop (j + 2)))
    (eP : (psig RD).endR ((psig RD).colourTgt
        (⟨up d, KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))⟩ : Col I X))
      ((wd RD μ (ups l)).drop (j + 2)) = μ)
    (hQ : (psig RD).ok s ((wd RD μ (ups l)).take j))
    (eQ : (psig RD).endR s ((wd RD μ (ups l)).take j) =
      (sh RD (up c) + (sh RD (up d) + KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))) : X))
    (hy : (psig RD).colourSrc
        (⟨up d, sh RD (up c) + KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))⟩ : Col I X) =
      (sh RD (up c) + (sh RD (up d) + KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))) : X)),
    ∃ (φ : gw (S := psig RD) s (wd RD μ (ups l)) μ h e ⟶
        gw (S := psig RD) _ ((wd RD μ (ups l)).drop (j + 2)) μ hP eP ≫
          ((strandF (RD := RD) ⟨up d, KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))⟩ ≫
              strandF ⟨up c, sh RD (up d) + KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))⟩) ≫
            gw (S := psig RD) s ((wd RD μ (ups l)).take j) _ hQ eQ))
      (ψ : gw (S := psig RD) _ ((wd RD μ (ups l)).drop (j + 2)) μ hP eP ≫
          ((strandF (RD := RD) ⟨up c, KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))⟩ ≫
              FreeBicategory.Hom.of (⟨⟨up d, sh RD (up c) +
                KL3.Diagram.wt RD μ (ups (l.drop (j + 2)))⟩, rfl, hy⟩ :
                  rq (S := psig RD) _ ⟶ rq _)) ≫
            gw (S := psig RD) s ((wd RD μ (ups l)).take j) _ hQ eQ) ⟶
          gw (S := psig RD) s (cswap RD j (wd RD μ (ups l))) μ h₁ e₁),
      eqToHom (S.lift_gw μ l h e h') ≫ S.wcross μ j (wdl RD μ l) s h' ≫ eqToHom E₁.symm =
        S.model.lift.map₂ φ ≫ midK S.model (gw (S := psig RD) _ ((wd RD μ (ups l)).drop (j + 2))
          μ hP eP) (gw (S := psig RD) s ((wd RD μ (ups l)).take j) _ hQ eQ)
          (S.crossF c d _ hy) ≫ S.model.lift.map₂ ψ
  | [], _, _, _, hc, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at hc
  | [_], 0, _, _, hc, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [wd] at hc
  | [_], _ + 1, _, _, hc, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [wd] at hc
  | c' :: d' :: l, 0, c, d, hc, s, h, e, h', h₁, e₁, E₁, hP, eP, hQ, eQ, hy => by
    obtain ⟨rfl, rfl⟩ : c' = c ∧ d' = d := by
      simp only [List.drop_zero, wd, ups, List.map_cons, List.cons.injEq] at hc
      exact ⟨(Prod.mk.inj (congrArg Col.l hc.1)).2, (Prod.mk.inj (congrArg Col.l hc.2.1)).2⟩
    obtain rfl : (psig RD).colourSrc
        (⟨up c', KL3.Diagram.wt RD μ (ups (d' :: l))⟩ : Col I X) = s := h.1
    refine ⟨(whiskerLeftIso _ (ρ_ _) ≪≫ (α_ _ _ _).symm).inv,
      (whiskerLeftIso _ (ρ_ _) ≪≫ (α_ _ _ _).symm).hom, ?_⟩
    have hb : KL3.Diagram.wt RD μ (ups l) + RD.iX c' =
        sh RD (up c') + KL3.Diagram.wt RD μ (ups l) :=
      cross_up_reg c' _
    have eM : wswap RD 0 (wdl RD μ (c' :: d' :: l)) =
        (d', sh RD (up c') + KL3.Diagram.wt RD μ (ups l)) :: (c', KL3.Diagram.wt RD μ (ups l)) ::
          wdl RD μ l := by
      simp only [wdl, wswap, hb]
    have hM : wValid RD μ ((d', sh RD (up c') + KL3.Diagram.wt RD μ (ups l)) ::
        (c', KL3.Diagram.wt RD μ (ups l)) :: wdl RD μ l) (sh RD (up c') + (sh RD (up d') +
          KL3.Diagram.wt RD μ (ups l))) := eM ▸ wValid_wswap 0 _ h'
    have hw : S.wcross μ 0 (wdl RD μ (c' :: d' :: l)) _ h' =
        S.wcrossTo μ 0 _ _ _ eM h' hM ≫ eqToHom (S.wcell_congr μ eM.symm hM _) := by
      simp only [wcrossTo]
      erw [Category.assoc, eqToHom_trans]
      exact (Category.comp_id (S.wcross μ 0 _ _ h')).symm
    rw [hw]
    erw [S.wcrossTo_zero μ c' d' _ _ _ (wdl RD μ l) _ eM h' hM hb]
    erw [Category.assoc, Category.assoc, eqToHom_trans]
    have key : ∀ (W : S.obj μ ⟶ S.obj (KL3.Diagram.wt RD μ (ups l)))
        (E0 : S.model.lift.map (gw (S := psig RD) _ (wd RD μ (ups l)) μ hP eP) = W)
        (E2 : _) (E3 : _),
        eqToHom E2 ≫ (α_ W _ _).hom ≫ (W ◁ S.cross c' d' h'.1.2 h'.2 hb hM.2 ≫ (α_ W _ _).inv) ≫
            eqToHom E3 =
          S.model.lift.map₂ (whiskerLeftIso (gw (S := psig RD) _ (wd RD μ (ups l)) μ hP eP)
              (ρ_ _) ≪≫ (α_ _ _ _).symm).inv ≫
            midK S.model (gw (S := psig RD) _ (wd RD μ (ups l)) μ hP eP)
              (gw (S := psig RD) _ [] _ hQ eQ) (S.crossF c' d' _ hy) ≫
              S.model.lift.map₂ (whiskerLeftIso (gw (S := psig RD) _ (wd RD μ (ups l)) μ hP eP)
                (ρ_ _) ≪≫ (α_ _ _ _).symm).hom := by
      rintro W rfl E2 E3
      erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact (layerAt_right_assoc S.model _ (S.crossF c' d' _ hy)).symm
    exact key _ (S.lift_gw μ l hP eP h'.1.1) _ _
  | c' :: l, j + 1, c, d, hc, s, h, e, h', h₁, e₁, E₁, hP, eP, hQ, eQ, hy => by
    obtain ⟨φ, ψ, H⟩ := wcross_wdl μ l j c d hc h.2 e h'.1 h₁.2 e₁
      (S.lift_gw_cswap μ j l h₁.2 e₁ (wValid_wswap j _ h'.1)) hP eP hQ.2 eQ hy
    refine ⟨φ ▷ _ ≫ (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).hom,
      _ ◁ (α_ _ _ _).inv ≫ (α_ _ _ _).inv ≫ ψ ▷ _, ?_⟩
    have H' := congrArg (· ▷ S.model.lift.map (FreeBicategory.Hom.of
      (⟨⟨up c', KL3.Diagram.wt RD μ (ups l)⟩, rfl, h.1⟩ : rq (S := psig RD) _ ⟶ rq s))) H
    refine Eq.trans ?_ (H'.trans ?_)
    · erw [Bicategory.comp_whiskerRight, Bicategory.comp_whiskerRight,
        Bicategory.eqToHom_whiskerRight, Bicategory.eqToHom_whiskerRight]
      rfl
    · erw [Bicategory.comp_whiskerRight, Bicategory.comp_whiskerRight,
        ← lift_map₂_whiskerRight, ← lift_map₂_whiskerRight, midK_whiskerRight]
      exact conj_regroup _ _ _ _ _ _ _ _

variable {ν : Multiset I}

theorem wValid_wdl_word (μ : X) (t : KLR.Seq ν) :
    wValid RD μ (wdl RD μ (KLR.Diagram.word t)) (wtop RD μ ν) := by
  rw [wdl_eq_canon]
  exact wValid_wordL μ t

/-- The image of the word `E_{t_0} ⋯ E_{t_{m-1}} 1_μ` under the admissible interpretation is the
word of `t` in the Rouquier family. -/
def upIso (μ : X) (t : KLR.Seq ν)
    (hs : Cond (S := psig RD) (wtop RD μ ν : X) μ (ob RD μ (ups (KLR.Diagram.word t)))) :
    S.model.word (wtop RD μ ν : X) (ob RD μ (ups (KLR.Diagram.word t))).word μ hs.1 hs.2.1 ≅
      S.wordCell μ t :=
  S.model.lift.map₂Iso (fwIso _ _ _ _ _) ≪≫
    eqToIso (S.lift_gw μ (KLR.Diagram.word t) hs.1 hs.2.1 (wValid_wdl_word μ t)) ≪≫
    eqToIso (S.wcell_congr μ (wdl_eq_canon μ _) _ _)

section Interp

variable {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  (Sc : CL.CLScalars C k)

omit [AdditiveWhiskering B] [∀ a b : B, Linear k (a ⟶ b)] in
/-- Conjugation of a transported endomorphism. -/
theorem conj_eq {𝒞 : Type*} [Category 𝒞] {Z G W W' : 𝒞} (κ : Z ≅ G) (E₀ : G = W) (E₂ : W = W')
    (f : Z ⟶ Z) (T : W ⟶ W) (T' : W' ⟶ W') (R : G ⟶ G) (H : κ.inv ≫ f ≫ κ.hom = R)
    (Hd : eqToHom E₀ ≫ T ≫ eqToHom E₀.symm = R) (hT : eqToHom E₂ ≫ T' = T ≫ eqToHom E₂) :
    (κ ≪≫ eqToIso E₀ ≪≫ eqToIso E₂).inv ≫ f ≫ (κ ≪≫ eqToIso E₀ ≪≫ eqToIso E₂).hom = T' := by
  subst E₀ E₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at Hd hT
  simp only [Iso.trans_inv, Iso.trans_hom, eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id]
  rw [H, ← Hd, hT]

theorem ups_drop_word (t : KLR.Seq ν) (a : Fin (Multiset.card ν)) :
    (ups (KLR.Diagram.word t)).drop a = up (t.1 a) :: (ups (KLR.Diagram.word t)).drop (a + 1) := by
  rw [ups, List.drop_eq_getElem_cons (by simp)]
  simp

/-- **The dot on the `a`-th strand of `E_t 1_μ` acts as the dot of the Rouquier family.** -/
theorem upIso_dot (μ : X) (t : KLR.Seq ν) (a : Fin (Multiset.card ν))
    (hs : Cond (S := psig RD) (wtop RD μ ν : X) μ (ob RD μ (ups (KLR.Diagram.word t)))) :
    (S.upIso μ t hs).inv ≫ admissibleMap (k := k) (S.genImg Sc) hs hs
        (LinDiagram.of (upDiag RD μ (KLR.Diagram.dotD t a))) ≫ (S.upIso μ t hs).hom =
      S.wordDot μ t a := by
  have hdrop : (wd RD μ (ups (KLR.Diagram.word t))).drop (a + 1) =
      wd RD μ (ups ((KLR.Diagram.word t).drop (a + 1))) := by
    rw [wd_drop, ups, ups, List.map_drop]
  have hc : (wd RD μ (ups (KLR.Diagram.word t))).drop a =
      ⟨up (t.1 a), KL3.Diagram.wt RD μ (ups ((KLR.Diagram.word t).drop (a + 1)))⟩ ::
        (wd RD μ (ups (KLR.Diagram.word t))).drop (a + 1) := by
    rw [wd_drop, ups_drop_word, wd_cons, hdrop, ups, ups, List.map_drop]
  have hP := hdrop ▸ ok_wd RD μ (ups ((KLR.Diagram.word t).drop (a + 1)))
  have eP := hdrop ▸ endR_wd RD μ (ups ((KLR.Diagram.word t).drop (a + 1)))
  have hs1 : (psig RD).ok (wtop RD μ ν : X) (wd RD μ (ups (KLR.Diagram.word t))) := hs.1
  rw [← List.take_append_drop a (wd RD μ (ups (KLR.Diagram.word t)))] at hs1
  have hsplit := (Signature.ok_append (S := psig RD) (wtop RD μ ν : X) _ _).1 hs1
  rw [hc] at hsplit
  obtain ⟨φ, ψ, Hd⟩ := S.wdot_wdl μ (KLR.Diagram.word t) a (t.1 a) hc hs.1 hs.2.1
    (wValid_wdl_word μ t) hP eP hsplit.1 hsplit.2.1.symm (cross_up_reg _ _)
  suffices H : S.model.lift.map₂ (fwIso (S := psig RD) _ _ _ hs.1 hs.2.1).inv ≫
      admissibleMap (k := k) (S.genImg Sc) hs hs
        (LinDiagram.of (upDiag RD μ (KLR.Diagram.dotD t a))) ≫
        S.model.lift.map₂ (fwIso (S := psig RD) _ _ _ hs.1 hs.2.1).hom =
      S.model.lift.map₂ φ ≫ midK S.model _ _ (S.dotF (t.1 a) _ (cross_up_reg _ _)) ≫
        S.model.lift.map₂ ψ by
    exact conj_eq _ _ _ _ _ _ _ H Hd (S.eqToHom_wdot μ a (wdl_eq_canon μ _) _ _)
  erw [admissibleMap_of]
  change S.model.lift.map₂ _ ≫ (eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _) ≫
    S.model.lift.map₂ _ = _
  erw [coreC_eq]
  have htake : (wd RD μ (ups (KLR.Diagram.word t))).take a =
      wd RD (KL3.Diagram.wt RD μ (up (t.1 a) :: ups ((KLR.Diagram.word t).drop (a + 1))))
        (ups ((KLR.Diagram.word t).take a)) := by
    rw [wd_take, ups_drop_word, ups, ups, ups, List.map_take, List.map_drop]
  have hdom : (upLay RD μ (KLR.Diagram.lay ((KLR.Diagram.word t).take a) (.dot (t.1 a))
      ((KLR.Diagram.word t).drop (a + 1)))).dom.word = wd RD μ (ups (KLR.Diagram.word t)) := by
    rw [upLay_dom, ob_word]
    exact congrArg (fun l => wd RD μ (ups l)) (KLR.Diagram.word_split t a)
  exact conj_layer S.model _ (fw_eq hdom.symm _ _ _ _) _ _ _ _ (fw_eq hdom _ _ _ _) _
    (fwIso _ _ _ _ _ ≪≫ eqToIso (gw_congr hdrop.symm _ _ hP eP))
    (fwIso _ _ _ _ _ ≪≫ eqToIso (gw_congr htake.symm _ _ hsplit.1 hsplit.2.1.symm)) φ ψ

omit [AdditiveWhiskering B] [∀ a b : B, Linear k (a ⟶ b)] in
/-- Conjugation of a transported morphism between two transported objects. -/
theorem conj_eq₂ {𝒞 : Type*} [Category 𝒞] {Z G W W₂ Z' G' W' W₂' G₁ Wsw : 𝒞} (κ : Z ≅ G)
    (E₀ : G = W) (E₂ : W = W₂) (κ' : Z' ≅ G') (E₀' : G' = W') (E₂' : W' = W₂') (f : Z ⟶ Z')
    (R : G ⟶ G₁) (eG : G₁ = G') (H : κ.inv ≫ f ≫ κ'.hom = R ≫ eqToHom eG) (T : W ⟶ Wsw)
    (E₁ : G₁ = Wsw) (Hd : eqToHom E₀ ≫ T ≫ eqToHom E₁.symm = R) (T' : W₂ ⟶ W₂')
    (P : Wsw = W₂') (hT : eqToHom E₂ ≫ T' = T ≫ eqToHom P) :
    (κ ≪≫ eqToIso E₀ ≪≫ eqToIso E₂).inv ≫ f ≫ (κ' ≪≫ eqToIso E₀' ≪≫ eqToIso E₂').hom = T' := by
  subst E₀ E₂ E₁ eG E₀' E₂'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at Hd hT H
  simp only [Iso.trans_inv, Iso.trans_hom, eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id]
  rw [H, ← Hd, hT]

theorem ups_drop_word₂ (t : KLR.Seq ν) {j : ℕ} (hj : j + 1 < Multiset.card ν) :
    (ups (KLR.Diagram.word t)).drop j = up (t.1 ⟨j, by omega⟩) :: up (t.1 ⟨j + 1, hj⟩) ::
      (ups (KLR.Diagram.word t)).drop (j + 2) := by
  rw [ups, List.drop_eq_getElem_cons (by simp; omega),
    List.drop_eq_getElem_cons (by simp; omega)]
  simp

/-- **The crossing of the strands `j`, `j + 1` of `E_t 1_μ` acts as the crossing of the
Rouquier family.** -/
theorem upIso_cross (μ : X) (t : KLR.Seq ν) {j : ℕ} (hj : j + 1 < Multiset.card ν)
    (hs : Cond (S := psig RD) (wtop RD μ ν : X) μ (ob RD μ (ups (KLR.Diagram.word t))))
    (hs' : Cond (S := psig RD) (wtop RD μ ν : X) μ
      (ob RD μ (ups (KLR.Diagram.word (TypeA.sadj (Multiset.card ν) j • t))))) :
    (S.upIso μ t hs).inv ≫ admissibleMap (k := k) (S.genImg Sc) hs hs'
        (LinDiagram.of (upDiag RD μ (KLR.Diagram.crossD t hj))) ≫
        (S.upIso μ (TypeA.sadj (Multiset.card ν) j • t) hs').hom =
      S.wordCross μ t j := by
  have hdrop : (wd RD μ (ups (KLR.Diagram.word t))).drop (j + 2) =
      wd RD μ (ups ((KLR.Diagram.word t).drop (j + 2))) := by
    rw [wd_drop, ups, ups, List.map_drop]
  have hc : (wd RD μ (ups (KLR.Diagram.word t))).drop j =
      ⟨up (t.1 ⟨j, by omega⟩), sh RD (up (t.1 ⟨j + 1, hj⟩)) +
          KL3.Diagram.wt RD μ (ups ((KLR.Diagram.word t).drop (j + 2)))⟩ ::
        ⟨up (t.1 ⟨j + 1, hj⟩), KL3.Diagram.wt RD μ (ups ((KLR.Diagram.word t).drop (j + 2)))⟩ ::
          (wd RD μ (ups (KLR.Diagram.word t))).drop (j + 2) := by
    rw [wd_drop, ups_drop_word₂ t hj, wd_cons, wd_cons, hdrop, ups, ups, List.map_drop]
    rfl
  have hcs : cswap RD j (wd RD μ (ups (KLR.Diagram.word t))) =
      wd RD μ (ups (KLR.Diagram.word (TypeA.sadj (Multiset.card ν) j • t))) := by
    rw [cswap_wd, lswap_eq _ _ (by simpa using hj), KLR.Diagram.word_sadj t hj]
    simp only [KLR.Diagram.getElem_word]
  have hP := hdrop ▸ ok_wd RD μ (ups ((KLR.Diagram.word t).drop (j + 2)))
  have eP := hdrop ▸ endR_wd RD μ (ups ((KLR.Diagram.word t).drop (j + 2)))
  have h₁ : (psig RD).ok (wtop RD μ ν : X) (cswap RD j (wd RD μ (ups (KLR.Diagram.word t)))) := by
    rw [hcs]; exact hs'.1
  have e₁ : (psig RD).endR (wtop RD μ ν : X) (cswap RD j (wd RD μ (ups (KLR.Diagram.word t)))) =
      μ := by
    rw [hcs]; exact hs'.2.1
  have hs1 : (psig RD).ok (wtop RD μ ν : X) (wd RD μ (ups (KLR.Diagram.word t))) := hs.1
  rw [← List.take_append_drop j (wd RD μ (ups (KLR.Diagram.word t)))] at hs1
  have hsplit := (Signature.ok_append (S := psig RD) (wtop RD μ ν : X) _ _).1 hs1
  rw [hc] at hsplit
  have hy : (psig RD).colourSrc (⟨up (t.1 ⟨j + 1, hj⟩), sh RD (up (t.1 ⟨j, by omega⟩)) +
        KL3.Diagram.wt RD μ (ups ((KLR.Diagram.word t).drop (j + 2)))⟩ : Col I X) =
      (sh RD (up (t.1 ⟨j, by omega⟩)) + (sh RD (up (t.1 ⟨j + 1, hj⟩)) +
        KL3.Diagram.wt RD μ (ups ((KLR.Diagram.word t).drop (j + 2)))) : X) := by
    exact @add_left_comm X _ _ _ _
  have E₁ := S.lift_gw_cswap μ j _ h₁ e₁ (wValid_wswap j _ (wValid_wdl_word μ t))
  obtain ⟨φ, ψ, Hd⟩ := S.wcross_wdl μ (KLR.Diagram.word t) j _ _ hc hs.1 hs.2.1
    (wValid_wdl_word μ t) h₁ e₁ E₁ hP eP hsplit.1 hsplit.2.1.symm hy
  suffices H : S.model.lift.map₂ (fwIso (S := psig RD) _ _ _ hs.1 hs.2.1).inv ≫
      admissibleMap (k := k) (S.genImg Sc) hs hs'
        (LinDiagram.of (upDiag RD μ (KLR.Diagram.crossD t hj))) ≫
        S.model.lift.map₂ (fwIso (S := psig RD) _ _ _ hs'.1 hs'.2.1).hom =
      (S.model.lift.map₂ φ ≫ midK S.model _ _ (S.crossF _ _ _ hy) ≫ S.model.lift.map₂ ψ) ≫
        eqToHom (congrArg S.model.lift.map (gw_congr hcs h₁ e₁ hs'.1 hs'.2.1)) by
    refine conj_eq₂ _ _ _ _ _ _ _ _ _ H _ E₁ Hd _ (S.wcell_congr μ
      ((congrArg (wswap RD j) (wdl_eq_canon μ _)).trans (wswap_wordL μ t hj)) _ _) ?_
    rw [wordCross_def _ _ _ hj, wcrossTo]
    erw [S.eqToHom_wcross_assoc μ j (wdl_eq_canon μ _), eqToHom_trans]
    rfl
  erw [admissibleMap_of]
  change S.model.lift.map₂ _ ≫ (eqToHom _ ≫ coreC (S.genImg Sc) _ _ ≫ eqToHom _) ≫
    S.model.lift.map₂ _ = _
  erw [coreC_eq]
  have htake : (wd RD μ (ups (KLR.Diagram.word t))).take j =
      wd RD (KL3.Diagram.wt RD μ (up (t.1 ⟨j, by omega⟩) :: up (t.1 ⟨j + 1, hj⟩) ::
        ups ((KLR.Diagram.word t).drop (j + 2)))) (ups ((KLR.Diagram.word t).take j)) := by
    rw [wd_take, ups_drop_word₂ t hj, ups, ups, ups, List.map_take, List.map_drop]
  have hdom : (upLay RD μ (KLR.Diagram.lay ((KLR.Diagram.word t).take j)
      (.cross (t.1 ⟨j, by omega⟩) (t.1 ⟨j + 1, hj⟩))
        ((KLR.Diagram.word t).drop (j + 2)))).dom.word =
      wd RD μ (ups (KLR.Diagram.word t)) := by
    rw [upLay_dom, ob_word]
    exact congrArg (fun l => wd RD μ (ups l)) (KLR.Diagram.word_split₂ t hj)
  have hcod : (upLay RD μ (KLR.Diagram.lay ((KLR.Diagram.word t).take j)
      (.cross (t.1 ⟨j, by omega⟩) (t.1 ⟨j + 1, hj⟩))
        ((KLR.Diagram.word t).drop (j + 2)))).cod.word =
      wd RD μ (ups (KLR.Diagram.word (TypeA.sadj (Multiset.card ν) j • t))) := by
    rw [upLay_cod, ob_word]
    exact congrArg (fun l => wd RD μ (ups l)) (KLR.Diagram.word_sadj t hj).symm
  exact conj_layer₂ S.model _ _ (fw_eq hdom.symm _ _ _ _) _ _ _ _ (fw_eq hcod _ _ _ _) _
    (fwIso _ _ _ _ _ ≪≫ eqToIso (gw_congr hdrop.symm _ _ hP eP))
    (fwIso _ _ _ _ _ ≪≫ eqToIso (gw_congr htake.symm _ _ hsplit.1 hsplit.2.1.symm)) φ ψ
    (gw_congr hcs h₁ e₁ hs'.1 hs'.2.1) _

end Interp

theorem cond_word (μ : X) (t : KLR.Seq ν) :
    Cond (S := psig RD) (wtop RD μ ν : X) μ (ob RD μ (ups (KLR.Diagram.word t))) := by
  have h : KL3.Diagram.wt RD μ (ups (KLR.Diagram.word t)) = wtop RD μ ν := by
    rw [wt_ups, wsum, add_comm, ← ctop_eq, ctop_word]
  exact ⟨h ▸ ok_wd RD μ _, h ▸ endR_wd RD μ _, h⟩

section Act

variable {k : Type*} [CommRing k] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k]

variable (k) in
/-- The relations of KL III's `U` hold under the admissible interpretation with the KL scalars. -/
theorem pres_rel_kl (H : BrundanUpKLR S (CL.CLScalars.kl : CL.CLScalars C k))
    (M : BrundanMixedInversion S) :
    ∀ (r : (pres RD k).Rel) {s t : X} (ha : Cond (S := psig RD) s t ((pres RD k).dom r))
      (hb : Cond (S := psig RD) s t ((pres RD k).cod r)),
      admissibleMap (S.genImg (CL.CLScalars.kl : CL.CLScalars C k)) ha hb
        ((pres RD k).rel r) = 0 := by
  rw [← CL.presCL_kl]
  exact fun r {_ _} ha hb => S.presCL_rel (CL.CLScalars.kl : CL.CLScalars C k) H M
    (fun _ => rfl) (fun _ _ _ _ _ _ _ => rfl) r ha hb

variable (H : BrundanUpKLR S (CL.CLScalars.kl : CL.CLScalars C k)) (M : BrundanMixedInversion S)

/-- **The evaluation of a 2-morphism of `U` between upward words** `E_t 1_μ → E_{t'} 1_μ`, as a
2-morphism between the words of `t` and `t'` in the Rouquier family. -/
def upEval (μ : X) {t t' : KLR.Seq ν}
    (f : (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t')))) :
    S.wordCell μ t ⟶ S.wordCell μ t' :=
  (S.upIso μ t (cond_word μ t)).inv ≫
    admissibleQuotientMap (S.genImg (CL.CLScalars.kl : CL.CLScalars C k)) (pres RD k)
      (S.pres_rel_kl k H M)
      Signature.IsEven.odd_eq_false (cond_word μ t) (cond_word μ t') f ≫
    (S.upIso μ t' (cond_word μ t')).hom

omit [∀ a b : B, Preadditive (a ⟶ b)] in
theorem conj_comp {𝒞 : Type*} [Category 𝒞] {Z Z' Z'' W W' W'' : 𝒞} (e : Z ≅ W) (e' : Z' ≅ W')
    (e'' : Z'' ≅ W'') (a : Z ⟶ Z') (b : Z' ⟶ Z'') :
    e.inv ≫ (a ≫ b) ≫ e''.hom = (e.inv ≫ a ≫ e'.hom) ≫ (e'.inv ≫ b ≫ e''.hom) := by
  simp

omit [∀ a b : B, Preadditive (a ⟶ b)] in
theorem conj_id {𝒞 : Type*} [Category 𝒞] {Z W : 𝒞} (e : Z ≅ W) :
    e.inv ≫ 𝟙 Z ≫ e.hom = 𝟙 W := by
  simp

omit [∀ a b : B, Preadditive (a ⟶ b)] in
theorem conj_add {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {Z Z' W W' : 𝒞} (e : Z ≅ W)
    (e' : Z' ≅ W') (a b : Z ⟶ Z') :
    e.inv ≫ (a + b) ≫ e'.hom = e.inv ≫ a ≫ e'.hom + e.inv ≫ b ≫ e'.hom := by
  simp

omit [∀ a b : B, Preadditive (a ⟶ b)] in
theorem conj_smul {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] {Z Z' W W' : 𝒞}
    (e : Z ≅ W) (e' : Z' ≅ W') (r : k) (a : Z ⟶ Z') :
    e.inv ≫ (r • a) ≫ e'.hom = r • (e.inv ≫ a ≫ e'.hom) := by
  simp

theorem upEval_add (μ : X) {t t' : KLR.Seq ν}
    (f g : (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t')))) :
    S.upEval H M μ (f + g) = S.upEval H M μ f + S.upEval H M μ g :=
  (congrArg (fun φ => (S.upIso μ t (cond_word μ t)).inv ≫ φ ≫
    (S.upIso μ t' (cond_word μ t')).hom) (admissibleQuotientMap_add _ _ _ _ _ _ f g)).trans
    (conj_add _ _ _ _)

theorem upEval_smul (μ : X) {t t' : KLR.Seq ν} (r : k)
    (f : (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t')))) :
    S.upEval H M μ (r • f) = r • S.upEval H M μ f :=
  (congrArg (fun φ => (S.upIso μ t (cond_word μ t)).inv ≫ φ ≫
    (S.upIso μ t' (cond_word μ t')).hom) (admissibleQuotientMap_smul _ _ _ _ _ _ r f)).trans
    (conj_smul _ _ _ _)

theorem upEval_zero (μ : X) {t t' : KLR.Seq ν} :
    S.upEval H M μ (0 : (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t')))) = 0 := by
  have h := S.upEval_smul H M μ (t := t) (t' := t') (0 : k) 0
  rwa [zero_smul, zero_smul] at h

theorem upEval_id (μ : X) (t : KLR.Seq ν) :
    S.upEval H M μ (𝟙 ((pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))))) = 𝟙 _ :=
  (congrArg (fun φ => (S.upIso μ t (cond_word μ t)).inv ≫ φ ≫
    (S.upIso μ t (cond_word μ t)).hom) (admissibleQuotientMap_id _ _ _ _ _)).trans
    (conj_id _)

theorem upEval_comp (μ : X) {t t' t'' : KLR.Seq ν}
    (f : (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t'))))
    (g : (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t'))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t'')))) :
    S.upEval H M μ (f ≫ g) = S.upEval H M μ f ≫ S.upEval H M μ g :=
  (congrArg (fun φ => (S.upIso μ t (cond_word μ t)).inv ≫ φ ≫
    (S.upIso μ t'' (cond_word μ t'')).hom)
      (admissibleQuotientMap_comp _ _ _ _ _ (cond_word μ t') _ f g)).trans
    (conj_comp _ (S.upIso μ t' (cond_word μ t')) _ _ _)

variable [DecidableEq I]

/-- **The action of `U` on the Rouquier family, on upward words of weight `ν`**: the algebra
homomorphism `END_U(⊕_t E_t 1_μ) → END(⊕_t E_t)` evaluating each entry by `upEval`. -/
def upAct (μ : X) (ν : Multiset I) :
    KLR.Diagram.MatEnd (fun t : KLR.Seq ν => (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t))))
    →ₐ[k] S.WordEnd μ ν where
  toFun f i j := S.upEval H M μ (f i j)
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [KLR.Diagram.MatEnd.one_apply_self]
      exact S.upEval_id H M μ i
    · simp only [KLR.Diagram.MatEnd.one_apply_of_ne h]
      exact S.upEval_zero H M μ
  map_mul' f g := by
    ext i l
    change S.upEval H M μ (∑ j, g i j ≫ f j l) =
      ∑ j, S.upEval H M μ (g i j) ≫ S.upEval H M μ (f j l)
    exact (map_sum (AddMonoidHom.mk' (fun φ => S.upEval H M μ (t := i) (t' := l) φ)
      (S.upEval_add H M μ)) (fun j => g i j ≫ f j l) Finset.univ).trans
      (Finset.sum_congr rfl fun j _ => S.upEval_comp H M μ _ _)
  map_zero' := by ext; exact S.upEval_zero H M μ
  map_add' f g := by ext; exact S.upEval_add H M μ _ _
  commutes' r := by
    ext i j
    simp only [Algebra.algebraMap_eq_smul_one, KLR.Diagram.MatEnd.smul_apply]
    rw [upEval_smul]
    by_cases h : i = j
    · subst h
      simp only [KLR.Diagram.MatEnd.one_apply_self]
      rw [upEval_id]
    · simp only [KLR.Diagram.MatEnd.one_apply_of_ne h, smul_zero]
      rw [upEval_zero, smul_zero]

theorem upAct_single (i j : KLR.Seq ν)
    (f : (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word i))) ⟶
      (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word j)))) :
    S.upAct H M μ ν (KLR.Diagram.MatEnd.single i j f) =
      KLR.Diagram.MatEnd.single i j (S.upEval H M μ f) := by
  ext i' j'
  change S.upEval H M μ (KLR.Diagram.MatEnd.single (X := fun t : KLR.Seq ν =>
    (pres RD k).obj (ob RD μ (ups (KLR.Diagram.word t)))) i j f i' j') = _
  by_cases h : i' = i ∧ j' = j
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [KLR.Diagram.MatEnd.single_apply_of_ne _ h, KLR.Diagram.MatEnd.single_apply_of_ne _ h,
      upEval_zero]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (g : b ⟶ c), (postcomp a g).Linear k] [AdditiveWhiskering B] [DecidableEq I] in
include H in
/-- The upward KLR equations with Brundan's polynomial for the KL scalars are those of KL II's
KLR algebra `R(ν)`. -/
theorem upKLR_kl : RouqUpKLR S (KLR.klQ2 k C) := by
  have h := H.toCL (fun _ _ _ _ _ _ _ => rfl)
  rwa [CL.qCL_kl] at h

/-- **`U` acts on upward words through the KLR action of the Rouquier family**: the composite of
`R(ν) → END_U(⊕_t E_t 1_μ)` (`toUEnd`) with the evaluation `upAct` of `U` is the action
`klrAct` of `R(ν)` on the words of the Rouquier family. -/
theorem upAct_comp_toUEnd (μ : X) (ν : Multiset I) :
    (S.upAct H M μ ν).comp (toUEnd RD k μ ν) = klrAct (S.upKLR_kl H) μ := by
  refine KLR.KLRAlgebra.algHom_ext (fun i => ?_) (fun a => ?_) (fun j => ?_)
  · rw [AlgHom.comp_apply, toUEnd_e, upAct_single, upEval_id, klrAct_e]
    rfl
  · rw [AlgHom.comp_apply, klrAct_dot, wordX]
    refine (congrArg (S.upAct H M μ ν) (toUEnd_x RD k μ ν a)).trans ?_
    erw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [upAct_single, KLR.Diagram.dotE, upFunctor_diag]
    exact congrArg _ (S.upIso_dot (CL.CLScalars.kl : CL.CLScalars C k) μ i a (cond_word μ i))
  · rw [AlgHom.comp_apply, klrAct_cross, wordΨ]
    refine (congrArg (S.upAct H M μ ν) (toUEnd_ψ RD k μ ν j)).trans ?_
    erw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [upAct_single]
    by_cases hj : j + 1 < Multiset.card ν
    · erw [KLR.Diagram.crossE_def _ hj, upFunctor_diag]
      exact congrArg _ (S.upIso_cross (CL.CLScalars.kl : CL.CLScalars C k) μ i hj
        (cond_word μ i) (cond_word μ _))
    · erw [KLR.Diagram.crossE_of_le _ (by omega), Functor.map_zero, upEval_zero,
        wordCross_of_le _ _ _ (by omega)]

end Act


end RouqFamily

end Categorification.TwoRep
