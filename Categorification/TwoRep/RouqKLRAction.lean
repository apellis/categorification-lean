/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqUpKLR
import Categorification.Diagrams.KLR.DiagR

/-!
# The KLR algebra acting on words of a Rouquier family

Let `S` be an ungraded Rouquier family (`RouqFamily`) satisfying the mixed upward KLR
equations `RouqUpKLR S Q` of J. Brundan, *On the definition of Kac–Moody 2-category*,
arXiv:1501.00350v1, Definition 1.1, (1.2)--(1.4). For a weight `μ` and `ν ∈ ℕ[I]`, the words
`E_{t_0} ∘ ⋯ ∘ E_{t_{m-1}} 1_μ` with `t ∈ Seq ν` all lie in the Hom category from `μ` to
`μ + Σ ν`. This file constructs the action of the KLR algebra `R(ν)` (M. Khovanov,
A. Lauda, arXiv:0803.4121v2, §2.1, and arXiv:0804.2080v1, §3; R. Rouquier,
*2-Kac–Moody algebras*, arXiv:0812.5023) on these words, as a `k`-algebra homomorphism

  `klrAct H μ : KLRAlgebra k Q ν →ₐ[k] WordEnd S μ ν`,

where `WordEnd S μ ν` is the algebra of `Seq ν × Seq ν` matrices of 2-morphisms between
words (`MatEnd`), the endomorphism algebra of the formal direct sum of the words. No
biproducts are assumed in the Hom categories.

## Conventions

Following `RouqUpKLR`, the KLR strand at position `0` (the leftmost strand of a diagram) is
the last 1-morphism of the composite: the word of `t` is `E_{t_0} ∘ ⋯ ∘ E_{t_{m-1}}`, i.e.
`E t_{m-1} ≫ ⋯ ≫ E t_0` in diagrammatic order. The idempotent `e(t)` acts as the identity of
the word of `t`, the dot `x_a` as the dot on the `a`-th letter, and the crossing `ψ_j` as the
crossing of the letters at positions `j` and `j + 1`.

Intermediate weights are recorded in the words (`wValid`), so that the generators are
defined without transport; transports appear only when comparing two weighted words with
the same letters, which are equal by `wcell_congr`.

## Main definitions and results

* `RouqData.wcell`, `RouqData.wdot`, `RouqData.wcross`: weighted words and their dots and
  crossings, defined for the generators alone (`RouqData`); the relations on weighted words are `wdot_comm`, `wdot_wcross`,
  `wcross_comm`, `wcross_sq_self`, `wslide_left_self`, `wslide_right_self`, and, for a family
  with `H : RouqUpKLR S Q`, `wcross_sq_ne`, `wslide_left_ne`, `wslide_right_ne`, `wbraid` and
  `wbraidQ`.
* `RouqData.WordEnd S μ ν`: the matrix algebra of the words of weight `ν` at `μ`, with the
  elements `wordE t`, `wordX a` and `wordΨ j`, and the action `RouqData.klrActFree` of the
  free algebra on the generators of `R(ν)`.
* `RouqFamily.klrAct`: the action of `R(ν)`, with `klrAct_e`, `klrAct_dot`, `klrAct_cross`.
* `RouqFamily.klrAct_pol_X_pow`: if every dot satisfies `x^M = 0`, then `x_a^M` acts by zero.

The single-colour KLR relations come from the fields `square`, `braid` and `loc` of
`RouqFamily` (the nil-Hecke relations), the mixed relations from `RouqUpKLR`, and the far
commutation relations from the interchange law.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KLR TypeA

universe w v u u₁

/-! ### Weighted words -/

section Weighted

variable {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y)

/-- A list of letters with, for each letter, the weight below it is a valid weighted word from
`μ` to `μ'` if the weights are consistent. -/
abbrev wValid (μ : X) : List (I × X) → X → Prop
  | [], μ' => μ = μ'
  | (c, ν) :: L, μ' => wValid μ L ν ∧ ν + RD.iX c = μ'

/-- Exchange the letters at positions `j` and `j + 1` of a weighted word; the new
intermediate weight is the bottom weight plus the letter that moved down. -/
def wswap : ℕ → List (I × X) → List (I × X)
  | 0, (c, _) :: (d, ν) :: L => (d, ν + RD.iX c) :: (c, ν) :: L
  | j + 1, p :: L => p :: wswap j L
  | _, L => L

variable {RD}

theorem wValid_wswap {μ : X} : ∀ (j : ℕ) (L : List (I × X)) {μ' : X},
    wValid RD μ L μ' → wValid RD μ (wswap RD j L) μ'
  | 0, (_, ν₁) :: (_, ν₂) :: L, μ', h =>
    And.intro (And.intro h.1.1 rfl) (by rw [← h.2, ← h.1.2, add_right_comm])
  | j + 1, (_, _) :: L, _, h => And.intro (wValid_wswap j L h.1) h.2
  | 0, [], _, h => h
  | 0, [_], _, h => h
  | _ + 1, [], _, h => h

theorem wValid_of_eq {μ μ' μ'' : X} {L : List (I × X)} (h : wValid RD μ L μ') (e : μ' = μ'') :
    wValid RD μ L μ'' := e ▸ h

variable (RD)

/-- The top weight of the canonical weighted word of a list of letters. -/
def ctop (μ : X) : List I → X
  | [] => μ
  | c :: l => ctop μ l + RD.iX c

/-- The canonical weighted word of a list of letters, starting at `μ`. -/
def canon (μ : X) : List I → List (I × X)
  | [] => []
  | c :: l => (c, ctop RD μ l) :: canon μ l

/-- The list exchange of the letters at positions `j` and `j + 1`. -/
def lswap : ℕ → List I → List I
  | 0, c :: d :: l => d :: c :: l
  | j + 1, c :: l => c :: lswap j l
  | _, l => l

variable {RD}

theorem wValid_canon (μ : X) : ∀ l : List I, wValid RD μ (canon RD μ l) (ctop RD μ l)
  | [] => rfl
  | _ :: l => And.intro (wValid_canon μ l) rfl

theorem ctop_eq (μ : X) : ∀ l : List I, ctop RD μ l = μ + (l.map RD.iX).sum
  | [] => by simp [ctop]
  | c :: l => by rw [ctop, ctop_eq μ l, List.map_cons, List.sum_cons]; abel

theorem ctop_lswap (μ : X) : ∀ (j : ℕ) (l : List I), ctop RD μ (lswap j l) = ctop RD μ l
  | 0, c :: d :: l => by simp only [lswap, ctop]; rw [add_right_comm]
  | j + 1, c :: l => by simp only [lswap, ctop]; rw [ctop_lswap μ j l]
  | 0, [] => rfl
  | 0, [_] => rfl
  | _ + 1, [] => rfl

theorem wswap_canon (μ : X) : ∀ (j : ℕ) (l : List I),
    wswap RD j (canon RD μ l) = canon RD μ (lswap j l)
  | 0, c :: d :: l => rfl
  | j + 1, c :: l => by
    simp only [canon, lswap, wswap]
    rw [wswap_canon μ j l, ctop_lswap]
  | 0, [] => rfl
  | 0, [_] => rfl
  | _ + 1, [] => rfl

theorem lswap_eq : ∀ (j : ℕ) (l : List I) (h : j + 1 < l.length),
    lswap j l = l.take j ++ [l[j + 1], l[j]] ++ l.drop (j + 2)
  | 0, _ :: _ :: _, _ => rfl
  | j + 1, c :: l, h => by
    simp only [lswap, List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons,
      List.cons_append]
    rw [lswap_eq j l (by simpa using h)]
  | 0, [], h => by simp at h
  | 0, [_], h => by simp at h
  | _ + 1, [], h => by simp at h

theorem wswap_comm : ∀ (j l : ℕ) (L : List (I × X)), j + 1 < l →
    wswap RD l (wswap RD j L) = wswap RD j (wswap RD l L)
  | 0, l + 2, (_, _) :: (_, _) :: _, _ => rfl
  | j + 1, l + 1, p :: L, h => by
    simp only [wswap, List.cons.injEq, true_and]
    exact wswap_comm j l L (by omega)
  | 0, l + 2, [], _ => rfl
  | 0, l + 2, [_], _ => by cases l <;> rfl
  | _ + 1, _ + 1, [], _ => rfl
  | 0, 0, _, h => by omega
  | 0, 1, _, h => by omega
  | _ + 1, 0, _, h => by omega

theorem wswap_wswap {μ : X} : ∀ (j : ℕ) (L : List (I × X)) {μ' : X},
    wValid RD μ L μ' → wswap RD j (wswap RD j L) = L
  | 0, (_, _) :: (_, _) :: _, _, h => by simp only [wswap]; rw [h.1.2]
  | j + 1, (_, _) :: L, _, h => by simp only [wswap]; rw [wswap_wswap j L h.1]
  | 0, [], _, _ => rfl
  | 0, [_], _, _ => rfl
  | _ + 1, [], _, _ => rfl

theorem wswap_succ_eq {j : ℕ} {p : I × X} {L M : List (I × X)}
    (e : wswap RD (j + 1) (p :: L) = M) : ∃ M', M = p :: M' ∧ wswap RD j L = M' :=
  ⟨wswap RD j L, e.symm, rfl⟩

theorem wswap_succ_cons {j : ℕ} {p : I × X} {L M : List (I × X)}
    (e : wswap RD (j + 1) (p :: L) = p :: M) : wswap RD j L = M := by
  simpa [wswap] using e

variable (RD) in
/-- The top weight `μ + Σ ν` of the words of weight `ν` at `μ`. -/
def wtop (μ : X) (ν : Multiset I) : X := μ + (ν.map RD.iX).sum

variable (RD) in
/-- The canonical weighted word of the sequence `t`, starting at `μ`. -/
abbrev wordL (μ : X) {ν : Multiset I} (t : Seq ν) : List (I × X) := canon RD μ (Diagram.word t)

theorem ctop_word (μ : X) {ν : Multiset I} (t : Seq ν) :
    ctop RD μ (Diagram.word t) = wtop RD μ ν := by
  have : ((List.ofFn t.1).map RD.iX).sum = (ν.map RD.iX).sum := by
    conv_rhs => rw [← t.2]
    rw [Fin.univ_val_map, Multiset.map_coe, Multiset.sum_coe]
  rw [ctop_eq, Diagram.word, this, wtop]

theorem wValid_wordL (μ : X) {ν : Multiset I} (t : Seq ν) :
    wValid RD μ (wordL RD μ t) (wtop RD μ ν) :=
  wValid_of_eq (wValid_canon μ _) (ctop_word μ t)

theorem wswap_wordL (μ : X) {ν : Multiset I} (t : Seq ν) {j : ℕ}
    (hj : j + 1 < Multiset.card ν) :
    wswap RD j (wordL RD μ t) = wordL RD μ (sadj (Multiset.card ν) j • t) := by
  unfold wordL
  rw [wswap_canon, lswap_eq _ _ (by simpa using hj), Diagram.word_sadj t hj]
  simp only [Diagram.getElem_word]

@[simp] theorem length_canon (μ : X) : ∀ l : List I, (canon RD μ l).length = l.length
  | [] => rfl
  | _ :: l => by rw [canon, List.length_cons, length_canon μ l, List.length_cons]

theorem map_fst_canon (μ : X) : ∀ l : List I, (canon RD μ l).map Prod.fst = l
  | [] => rfl
  | c :: l => by rw [canon, List.map_cons, map_fst_canon μ l]

theorem wordL_fst (μ : X) {ν : Multiset I} (t : Seq ν) (a : ℕ) (ha : a < Multiset.card ν) :
    ((wordL RD μ t).map Prod.fst)[a]? = some (t.1 ⟨a, ha⟩) := by
  rw [map_fst_canon, Diagram.word, List.getElem?_ofFn]
  simp [ha]

end Weighted

/-! ### Words of a Rouquier family -/

theorem comp_eqToHom_self {𝒞 : Type*} [Category 𝒞] {Z Z' : 𝒞} (f : Z ⟶ Z') (p : Z' = Z') :
    f ≫ eqToHom p = f := by
  simp

section Words

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}

namespace RouqData

variable (S : RouqData (B := B) RD) (μ : X)

/-- The 1-morphism of a valid weighted word: `E c₀ ∘ ⋯ ∘ E c_{n-1}` from `μ` to `μ'`. -/
def wcell : (L : List (I × X)) → (μ' : X) → wValid RD μ L μ' → (S.obj μ ⟶ S.obj μ')
  | [], _, h => eqToHom (congrArg S.obj h)
  | (c, ν) :: L, _, h => wcell L ν h.1 ≫ S.E c h.2

omit [∀ a b : B, Preadditive (a ⟶ b)] in
theorem wcell_congr {L L' : List (I × X)} (e : L = L') {μ' : X} (h : wValid RD μ L μ')
    (h' : wValid RD μ L' μ') : S.wcell μ L μ' h = S.wcell μ L' μ' h' := by
  subst e; rfl

/-- The dot on the `a`-th letter of a weighted word (zero if out of range). -/
def wdot : (a : ℕ) → (L : List (I × X)) → (μ' : X) → (h : wValid RD μ L μ') →
    (S.wcell μ L μ' h ⟶ S.wcell μ L μ' h)
  | 0, (c, ν) :: L, _, h => S.wcell μ L ν h.1 ◁ S.dot c h.2
  | a + 1, (c, ν) :: L, _, h => wdot a L ν h.1 ▷ S.E c h.2
  | 0, [], _, _ => 0
  | _ + 1, [], _, _ => 0

/-- The crossing of the letters at positions `j` and `j + 1` of a weighted word (zero if out
of range). -/
def wcross : (j : ℕ) → (L : List (I × X)) → (μ' : X) → (h : wValid RD μ L μ') →
    (S.wcell μ L μ' h ⟶ S.wcell μ (wswap RD j L) μ' (wValid_wswap j L h))
  | 0, (c, ν₁) :: (d, ν₂) :: L, μ', h =>
    (α_ _ _ _).hom ≫ S.wcell μ L ν₂ h.1.1 ◁ S.cross c d h.1.2 h.2 rfl
      (by rw [← h.2, ← h.1.2, add_right_comm]) ≫ (α_ _ _ _).inv
  | j + 1, (c, ν) :: L, _, h => wcross j L ν h.1 ▷ S.E c h.2
  | 0, [], _, _ => 0
  | 0, [_], _, _ => 0
  | _ + 1, [], _, _ => 0

/-- The crossing of the letters at positions `j` and `j + 1`, followed by the comparison with
a given weighted word `M` with the same letters and weights. -/
def wcrossTo (j : ℕ) (L M : List (I × X)) (μ' : X) (e : wswap RD j L = M)
    (h : wValid RD μ L μ') (hM : wValid RD μ M μ') : S.wcell μ L μ' h ⟶ S.wcell μ M μ' hM :=
  S.wcross μ j L μ' h ≫ eqToHom (S.wcell_congr μ e _ hM)

theorem wcrossTo_zero (c d : I) (ν₁ ν₂ b : X) (R : List (I × X)) (μ' : X)
    (e : wswap RD 0 ((c, ν₁) :: (d, ν₂) :: R) = (d, b) :: (c, ν₂) :: R)
    (h : wValid RD μ ((c, ν₁) :: (d, ν₂) :: R) μ') (hM : wValid RD μ ((d, b) :: (c, ν₂) :: R) μ')
    (hb : ν₂ + RD.iX c = b) :
    S.wcrossTo μ 0 _ _ μ' e h hM = (α_ _ _ _).hom ≫
      S.wcell μ R ν₂ h.1.1 ◁ S.cross c d h.1.2 h.2 hb hM.2 ≫ (α_ _ _ _).inv := by
  subst hb
  exact comp_eqToHom_self _ _

theorem wcrossTo_succ (j : ℕ) (c : I) (ν : X) (L M : List (I × X)) (μ' : X)
    (e : wswap RD (j + 1) ((c, ν) :: L) = (c, ν) :: M)
    (h : wValid RD μ ((c, ν) :: L) μ') (hM : wValid RD μ ((c, ν) :: M) μ') :
    S.wcrossTo μ (j + 1) _ _ μ' e h hM =
      S.wcrossTo μ j L M ν (by simpa [wswap] using e) h.1 hM.1 ▷ S.E c h.2 := by
  have e' : wswap RD j L = M := by simpa [wswap] using e
  subst e'
  rw [wcrossTo, wcrossTo, comp_whiskerRight, eqToHom_whiskerRight]
  rfl

theorem wcrossTo_zero_rfl (c d : I) (ν₁ ν₂ : X) (R : List (I × X)) (μ' : X)
    (e : wswap RD 0 ((c, ν₁) :: (d, ν₂) :: R) = (d, ν₂ + RD.iX c) :: (c, ν₂) :: R)
    (h : wValid RD μ ((c, ν₁) :: (d, ν₂) :: R) μ')
    (hM : wValid RD μ ((d, ν₂ + RD.iX c) :: (c, ν₂) :: R) μ') :
    S.wcrossTo μ 0 _ _ μ' e h hM = (α_ _ _ _).hom ≫
      S.wcell μ R ν₂ h.1.1 ◁ S.cross c d h.1.2 h.2 rfl hM.2 ≫ (α_ _ _ _).inv :=
  S.wcrossTo_zero μ c d ν₁ ν₂ _ R μ' e h hM rfl

@[simp] theorem wcrossTo_rfl (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ')
    (hM : wValid RD μ (wswap RD j L) μ') :
    S.wcrossTo μ j L (wswap RD j L) μ' rfl h hM = S.wcross μ j L μ' h :=
  comp_eqToHom_self _ _

theorem wswap_of_le : ∀ (j : ℕ) (L : List (I × X)), L.length ≤ j + 1 → wswap RD j L = L
  | 0, [], _ => rfl
  | 0, [_], _ => rfl
  | 0, _ :: _ :: _, h => by simp at h
  | j + 1, [], _ => rfl
  | j + 1, p :: L, h => by
    simp only [wswap, List.cons.injEq, true_and]
    exact wswap_of_le j L (by simpa using h)

variable [AdditiveWhiskering B] in
theorem wcross_of_le : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ'),
    L.length ≤ j + 1 → S.wcross μ j L μ' h = 0
  | 0, [], _, _, _ => rfl
  | 0, [_], _, _, _ => rfl
  | 0, _ :: _ :: _, _, _, hl => by simp at hl
  | j + 1, [], _, _, _ => rfl
  | j + 1, (c, ν) :: L, _, h, hl => by
    simp only [wcross]
    rw [wcross_of_le j L ν h.1 (by simpa using hl)]
    exact AdditiveWhiskering.zero_whiskerRight _ _ _

end RouqData

end Words

section Coh

variable {B : Type u} [Bicategory.{w, v} B]

/-- Whiskering a two-letter 2-morphism by `W` on the left, reassociated. -/
def wl2 {a b c c' d : B} (W : a ⟶ b) {f : b ⟶ c} {g : b ⟶ c'} {f' : c ⟶ d} {g' : c' ⟶ d}
    (η : f ≫ f' ⟶ g ≫ g') : (W ≫ f) ≫ f' ⟶ (W ≫ g) ≫ g' :=
  (α_ W f f').hom ≫ W ◁ η ≫ (α_ W g g').inv

/-- Whiskering a three-letter 2-morphism by `W` on the left, reassociated. -/
def wl3 {a b c c' d d' e : B} (W : a ⟶ b) {f : b ⟶ c} {f' : b ⟶ c'} {g : c ⟶ d}
    {g' : c' ⟶ d'} {h : d ⟶ e} {h' : d' ⟶ e}
    (η : f ≫ (g ≫ h) ⟶ f' ≫ (g' ≫ h')) : ((W ≫ f) ≫ g) ≫ h ⟶ ((W ≫ f') ≫ g') ≫ h' :=
  (α_ (W ≫ f) g h).hom ≫ (α_ W f (g ≫ h)).hom ≫ W ◁ η ≫ (α_ W f' (g' ≫ h')).inv ≫
    (α_ (W ≫ f') g' h').inv

variable {a b : B} (W : a ⟶ b)

theorem wl2_comp {c₁ c₂ c₃ d : B} {f : b ⟶ c₁} {g : b ⟶ c₂} {h : b ⟶ c₃} {f' : c₁ ⟶ d}
    {g' : c₂ ⟶ d} {h' : c₃ ⟶ d} (η : f ≫ f' ⟶ g ≫ g') (θ : g ≫ g' ⟶ h ≫ h') :
    wl2 W η ≫ wl2 W θ = wl2 W (η ≫ θ) := by
  simp [wl2]

theorem wl2_whiskerLeft {c d : B} (f : b ⟶ c) {f' g' : c ⟶ d} (x : f' ⟶ g') :
    wl2 W (f ◁ x) = (W ≫ f) ◁ x := by
  unfold wl2; bicategory

theorem wl2_whiskerRight {c d : B} {f g : b ⟶ c} (x : f ⟶ g) (f' : c ⟶ d) :
    wl2 W (x ▷ f') = (W ◁ x) ▷ f' := by
  unfold wl2; bicategory

theorem wl3_comp {c₁ c₂ c₃ d₁ d₂ d₃ e : B} {f : b ⟶ c₁} {f' : b ⟶ c₂} {f'' : b ⟶ c₃}
    {g : c₁ ⟶ d₁} {g' : c₂ ⟶ d₂} {g'' : c₃ ⟶ d₃} {h : d₁ ⟶ e} {h' : d₂ ⟶ e} {h'' : d₃ ⟶ e}
    (η : f ≫ (g ≫ h) ⟶ f' ≫ (g' ≫ h')) (θ : f' ≫ (g' ≫ h') ⟶ f'' ≫ (g'' ≫ h'')) :
    wl3 W η ≫ wl3 W θ = wl3 W (η ≫ θ) := by
  simp [wl3]

theorem wl3_dot₀ {c d e : B} (f : b ⟶ c) (g : c ⟶ d) {h h' : d ⟶ e} (x : h ⟶ h') :
    wl3 W (f ◁ g ◁ x) = ((W ≫ f) ≫ g) ◁ x := by
  unfold wl3; bicategory

theorem wl3_dot₁ {c d e : B} (f : b ⟶ c) {g g' : c ⟶ d} (x : g ⟶ g') (h : d ⟶ e) :
    wl3 W (f ◁ (x ▷ h)) = ((W ≫ f) ◁ x) ▷ h := by
  unfold wl3; bicategory

theorem wl3_dot₂ {c d e : B} {f f' : b ⟶ c} (x : f ⟶ f') (g : c ⟶ d) (h : d ⟶ e) :
    wl3 W (x ▷ (g ≫ h)) = ((W ◁ x) ▷ g) ▷ h := by
  unfold wl3; bicategory

theorem wl2_id {c d : B} (f : b ⟶ c) (f' : c ⟶ d) :
    wl2 W (𝟙 (f ≫ f')) = 𝟙 _ := by
  simp [wl2]

/-- The left-hand side of the braid relations (Brundan (1.4)), whiskered by `W`. -/
theorem wl3_braid_left {c₁ c₂ d₁ d₂ d₄ e : B} {f : b ⟶ c₁} {f' : b ⟶ c₂}
    {g : c₁ ⟶ d₁} {g' : c₁ ⟶ d₂} {g'' : c₂ ⟶ d₂} {g''' : c₂ ⟶ d₄}
    {h : d₁ ⟶ e} {h' : d₂ ⟶ e} {h'' : d₄ ⟶ e}
    (x : g ≫ h ⟶ g' ≫ h') (y : f ≫ g' ⟶ f' ≫ g'') (z : g'' ≫ h' ⟶ g''' ≫ h'') :
    wl3 W (f ◁ x ≫ ((α_ f g' h').inv ≫ y ▷ h' ≫ (α_ f' g'' h').hom) ≫ f' ◁ z) =
      wl2 (W ≫ f) x ≫ wl2 W y ▷ h' ≫ wl2 (W ≫ f') z := by
  unfold wl3 wl2; bicategory

/-- The right-hand side of the braid relations (Brundan (1.4)), whiskered by `W`. -/
theorem wl3_braid_right {c₁ c₂ c₃ d₁ d₃ e : B} {f : b ⟶ c₁} {f' : b ⟶ c₂}
    {f'' : b ⟶ c₃} {g : c₁ ⟶ d₁} {g' : c₂ ⟶ d₁} {g''' : c₃ ⟶ d₃}
    {h : d₁ ⟶ e} {h₁ : d₃ ⟶ e} {g₁ : c₂ ⟶ d₃}
    (y : f ≫ g ⟶ f' ≫ g') (x : g' ≫ h ⟶ g₁ ≫ h₁) (z : f' ≫ g₁ ⟶ f'' ≫ g''') :
    wl3 W (((α_ f g h).inv ≫ y ▷ h ≫ (α_ f' g' h).hom) ≫ f' ◁ x ≫
        ((α_ f' g₁ h₁).inv ≫ z ▷ h₁ ≫ (α_ f'' g''' h₁).hom)) =
      wl2 W y ▷ h ≫ wl2 (W ≫ f') x ≫ wl2 W z ▷ h₁ := by
  unfold wl3 wl2; bicategory

theorem whiskerLeft_pow {c : B} (f : a ⟶ b) {g : b ⟶ c} (x : g ⟶ g) (n : ℕ) :
    End.of (f ◁ x) ^ n = End.of (f ◁ End.asHom (End.of x ^ n)) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact (whiskerLeft_id f g).symm
  | succ n ih => rw [pow_succ, pow_succ, ih]; exact (whiskerLeft_comp f _ _).symm

theorem whiskerRight_pow {c : B} {f : a ⟶ b} (x : f ⟶ f) (g : b ⟶ c) (n : ℕ) :
    End.of (x ▷ g) ^ n = End.of (End.asHom (End.of x ^ n) ▷ g) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact (id_whiskerRight f g).symm
  | succ n ih => rw [pow_succ, pow_succ, ih]; exact (comp_whiskerRight _ _ g).symm

end Coh

section CohAdd

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [AdditiveWhiskering B] {a b : B} (W : a ⟶ b)

theorem AdditiveWhiskering.whiskerLeft_sub {c : B} {g h : b ⟶ c} (η θ : g ⟶ h) :
    W ◁ (η - θ) = W ◁ η - W ◁ θ :=
  map_sub (AdditiveWhiskering.whiskerLeftAddHom W g h) η θ

theorem AdditiveWhiskering.sub_whiskerRight {c : B} {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c) :
    (η - θ) ▷ h = η ▷ h - θ ▷ h :=
  map_sub (AdditiveWhiskering.whiskerRightAddHom f g h) η θ

theorem wl2_sub {c c' d : B} {f : b ⟶ c} {g : b ⟶ c'} {f' : c ⟶ d} {g' : c' ⟶ d}
    (η θ : f ≫ f' ⟶ g ≫ g') : wl2 W η - wl2 W θ = wl2 W (η - θ) := by
  simp only [wl2, AdditiveWhiskering.whiskerLeft_sub, Preadditive.comp_sub,
    Preadditive.sub_comp]

theorem wl3_sub {c c' d d' e : B} {f : b ⟶ c} {f' : b ⟶ c'} {g : c ⟶ d}
    {g' : c' ⟶ d'} {h : d ⟶ e} {h' : d' ⟶ e}
    (η θ : f ≫ (g ≫ h) ⟶ f' ≫ (g' ≫ h')) : wl3 W η - wl3 W θ = wl3 W (η - θ) := by
  simp only [wl3, AdditiveWhiskering.whiskerLeft_sub, Preadditive.comp_sub,
    Preadditive.sub_comp]

theorem wl2_zero {c c' d : B} {f : b ⟶ c} {g : b ⟶ c'} {f' : c ⟶ d} {g' : c' ⟶ d} :
    wl2 W (0 : f ≫ f' ⟶ g ≫ g') = 0 := by
  simp [wl2, AdditiveWhiskering.whiskerLeft_zero]

end CohAdd

/-! ### Whiskering as algebra homomorphisms -/

section Alg

variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]

variable (k) in
/-- Right whiskering as an algebra homomorphism of endomorphism algebras. -/
def endWR {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : End f →ₐ[k] End (f ≫ g) where
  toFun η := (η ▷ g : f ≫ g ⟶ f ≫ g)
  map_one' := id_whiskerRight f g
  map_mul' η θ := comp_whiskerRight θ η g
  map_zero' := AdditiveWhiskering.zero_whiskerRight f f g
  map_add' η θ := AdditiveWhiskering.add_whiskerRight η θ g
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change (r • 𝟙 f) ▷ g = r • 𝟙 (f ≫ g)
    rw [show (r • 𝟙 f) ▷ g = r • (𝟙 f ▷ g) from (postcomp a g).map_smul r (𝟙 f),
      id_whiskerRight]

variable (k) in
/-- Left whiskering as an algebra homomorphism of endomorphism algebras. -/
def endWL {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : End g →ₐ[k] End (f ≫ g) where
  toFun η := (f ◁ η : f ≫ g ⟶ f ≫ g)
  map_one' := whiskerLeft_id f g
  map_mul' η θ := whiskerLeft_comp f θ η
  map_zero' := AdditiveWhiskering.whiskerLeft_zero f g g
  map_add' η θ := AdditiveWhiskering.whiskerLeft_add f η θ
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change f ◁ (r • 𝟙 g) = r • 𝟙 (f ≫ g)
    rw [show f ◁ (r • 𝟙 g) = r • (f ◁ 𝟙 g) from (precomp c f).map_smul r (𝟙 g),
      whiskerLeft_id]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
@[simp] theorem endWR_apply {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (η : End f) :
    endWR k f g η = η ▷ g := rfl

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
@[simp] theorem endWL_apply {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (η : End g) :
    endWL k f g η = f ◁ η := rfl

variable (k) in
/-- Conjugation by an isomorphism, as an algebra homomorphism. -/
def endConj {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞] {Z Z' : 𝒞} (e : Z ≅ Z') :
    End Z →ₐ[k] End Z' where
  toFun φ := (e.inv ≫ φ ≫ e.hom : Z' ⟶ Z')
  map_one' := by
    change e.inv ≫ 𝟙 Z ≫ e.hom = 𝟙 Z'
    simp
  map_mul' φ ψ := by
    change e.inv ≫ (ψ ≫ φ) ≫ e.hom = (e.inv ≫ ψ ≫ e.hom) ≫ (e.inv ≫ φ ≫ e.hom)
    simp
  map_zero' := by
    change e.inv ≫ (0 : Z ⟶ Z) ≫ e.hom = 0
    simp
  map_add' φ ψ := by
    change e.inv ≫ ((φ : Z ⟶ Z) + (ψ : Z ⟶ Z)) ≫ e.hom =
      (e.inv ≫ φ ≫ e.hom : Z' ⟶ Z') + (e.inv ≫ ψ ≫ e.hom : Z' ⟶ Z')
    rw [Preadditive.add_comp, Preadditive.comp_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change e.inv ≫ (r • 𝟙 Z) ≫ e.hom = r • 𝟙 Z'
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.inv_hom_id]

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
@[simp] theorem endConj_apply {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
    {Z Z' : 𝒞} (e : Z ≅ Z') (φ : End Z) : endConj k e φ = (e.inv ≫ φ ≫ e.hom : Z' ⟶ Z') := rfl

variable (k) in
/-- `wl2` as an algebra homomorphism. -/
def wl2Alg {a b c d : B} (W : a ⟶ b) (f : b ⟶ c) (f' : c ⟶ d) :
    End (f ≫ f') →ₐ[k] End ((W ≫ f) ≫ f') :=
  (endConj k (α_ W f f').symm).comp (endWL k W (f ≫ f'))

variable (k) in
/-- `wl3` as an algebra homomorphism. -/
def wl3Alg {a b c d e : B} (W : a ⟶ b) (f : b ⟶ c) (g : c ⟶ d) (h : d ⟶ e) :
    End (f ≫ (g ≫ h)) →ₐ[k] End (((W ≫ f) ≫ g) ≫ h) :=
  (endConj k ((α_ (W ≫ f) g h) ≪≫ (α_ W f (g ≫ h))).symm).comp (endWL k W (f ≫ (g ≫ h)))

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
theorem wl2Alg_apply {a b c d : B} (W : a ⟶ b) (f : b ⟶ c) (f' : c ⟶ d) (η : End (f ≫ f')) :
    wl2Alg k W f f' η = wl2 W η := rfl

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
theorem wl3Alg_apply {a b c d e : B} (W : a ⟶ b) (f : b ⟶ c) (g : c ⟶ d) (h : d ⟶ e)
    (η : End (f ≫ (g ≫ h))) : wl3Alg k W f g h η = wl3 W η := by
  simp [wl3Alg, wl3]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem ncEval_whiskerRight {n : ℕ} {a b c : B} {f : a ⟶ b} (h : b ⟶ c) (y : Fin n → End f)
    (p : MvPolynomial (Fin n) k) :
    (ncEval (A := End f) y p) ▷ h = ncEval (A := End (f ≫ h)) (fun t => (y t : f ⟶ f) ▷ h) p :=
  (endWR k f h).map_ncEval y p

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem ncEval_whiskerRight₂ {a b c : B} {f : a ⟶ b} (h : b ⟶ c) (y₁ y₂ : End f)
    (p : MvPolynomial (Fin 2) k) :
    (ncEval (A := End f) ![y₁, y₂] p) ▷ h =
      ncEval (A := End (f ≫ h)) ![(y₁ : f ⟶ f) ▷ h, (y₂ : f ⟶ f) ▷ h] p := by
  rw [ncEval_whiskerRight]; congr 1; funext t; fin_cases t <;> rfl

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k] in
theorem ncEval_whiskerRight₃ {a b c : B} {f : a ⟶ b} (h : b ⟶ c) (y₁ y₂ y₃ : End f)
    (p : MvPolynomial (Fin 3) k) :
    (ncEval (A := End f) ![y₁, y₂, y₃] p) ▷ h =
      ncEval (A := End (f ≫ h)) ![(y₁ : f ⟶ f) ▷ h, (y₂ : f ⟶ f) ▷ h, (y₃ : f ⟶ f) ▷ h] p := by
  rw [ncEval_whiskerRight]; congr 1; funext t; fin_cases t <;> rfl

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
theorem wl2_ncEval₂ {a b c d : B} (W : a ⟶ b) {f : b ⟶ c} {f' : c ⟶ d} (y₁ y₂ : End (f ≫ f'))
    (p : MvPolynomial (Fin 2) k) :
    wl2 W (ncEval (A := End (f ≫ f')) ![y₁, y₂] p) =
      ncEval (A := End ((W ≫ f) ≫ f')) ![wl2 W y₁, wl2 W y₂] p := by
  rw [← wl2Alg_apply (k := k), AlgHom.map_ncEval]; congr 1; funext t; fin_cases t <;> rfl

omit [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
theorem wl3_ncEval₃ {a b c d e : B} (W : a ⟶ b) {f : b ⟶ c} {g : c ⟶ d} {h : d ⟶ e}
    (y₁ y₂ y₃ : End (f ≫ (g ≫ h))) (p : MvPolynomial (Fin 3) k) :
    wl3 W (ncEval (A := End (f ≫ (g ≫ h))) ![y₁, y₂, y₃] p) =
      ncEval (A := End (((W ≫ f) ≫ g) ≫ h)) ![wl3 W y₁, wl3 W y₂, wl3 W y₃] p := by
  rw [← wl3Alg_apply (k := k), AlgHom.map_ncEval]
  congr 1; funext t; fin_cases t <;> simp [wl3Alg_apply]

end Alg

/-! ### Relations on weighted words -/

section ListRel

variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)] [AdditiveWhiskering B]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  {I : Type*} {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : WeightDatum C X Y}

namespace RouqData

variable (S : RouqData (B := B) RD) (μ : X)

omit [AdditiveWhiskering B] in
/-- Dots on a weighted word commute. -/
theorem wdot_comm : ∀ (a b : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ'),
    S.wdot μ a L μ' h ≫ S.wdot μ b L μ' h = S.wdot μ b L μ' h ≫ S.wdot μ a L μ' h
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, (_, _) :: _, _, _ => whisker_exchange _ _
  | _ + 1, 0, (_, _) :: _, _, _ => (whisker_exchange _ _).symm
  | a + 1, b + 1, (c, ν) :: L, _, h => by
    dsimp only [wdot, wcell]
    rw [← comp_whiskerRight, wdot_comm a b L ν h.1, comp_whiskerRight]
  | _ + 1, _, [], _, _ => by simp [wdot]
  | 0, _ + 1, [], _, _ => by simp [wdot]

omit [AdditiveWhiskering B] in
/-- A dot away from a crossing commutes with it. -/
theorem wdot_wcross : ∀ (a j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ'),
    a ≠ j → a ≠ j + 1 →
    S.wdot μ a L μ' h ≫ S.wcross μ j L μ' h =
      S.wcross μ j L μ' h ≫ S.wdot μ a (wswap RD j L) μ' (wValid_wswap j L h)
  | a + 2, 0, (c, ν₁) :: (d, ν₂) :: R, μ', h, _, _ => by
    dsimp only [wdot, wcross, wswap, wcell]
    simp only [Category.assoc]
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
      associator_inv_naturality_left]
  | 0, j + 1, (c, ν) :: L, _, h, _, _ => whisker_exchange _ _
  | a + 1, j + 1, (c, ν) :: L, _, h, h₁, h₂ => by
    dsimp only [wdot, wcross, wswap, wcell]
    rw [← comp_whiskerRight, wdot_wcross a j L ν h.1 (by omega) (by omega), comp_whiskerRight]
  | 0, 0, _, _, _, h₁, _ => absurd rfl h₁
  | 1, 0, _, _, _, _, h₂ => absurd rfl h₂
  | _ + 2, 0, [], _, _, _, _ => by simp [wcross]
  | _ + 2, 0, [_], _, _, _, _ => by simp [wcross]
  | _, _ + 1, [], _, _, _, _ => by simp [wcross]

omit [AdditiveWhiskering B] [∀ a b : B, Preadditive (a ⟶ b)] in
theorem eqToHom_wcell_cons (c : I) (ν : X) {L₁ L₂ : List (I × X)} (e : L₁ = L₂) {μ' : X}
    (h₁ : wValid RD μ ((c, ν) :: L₁) μ') (h₂ : wValid RD μ ((c, ν) :: L₂) μ')
    (p : S.wcell μ ((c, ν) :: L₁) μ' h₁ = S.wcell μ ((c, ν) :: L₂) μ' h₂) :
    eqToHom p = eqToHom (S.wcell_congr μ e h₁.1 h₂.1) ▷ S.E c h₁.2 := by
  subst e; simp; rfl

/-- Distant crossings commute. -/
theorem wcross_comm : ∀ (j l : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ')
    (hjl : j + 1 < l),
    S.wcross μ j L μ' h ≫ S.wcross μ l (wswap RD j L) μ' (wValid_wswap j L h) ≫
      eqToHom (S.wcell_congr μ (wswap_comm j l L hjl) _ _) =
    S.wcross μ l L μ' h ≫ S.wcross μ j (wswap RD l L) μ' (wValid_wswap l L h)
  | 0, l + 2, (c, ν₁) :: (d, ν₂) :: R, μ', h, _ => by
    dsimp only [wcross, wswap, wcell]
    simp only [Category.assoc]
    erw [comp_eqToHom_self]
    symm
    rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
      associator_inv_naturality_left]
  | j + 1, l + 1, (c, ν) :: L, μ', h, hjl => by
    have ih := congrArg (· ▷ S.E c h.2) (wcross_comm j l L ν h.1 (by omega))
    simp only [comp_whiskerRight, eqToHom_whiskerRight] at ih
    exact ih
  | 0, l + 2, [], _, _, _ => by simp [wcross]
  | 0, l + 2, [_], _, _, _ => by
    simp [wcross, AdditiveWhiskering.zero_whiskerRight]
    exact Limits.zero_comp.symm
  | _ + 1, _ + 1, [], _, _, _ => by simp [wcross]
  | 0, 0, _, _, _, h => by omega
  | 0, 1, _, _, _, h => by omega
  | _ + 1, 0, _, _, _, h => by omega

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
@[reassoc]
theorem eqToHom_wdot (a : ℕ) {L L' : List (I × X)} (e : L = L') {μ' : X}
    (h : wValid RD μ L μ') (h' : wValid RD μ L' μ') :
    eqToHom (S.wcell_congr μ e h h') ≫ S.wdot μ a L' μ' h' =
      S.wdot μ a L μ' h ≫ eqToHom (S.wcell_congr μ e h h') := by
  subst e; simp

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
@[reassoc]
theorem eqToHom_wcross (j : ℕ) {L L' : List (I × X)} (e : L = L') {μ' : X}
    (h : wValid RD μ L μ') (h' : wValid RD μ L' μ') :
    eqToHom (S.wcell_congr μ e h h') ≫ S.wcross μ j L' μ' h' =
      S.wcross μ j L μ' h ≫ eqToHom (S.wcell_congr μ (congrArg (wswap RD j) e)
        (wValid_wswap j L h) (wValid_wswap j L' h')) := by
  subst e; simp

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
theorem wcrossTo_comp_eqToHom (j : ℕ) {L M M' : List (I × X)} {μ' : X} (e : wswap RD j L = M)
    (h : wValid RD μ L μ') (hM : wValid RD μ M μ') (hM' : wValid RD μ M' μ') (e' : M = M')
    (p : S.wcell μ M μ' hM = S.wcell μ M' μ' hM') :
    S.wcrossTo μ j L M μ' e h hM ≫ eqToHom p = S.wcrossTo μ j L M' μ' (e.trans e') h hM' := by
  subst e'; simp [wcrossTo]

end RouqData

namespace RouqFamily

open RouqData

variable (S : RouqFamily (B := B) RD) (μ : X)

/-- The same-colour quadratic relation `ψ_j² = 0`. -/
theorem wcross_sq_self : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ')
    (c : I), (L.map Prod.fst)[j]? = some c → (L.map Prod.fst)[j + 1]? = some c →
    S.wcross μ j L μ' h ≫ S.wcross μ j (wswap RD j L) μ' (wValid_wswap j L h) = 0
  | 0, (c₁, ν₁) :: (c₂, ν₂) :: R, μ', h, c, h₁, h₂ => by
    simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at h₁ h₂
    subst h₁ h₂
    obtain ⟨⟨hR, rfl⟩, rfl⟩ := h
    dsimp only [wcross, wswap, wcell]
    change wl2 _ _ ≫ wl2 _ _ = _
    rw [wl2_comp, S.square, wl2_zero]
    rfl
  | j + 1, (c₁, ν) :: L, μ', h, c, h₁, h₂ => by
    have ih := congrArg (· ▷ S.E c₁ h.2)
      (wcross_sq_self j L ν h.1 c (by simpa using h₁) (by simpa using h₂))
    simp only [comp_whiskerRight, AdditiveWhiskering.zero_whiskerRight] at ih
    exact ih
  | 0, [], _, _, _, h₁, _ => by simp at h₁
  | 0, [_], _, _, _, _, h₂ => by simp at h₂
  | _ + 1, [], _, _, _, h₁, _ => by simp at h₁

/-- The nil-Hecke relation `(x_j ψ_j - ψ_j x_{j+1}) e = e` for equal colours. -/
theorem wslide_left_self : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ')
    (c : I), (L.map Prod.fst)[j]? = some c → (L.map Prod.fst)[j + 1]? = some c →
    ∀ (hL : wswap RD j L = L),
    (S.wcross μ j L μ' h ≫ S.wdot μ j (wswap RD j L) μ' (wValid_wswap j L h) -
      S.wdot μ (j + 1) L μ' h ≫ S.wcross μ j L μ' h) ≫ eqToHom (S.wcell_congr μ hL _ h) = 𝟙 _
  | 0, (c₁, ν₁) :: (c₂, ν₂) :: R, μ', h, c, h₁, h₂, hL => by
    simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at h₁ h₂
    subst h₁ h₂
    obtain ⟨⟨hR, rfl⟩, rfl⟩ := h
    refine (comp_eqToHom_self _ _).trans ?_
    have key := congrArg (wl2 (S.wcell μ R ν₂ hR)) (S.loc c₂ rfl rfl).slide_right
    rw [← wl2_sub, ← wl2_comp, ← wl2_comp, wl2_whiskerLeft, wl2_whiskerRight, wl2_id] at key
    exact key
  | j + 1, (c₁, ν) :: L, μ', h, c, h₁, h₂, hL => by
    have hL' : wswap RD j L = L := by simpa [wswap] using hL
    have ih := congrArg (· ▷ S.E c₁ h.2)
      (wslide_left_self j L ν h.1 c (by simpa using h₁) (by simpa using h₂) hL')
    simp only [comp_whiskerRight, AdditiveWhiskering.sub_whiskerRight, eqToHom_whiskerRight,
      id_whiskerRight] at ih
    exact ih
  | 0, [], _, _, _, h₁, _, _ => by simp at h₁
  | 0, [_], _, _, _, _, h₂, _ => by simp at h₂
  | _ + 1, [], _, _, _, h₁, _, _ => by simp at h₁

/-- The nil-Hecke relation `(ψ_j x_j - x_{j+1} ψ_j) e = e` for equal colours. -/
theorem wslide_right_self : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ')
    (c : I), (L.map Prod.fst)[j]? = some c → (L.map Prod.fst)[j + 1]? = some c →
    ∀ (hL : wswap RD j L = L),
    (S.wdot μ j L μ' h ≫ S.wcross μ j L μ' h -
      S.wcross μ j L μ' h ≫ S.wdot μ (j + 1) (wswap RD j L) μ' (wValid_wswap j L h)) ≫
        eqToHom (S.wcell_congr μ hL _ h) = 𝟙 _
  | 0, (c₁, ν₁) :: (c₂, ν₂) :: R, μ', h, c, h₁, h₂, hL => by
    simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at h₁ h₂
    subst h₁ h₂
    obtain ⟨⟨hR, rfl⟩, rfl⟩ := h
    refine (comp_eqToHom_self _ _).trans ?_
    have key := congrArg (wl2 (S.wcell μ R ν₂ hR)) (S.loc c₂ rfl rfl).slide_left
    rw [← wl2_sub, ← wl2_comp, ← wl2_comp, wl2_whiskerLeft, wl2_whiskerRight, wl2_id] at key
    exact key
  | j + 1, (c₁, ν) :: L, μ', h, c, h₁, h₂, hL => by
    have hL' : wswap RD j L = L := by simpa [wswap] using hL
    have ih := congrArg (· ▷ S.E c₁ h.2)
      (wslide_right_self j L ν h.1 c (by simpa using h₁) (by simpa using h₂) hL')
    simp only [comp_whiskerRight, AdditiveWhiskering.sub_whiskerRight, eqToHom_whiskerRight,
      id_whiskerRight] at ih
    exact ih
  | 0, [], _, _, _, h₁, _, _ => by simp at h₁
  | 0, [_], _, _, _, _, h₂, _ => by simp at h₂
  | _ + 1, [], _, _, _, h₁, _, _ => by simp at h₁

section Mixed

variable {S} {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)
include H

/-- The quadratic relation `ψ_j² = Q_{cd}(x_j, x_{j+1})` for distinct colours `c ≠ d`. -/
theorem wcross_sq_ne : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ') (c d : I),
    (L.map Prod.fst)[j]? = some c → (L.map Prod.fst)[j + 1]? = some d → c ≠ d →
    S.wcross μ j L μ' h ≫ S.wcross μ j (wswap RD j L) μ' (wValid_wswap j L h) ≫
      eqToHom (S.wcell_congr μ (wswap_wswap j L h) _ h) =
    ncEval (A := End (S.wcell μ L μ' h)) ![S.wdot μ j L μ' h, S.wdot μ (j + 1) L μ' h] (Q c d)
  | 0, (c₁, ν₁) :: (c₂, ν₂) :: R, μ', h, c, d, h₁, h₂, hcd => by
    simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at h₁ h₂
    subst c d
    obtain ⟨⟨hR, rfl⟩, rfl⟩ := h
    rw [← Category.assoc]
    refine (comp_eqToHom_self _ _).trans ?_
    have key := congrArg (wl2 (S.wcell μ R ν₂ hR))
      (H.square c₁ c₂ hcd (a := ν₂) rfl rfl rfl (add_right_comm _ _ _))
    rw [wl2_ncEval₂, wl2_whiskerLeft, wl2_whiskerRight] at key
    exact (wl2_comp _ _ _).trans key
  | j + 1, (c₁, ν) :: L, μ', h, c, d, h₁, h₂, hcd => by
    have ih := congrArg (· ▷ S.E c₁ h.2)
      (wcross_sq_ne j L ν h.1 c d (by simpa using h₁) (by simpa using h₂) hcd)
    simp only [comp_whiskerRight, eqToHom_whiskerRight, ncEval_whiskerRight₂] at ih
    exact ih
  | 0, [], _, _, _, _, h₁, _, _ => by simp at h₁
  | 0, [_], _, _, _, _, _, h₂, _ => by simp at h₂
  | _ + 1, [], _, _, _, _, h₁, _, _ => by simp at h₁

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- The relation `x_j ψ_j = ψ_j x_{j+1}` for distinct colours (KL I (2.5)). -/
theorem wslide_left_ne : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ') (c d : I),
    (L.map Prod.fst)[j]? = some c → (L.map Prod.fst)[j + 1]? = some d → c ≠ d →
    S.wcross μ j L μ' h ≫ S.wdot μ j (wswap RD j L) μ' (wValid_wswap j L h) =
      S.wdot μ (j + 1) L μ' h ≫ S.wcross μ j L μ' h
  | 0, (c₁, ν₁) :: (c₂, ν₂) :: R, μ', h, c, d, h₁, h₂, hcd => by
    simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at h₁ h₂
    subst c d
    obtain ⟨⟨hR, rfl⟩, rfl⟩ := h
    have key₀ := H.slide_right c₁ c₂ hcd (a := ν₂) rfl rfl rfl (add_right_comm _ _ _)
    have key := congrArg (wl2 (S.wcell μ R ν₂ hR)) key₀
    rw [← wl2_comp, ← wl2_comp, wl2_whiskerLeft, wl2_whiskerRight] at key
    exact key.symm
  | j + 1, (c₁, ν) :: L, μ', h, c, d, h₁, h₂, hcd => by
    have ih := congrArg (· ▷ S.E c₁ h.2)
      (wslide_left_ne j L ν h.1 c d (by simpa using h₁) (by simpa using h₂) hcd)
    simp only [comp_whiskerRight] at ih
    exact ih
  | 0, [], _, _, _, _, h₁, _, _ => by simp at h₁
  | 0, [_], _, _, _, _, _, h₂, _ => by simp at h₂
  | _ + 1, [], _, _, _, _, h₁, _, _ => by simp at h₁

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- The relation `ψ_j x_j = x_{j+1} ψ_j` for distinct colours (KL I (2.6)). -/
theorem wslide_right_ne : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ') (c d : I),
    (L.map Prod.fst)[j]? = some c → (L.map Prod.fst)[j + 1]? = some d → c ≠ d →
    S.wdot μ j L μ' h ≫ S.wcross μ j L μ' h =
      S.wcross μ j L μ' h ≫ S.wdot μ (j + 1) (wswap RD j L) μ' (wValid_wswap j L h)
  | 0, (c₁, ν₁) :: (c₂, ν₂) :: R, μ', h, c, d, h₁, h₂, hcd => by
    simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at h₁ h₂
    subst c d
    obtain ⟨⟨hR, rfl⟩, rfl⟩ := h
    have key₀ := H.slide_left c₁ c₂ hcd (a := ν₂) rfl rfl rfl (add_right_comm _ _ _)
    have key := congrArg (wl2 (S.wcell μ R ν₂ hR)) key₀
    rw [← wl2_comp, ← wl2_comp, wl2_whiskerLeft, wl2_whiskerRight] at key
    exact key
  | j + 1, (c₁, ν) :: L, μ', h, c, d, h₁, h₂, hcd => by
    have ih := congrArg (· ▷ S.E c₁ h.2)
      (wslide_right_ne j L ν h.1 c d (by simpa using h₁) (by simpa using h₂) hcd)
    simp only [comp_whiskerRight] at ih
    exact ih
  | 0, [], _, _, _, _, h₁, _, _ => by simp at h₁
  | 0, [_], _, _, _, _, _, h₂, _ => by simp at h₂
  | _ + 1, [], _, _, _, _, h₁, _, _ => by simp at h₁

omit [AdditiveWhiskering B] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- The braid relation `ψ_j ψ_{j+1} ψ_j = ψ_{j+1} ψ_j ψ_{j+1}` on a word with colours
`c, d, e` at positions `j, j + 1, j + 2`, unless `c = e ≠ d` (KL I (2.7)). The intermediate
words are arbitrary weighted words with the expected letters and weights. -/
theorem wbraid : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ') (c d e : I),
    (L.map Prod.fst)[j]? = some c → (L.map Prod.fst)[j + 1]? = some d →
    (L.map Prod.fst)[j + 2]? = some e → ¬(c = e ∧ c ≠ d) →
    ∀ (M₁ M₂ M₃ N₁ N₂ : List (I × X)) (h₁ : wValid RD μ M₁ μ') (h₂ : wValid RD μ M₂ μ')
      (h₃ : wValid RD μ M₃ μ') (h₄ : wValid RD μ N₁ μ') (h₅ : wValid RD μ N₂ μ')
      (e₁ : wswap RD j L = M₁) (e₂ : wswap RD (j + 1) M₁ = M₂) (e₃ : wswap RD j M₂ = M₃)
      (e₄ : wswap RD (j + 1) L = N₁) (e₅ : wswap RD j N₁ = N₂) (e₆ : wswap RD (j + 1) N₂ = M₃),
    S.wcrossTo μ j L M₁ μ' e₁ h h₁ ≫ S.wcrossTo μ (j + 1) M₁ M₂ μ' e₂ h₁ h₂ ≫
        S.wcrossTo μ j M₂ M₃ μ' e₃ h₂ h₃ =
      S.wcrossTo μ (j + 1) L N₁ μ' e₄ h h₄ ≫ S.wcrossTo μ j N₁ N₂ μ' e₅ h₄ h₅ ≫
        S.wcrossTo μ (j + 1) N₂ M₃ μ' e₆ h₅ h₃
  | 0, (c₁, ν₁) :: (c₂, ν₂) :: (c₃, ν₃) :: R, μ', h, c, d, e, hc, hd, he, hne => by
    intro M₁ M₂ M₃ N₁ N₂ h₁ h₂ h₃ h₄ h₅ e₁ e₂ e₃ e₄ e₅ e₆
    simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hc hd he
    subst c d e
    obtain ⟨⟨⟨hR, rfl⟩, rfl⟩, rfl⟩ := h
    obtain rfl : M₁ = (c₂, ν₃ + RD.iX c₃ + RD.iX c₁) :: (c₁, ν₃ + RD.iX c₃) :: (c₃, ν₃) :: R :=
      e₁.symm
    obtain rfl : M₂ = (c₂, ν₃ + RD.iX c₃ + RD.iX c₁) :: (c₃, ν₃ + RD.iX c₁) :: (c₁, ν₃) :: R :=
      e₂.symm
    obtain rfl : M₃ = (c₃, ν₃ + RD.iX c₁ + RD.iX c₂) :: (c₂, ν₃ + RD.iX c₁) :: (c₁, ν₃) :: R :=
      e₃.symm
    obtain rfl : N₁ = (c₁, ν₃ + RD.iX c₃ + RD.iX c₂) :: (c₃, ν₃ + RD.iX c₂) :: (c₂, ν₃) :: R :=
      e₄.symm
    obtain rfl : N₂ = (c₃, ν₃ + RD.iX c₁ + RD.iX c₂) :: (c₁, ν₃ + RD.iX c₂) :: (c₂, ν₃) :: R := by
      rw [← e₅]; simp only [wswap]; rw [add_right_comm]
    rw [S.wcrossTo_zero μ c₁ c₃ _ _ _ _ _ _ _ _ (add_right_comm _ _ _)]
    simp only [wcrossTo_succ, wcrossTo_zero_rfl]
    by_cases h13 : c₁ = c₃
    · have h12 : c₁ = c₂ := by
        by_contra h12
        exact hne ⟨h13, h12⟩
      subst h13 h12
      have key := congrArg (wl3 (S.wcell μ R ν₃ hR)) (S.braid c₁ (a := ν₃) rfl rfl rfl)
      rw [wl3_braid_left, wl3_braid_right] at key
      exact key
    · have key := congrArg (wl3 (S.wcell μ R ν₃ hR)) (H.braid c₁ c₂ c₃ h13 (l := ν₃)
        (w₁ := ν₃ + RD.iX c₃) (w₂ := ν₃ + RD.iX c₃ + RD.iX c₂) (w₃ := ν₃ + RD.iX c₃ + RD.iX c₁)
        (w₄ := ν₃ + RD.iX c₁) (w₅ := ν₃ + RD.iX c₁ + RD.iX c₂) (w₆ := ν₃ + RD.iX c₂)
        (m := ν₃ + RD.iX c₃ + RD.iX c₂ + RD.iX c₁) rfl rfl rfl rfl (by abel) rfl (by abel) rfl
        (by abel) rfl (by abel) (by abel))
      rw [wl3_braid_left, wl3_braid_right] at key
      exact key
  | j + 1, (c₀, ν) :: L, μ', h, c, d, e, hc, hd, he, hne => by
    intro M₁ M₂ M₃ N₁ N₂ h₁ h₂ h₃ h₄ h₅ e₁ e₂ e₃ e₄ e₅ e₆
    obtain ⟨M₁, rfl, e₁'⟩ := wswap_succ_eq e₁
    obtain ⟨M₂, rfl, e₂'⟩ := wswap_succ_eq e₂
    obtain ⟨M₃, rfl, e₃'⟩ := wswap_succ_eq e₃
    obtain ⟨N₁, rfl, e₄'⟩ := wswap_succ_eq e₄
    obtain ⟨N₂, rfl, e₅'⟩ := wswap_succ_eq e₅
    have e₆' := wswap_succ_cons e₆
    have ih := congrArg (· ▷ S.E c₀ h.2) (wbraid j L ν h.1 c d e (by simpa using hc)
      (by simpa using hd) (by simpa using he) hne M₁ M₂ M₃ N₁ N₂ h₁.1 h₂.1 h₃.1 h₄.1 h₅.1
      e₁' e₂' e₃' e₄' e₅' e₆')
    simp only [comp_whiskerRight] at ih
    simp only [wcrossTo_succ]
    exact ih
  | 0, [], _, _, _, _, _, hc, _, _, _ => by simp at hc
  | 0, [_], _, _, _, _, _, _, hd, _, _ => by simp at hd
  | 0, [_, _], _, _, _, _, _, _, _, he, _ => by simp at he
  | _ + 1, [], _, _, _, _, _, hc, _, _, _ => by simp at hc

/-- The braid relation with correction term,
`ψ_j ψ_{j+1} ψ_j - ψ_{j+1} ψ_j ψ_{j+1} = Q̄_{cd}(x_j, x_{j+1}, x_{j+2})`, on a word with colours
`c, d, c` at positions `j, j + 1, j + 2` and `c ≠ d` (KL I (2.8); Brundan (1.4)). -/
theorem wbraidQ : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ') (c d : I),
    (L.map Prod.fst)[j]? = some c → (L.map Prod.fst)[j + 1]? = some d →
    (L.map Prod.fst)[j + 2]? = some c → c ≠ d →
    ∀ (M₁ M₂ N₁ N₂ : List (I × X)) (h₁ : wValid RD μ M₁ μ') (h₂ : wValid RD μ M₂ μ')
      (h₄ : wValid RD μ N₁ μ') (h₅ : wValid RD μ N₂ μ')
      (e₁ : wswap RD j L = M₁) (e₂ : wswap RD (j + 1) M₁ = M₂) (e₃ : wswap RD j M₂ = L)
      (e₄ : wswap RD (j + 1) L = N₁) (e₅ : wswap RD j N₁ = N₂) (e₆ : wswap RD (j + 1) N₂ = L),
    S.wcrossTo μ j L M₁ μ' e₁ h h₁ ≫ S.wcrossTo μ (j + 1) M₁ M₂ μ' e₂ h₁ h₂ ≫
        S.wcrossTo μ j M₂ L μ' e₃ h₂ h -
      S.wcrossTo μ (j + 1) L N₁ μ' e₄ h h₄ ≫ S.wcrossTo μ j N₁ N₂ μ' e₅ h₄ h₅ ≫
        S.wcrossTo μ (j + 1) N₂ L μ' e₆ h₅ h =
    ncEval (A := End (S.wcell μ L μ' h))
      ![S.wdot μ j L μ' h, S.wdot μ (j + 1) L μ' h, S.wdot μ (j + 2) L μ' h] (qbar (Q c d))
  | 0, (c₁, ν₁) :: (c₂, ν₂) :: (c₃, ν₃) :: R, μ', h, c, d, hc, hd, he, hcd => by
    intro M₁ M₂ N₁ N₂ h₁ h₂ h₄ h₅ e₁ e₂ e₃ e₄ e₅ e₆
    simp only [List.map_cons, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hc hd he
    subst c d
    subst c₃
    obtain ⟨⟨⟨hR, rfl⟩, rfl⟩, rfl⟩ := h
    obtain rfl : M₁ = (c₂, ν₃ + RD.iX c₁ + RD.iX c₁) :: (c₁, ν₃ + RD.iX c₁) :: (c₁, ν₃) :: R :=
      e₁.symm
    obtain rfl : M₂ = (c₂, ν₃ + RD.iX c₁ + RD.iX c₁) :: (c₁, ν₃ + RD.iX c₁) :: (c₁, ν₃) :: R :=
      e₂.symm
    obtain rfl : N₁ = (c₁, ν₃ + RD.iX c₁ + RD.iX c₂) :: (c₁, ν₃ + RD.iX c₂) :: (c₂, ν₃) :: R :=
      e₄.symm
    obtain rfl : N₂ = (c₁, ν₃ + RD.iX c₁ + RD.iX c₂) :: (c₁, ν₃ + RD.iX c₂) :: (c₂, ν₃) :: R := by
      rw [← e₅]; simp only [wswap]; rw [add_right_comm]
    rw [S.wcrossTo_zero μ c₁ c₁ _ _ _ _ _ _ _ _ (add_right_comm _ _ _)]
    simp only [wcrossTo_succ, wcrossTo_zero_rfl]
    have key := congrArg (wl3 (S.wcell μ R ν₃ hR)) (H.braidQ c₁ c₂ hcd (a := ν₃)
      (b := ν₃ + RD.iX c₁) (c := ν₃ + RD.iX c₁ + RD.iX c₂) (d := ν₃ + RD.iX c₁ + RD.iX c₁)
      (e := ν₃ + RD.iX c₂) (f := ν₃ + RD.iX c₁ + RD.iX c₂ + RD.iX c₁)
      rfl rfl rfl rfl (by abel) rfl (by abel))
    rw [← wl3_sub, wl3_braid_left, wl3_braid_right, wl3_ncEval₃, wl3_dot₀, wl3_dot₁,
      wl3_dot₂] at key
    exact key
  | j + 1, (c₀, ν) :: L, μ', h, c, d, hc, hd, he, hcd => by
    intro M₁ M₂ N₁ N₂ h₁ h₂ h₄ h₅ e₁ e₂ e₃ e₄ e₅ e₆
    obtain ⟨M₁, rfl, e₁'⟩ := wswap_succ_eq e₁
    obtain ⟨M₂, rfl, e₂'⟩ := wswap_succ_eq e₂
    have e₃' := wswap_succ_cons e₃
    obtain ⟨N₁, rfl, e₄'⟩ := wswap_succ_eq e₄
    obtain ⟨N₂, rfl, e₅'⟩ := wswap_succ_eq e₅
    have e₆' := wswap_succ_cons e₆
    have ih := congrArg (· ▷ S.E c₀ h.2) (wbraidQ j L ν h.1 c d (by simpa using hc)
      (by simpa using hd) (by simpa using he) hcd M₁ M₂ N₁ N₂ h₁.1 h₂.1 h₄.1 h₅.1
      e₁' e₂' e₃' e₄' e₅' e₆')
    simp only [comp_whiskerRight, AdditiveWhiskering.sub_whiskerRight,
      ncEval_whiskerRight₃] at ih
    simp only [wcrossTo_succ]
    exact ih
  | 0, [], _, _, _, _, hc, _, _, _ => by simp at hc
  | 0, [_], _, _, _, _, _, hd, _, _ => by simp at hd
  | 0, [_, _], _, _, _, _, _, _, he, _ => by simp at he
  | _ + 1, [], _, _, _, _, hc, _, _, _ => by simp at hc

end Mixed

end RouqFamily

end ListRel

/-! ### The algebra of matrices on the words of weight `ν` -/

section Matrix

variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k]
  {I : Type*} [DecidableEq I] {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : WeightDatum C X Y}

namespace RouqData

open Diagram MatEnd

variable (S : RouqData (B := B) RD) (μ : X) {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- The word `E_{t_0} ∘ ⋯ ∘ E_{t_{m-1}}` from `μ` to `μ + Σ ν` of a sequence `t`. -/
abbrev wordCell (t : Seq ν) : S.obj μ ⟶ S.obj (wtop RD μ ν) :=
  S.wcell μ (wordL RD μ t) (wtop RD μ ν) (wValid_wordL μ t)

variable (ν) in
/-- The algebra of `Seq ν × Seq ν` matrices of 2-morphisms between the words of weight `ν` at
`μ`: the endomorphism algebra of their formal direct sum. -/
abbrev WordEnd : Type _ := MatEnd (fun t : Seq ν => S.wordCell μ t)

/-- The dot on the `a`-th strand of the word of `t`. -/
def wordDot (t : Seq ν) (a : Fin m) : End (S.wordCell μ t) :=
  S.wdot μ a (wordL RD μ t) (wtop RD μ ν) (wValid_wordL μ t)

/-- The crossing of the strands `j` and `j + 1` of the word of `t` (zero if `j + 1 ≥ m`). -/
def wordCross (t : Seq ν) (j : ℕ) : S.wordCell μ t ⟶ S.wordCell μ (sadj m j • t) :=
  if hj : j + 1 < m then
    S.wcrossTo μ j _ _ _ (wswap_wordL μ t hj) (wValid_wordL μ t) (wValid_wordL μ _)
  else 0

omit [DecidableEq I] in
theorem wordCross_def (t : Seq ν) {j : ℕ} (hj : j + 1 < m) :
    S.wordCross μ t j =
      S.wcrossTo μ j _ _ _ (wswap_wordL μ t hj) (wValid_wordL μ t) (wValid_wordL μ _) :=
  dite_eq_left hj

omit [DecidableEq I] in
theorem wordCross_of_le (t : Seq ν) {j : ℕ} (hj : m ≤ j + 1) : S.wordCross μ t j = 0 :=
  dite_eq_right (by omega)

/-- The idempotent of the word of `t`. -/
def wordE (t : Seq ν) : S.WordEnd μ ν := single t t (𝟙 _)

/-- The dot on the `a`-th strand, summed over all sequences. -/
def wordX (a : Fin m) : S.WordEnd μ ν := ∑ t, single t t (S.wordDot μ t a)

/-- The crossing of the strands `j` and `j + 1`, summed over all sequences. -/
def wordΨ (j : ℕ) : S.WordEnd μ ν := ∑ t, single t (sadj m j • t) (S.wordCross μ t j)

variable {S μ}

theorem wordE_eq (t : Seq ν) : S.wordE μ t = single t t (𝟙 _) := rfl

theorem wordE_mul_single_self {t t' : Seq ν} (f : S.wordCell μ t ⟶ S.wordCell μ t') :
    S.wordE μ t' * single t t' f = single t t' f := by
  rw [wordE, single_mul_single, Category.comp_id]

theorem wordE_mul_single_of_ne {t t' t'' : Seq ν} (f : S.wordCell μ t ⟶ S.wordCell μ t')
    (h : t' ≠ t'') : S.wordE μ t'' * single t t' f = 0 :=
  single_mul_single_of_ne _ _ h

theorem wordX_mul_single (a : Fin m) {t t' : Seq ν} (f : S.wordCell μ t ⟶ S.wordCell μ t') :
    S.wordX μ a * single t t' f = single t t' (f ≫ S.wordDot μ t' a) := by
  rw [wordX, Finset.sum_mul, Finset.sum_eq_single t', single_mul_single]
  · intro l _ hl; exact single_mul_single_of_ne _ _ (Ne.symm hl)
  · simp

theorem wordΨ_mul_single (j : ℕ) {t t' : Seq ν} (f : S.wordCell μ t ⟶ S.wordCell μ t') :
    S.wordΨ μ j * single t t' f = single t (sadj m j • t') (f ≫ S.wordCross μ t' j) := by
  rw [wordΨ, Finset.sum_mul, Finset.sum_eq_single t', single_mul_single]
  · intro l _ hl; exact single_mul_single_of_ne _ _ (Ne.symm hl)
  · simp

theorem wordE_mul_wordE (t t' : Seq ν) :
    S.wordE μ t * S.wordE μ t' = if t = t' then S.wordE μ t else 0 := by
  split_ifs with h
  · subst h; exact wordE_mul_single_self _
  · exact wordE_mul_single_of_ne _ (Ne.symm h)

theorem sum_wordE : ∑ t, S.wordE μ t = (1 : S.WordEnd μ ν) := one_eq_sum_single.symm

theorem ext_wordE {f g : S.WordEnd μ ν} (h : ∀ t, f * S.wordE μ t = g * S.wordE μ t) :
    f = g := by
  rw [← mul_one f, ← mul_one g, ← sum_wordE, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => h t

theorem wordX_mul_wordE (a : Fin m) (t : Seq ν) :
    S.wordX μ a * S.wordE μ t = S.wordE μ t * S.wordX μ a := by
  rw [wordE_eq, wordX_mul_single, Category.id_comp, wordX, Finset.mul_sum,
    Finset.sum_eq_single t, ← wordE_eq, wordE_mul_single_self]
  · intro l _ hl; exact wordE_mul_single_of_ne _ hl
  · simp

theorem wordΨ_mul_wordE (j : ℕ) (t : Seq ν) :
    S.wordΨ μ j * S.wordE μ t = S.wordE μ (sadj m j • t) * S.wordΨ μ j := by
  rw [wordE_eq t, wordΨ_mul_single, Category.id_comp, wordΨ, Finset.mul_sum,
    Finset.sum_eq_single t, wordE_mul_single_self]
  · intro l _ hl; exact wordE_mul_single_of_ne _ (fun h => hl (sadj_smul_injective j h))
  · simp

theorem wordΨ_of_le {j : ℕ} (h : m ≤ j + 1) : (S.wordΨ μ j : S.WordEnd μ ν) = 0 := by
  simp [wordΨ, wordCross_of_le _ _ _ h]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
theorem single_ncEval (t : Seq ν) {n : ℕ} (a : Fin n → Fin m) (p : MvPolynomial (Fin n) k) :
    single t t (ncEval (A := End (S.wordCell μ t)) (fun r => S.wordDot μ t (a r)) p) =
      ncEval (fun r => S.wordX μ (a r)) p * S.wordE μ t := by
  let φ : End (S.wordCell μ t) →ₗ[k] S.WordEnd μ ν :=
    singleₗ (X := fun t : Seq ν => S.wordCell μ t) k t t
  refine ncEval_of_mul φ (fun f g => ?_) (e := S.wordE μ t) rfl _ _ (fun r => ?_)
    (fun r => wordX_mul_wordE _ t) p
  · show single t t (g ≫ f) = single t t f * single t t g
    rw [single_mul_single]
  · show single t t (S.wordDot μ t (a r)) = _
    rw [wordE_eq, wordX_mul_single, Category.id_comp]

/-! #### Isotopy relations -/

theorem wordX_mul_wordX (a b : Fin m) : S.wordX μ a * S.wordX μ b = S.wordX μ b * S.wordX μ a := by
  refine ext_wordE fun t => ?_
  simp only [mul_assoc, wordE_eq, wordX_mul_single, Category.id_comp, wordDot, wdot_comm]

omit [DecidableEq I] in
theorem wordDot_wordCross (t : Seq ν) (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    S.wordDot μ t a ≫ S.wordCross μ t j = S.wordCross μ t j ≫ S.wordDot μ (sadj m j • t) a := by
  by_cases hj : j + 1 < m
  · rw [wordCross_def _ _ _ hj, wcrossTo, wordDot, wordDot, Category.assoc,
      S.eqToHom_wdot μ a (wswap_wordL μ t hj),
      ← Category.assoc, wdot_wcross _ _ _ _ _ _ _ h₁ h₂, Category.assoc]
  · rw [wordCross_of_le _ _ _ (by omega), Limits.comp_zero, Limits.zero_comp]

theorem wordX_mul_wordΨ (a : Fin m) (j : ℕ) (h₁ : a.val ≠ j) (h₂ : a.val ≠ j + 1) :
    S.wordX μ a * S.wordΨ μ j = S.wordΨ μ j * S.wordX μ a := by
  refine ext_wordE fun t => ?_
  simp only [mul_assoc, wordE_eq, wordX_mul_single, wordΨ_mul_single, Category.id_comp,
    wordDot_wordCross t a j h₁ h₂]

variable [AdditiveWhiskering B]

omit [DecidableEq I] in
theorem wordCross_comm (t : Seq ν) {j l : ℕ} (h : j + 1 < l)
    (hs : sadj m j • sadj m l • t = sadj m l • sadj m j • t) :
    S.wordCross μ t j ≫ S.wordCross μ (sadj m j • t) l =
      S.wordCross μ t l ≫ S.wordCross μ (sadj m l • t) j ≫ eqToHom (by rw [hs]) := by
  by_cases hl : l + 1 < m
  · have hj : j + 1 < m := by omega
    rw [wordCross_def _ _ _ hj, wordCross_def _ _ _ hl, wordCross_def _ _ _ hl,
      wordCross_def _ _ _ hj]
    simp only [wcrossTo, Category.assoc]
    rw [S.eqToHom_wcross_assoc μ l (wswap_wordL μ t hj),
      S.eqToHom_wcross_assoc μ j (wswap_wordL μ t hl)]
    rw [← reassoc_of% (S.wcross_comm μ j l _ _ (wValid_wordL μ t) h)]
    simp only [eqToHom_trans]
  · rw [wordCross_of_le _ _ _ (show m ≤ l + 1 by omega),
      wordCross_of_le _ _ _ (show m ≤ l + 1 by omega)]
    simp

theorem wordΨ_mul_wordΨ {j l : ℕ} (h : j + 1 < l) :
    (S.wordΨ μ j * S.wordΨ μ l : S.WordEnd μ ν) = S.wordΨ μ l * S.wordΨ μ j := by
  refine ext_wordE fun t => ?_
  have hs : sadj m j • sadj m l • t = sadj m l • sadj m j • t := by
    rw [← mul_smul, ← mul_smul, sadj_comm m (Or.inl h)]
  simp only [mul_assoc, wordE_eq, wordΨ_mul_single, Category.id_comp]
  rw [wordCross_comm t h hs, ← Category.assoc, single_eqToHom _ hs]

/-! #### The local relations -/

/-! #### The action of `R(ν)` -/

section ActionFree

variable (S μ ν) in
/-- The images of the generators of `R(ν)`. -/
def klrGen : KLR.Gen ν → S.WordEnd μ ν
  | .idem t => S.wordE μ t
  | .dot a => S.wordX μ a
  | .cross j => S.wordΨ μ j

variable (k S μ ν) in
/-- The action of the free algebra on the generators of `R(ν)`. -/
def klrActFree : FreeAlgebra k (KLR.Gen ν) →ₐ[k] S.WordEnd μ ν :=
  FreeAlgebra.lift k (S.klrGen μ ν)

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] [AdditiveWhiskering B] in
@[simp] theorem klrActFree_fe (t : Seq ν) : S.klrActFree k μ ν (fe k ν t) = S.wordE μ t := by
  simp [klrActFree, klrGen]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] [AdditiveWhiskering B] in
@[simp] theorem klrActFree_fx (a : Fin m) : S.klrActFree k μ ν (fx k ν a) = S.wordX μ a := by
  simp [klrActFree, klrGen]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] [AdditiveWhiskering B] in
@[simp] theorem klrActFree_fψ (j : ℕ) : S.klrActFree k μ ν (fψ k ν j) = S.wordΨ μ j := by
  simp [klrActFree, klrGen]

variable (S) in
omit [DecidableEq I] [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
/-- If every dot satisfies `x^M = 0`, so does every dot on a weighted word. -/
theorem wdot_pow_eq_zero {M : ℕ}
    (hM : ∀ (c : I) {x y : X} (h : x + RD.iX c = y), End.of (S.dot c h) ^ M = 0) :
    ∀ (a : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ'), a < L.length →
      End.of (S.wdot μ a L μ' h) ^ M = 0
  | 0, (c, ν) :: L, _, h, _ => by
    change End.of (S.wcell μ L ν h.1 ◁ S.dot c h.2) ^ M = 0
    rw [whiskerLeft_pow, hM]
    exact AdditiveWhiskering.whiskerLeft_zero _ _ _
  | a + 1, (c, ν) :: L, _, h, ha => by
    change End.of (S.wdot μ a L ν h.1 ▷ S.E c h.2) ^ M = 0
    rw [whiskerRight_pow, wdot_pow_eq_zero hM a L ν h.1 (by simpa using ha)]
    exact AdditiveWhiskering.zero_whiskerRight _ _ _
  | _, [], _, _, ha => by simp at ha

omit [AdditiveWhiskering B] in
theorem wordX_pow_mul_wordE (a : Fin m) (t : Seq ν) (n : ℕ) :
    S.wordX μ a ^ n * S.wordE μ t = single t t (S.wordDot μ t a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_mul]; rfl
  | succ n ih => rw [pow_succ', mul_assoc, ih, wordX_mul_single, pow_succ']; rfl

end ActionFree

end RouqData

namespace RouqFamily

open Diagram MatEnd RouqData

variable {S : RouqFamily (B := B) RD} {μ : X} {ν : Multiset I}

local notation "m" => Multiset.card ν

variable [AdditiveWhiskering B]

section Local

variable {Q : I → I → MvPolynomial (Fin 2) k} (H : RouqUpKLR S Q)

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
include H in
/-- KL I (2.4)/(2.5): `(x_j ψ_j - ψ_j x_{j+1}) e(t) = [t_j = t_{j+1}] e(t)`. -/
theorem wordDot_cross_left {j : ℕ} (h : j + 1 < m) (t : Seq ν) :
    ((S.wordX μ ⟨j, by omega⟩ * S.wordΨ μ j - S.wordΨ μ j * S.wordX μ ⟨j + 1, h⟩) *
        S.wordE μ t : S.WordEnd μ ν) =
      if t.1 ⟨j, by omega⟩ = t.1 ⟨j + 1, h⟩ then S.wordE μ t else 0 := by
  simp only [sub_mul, mul_assoc, wordE_eq, wordX_mul_single, wordΨ_mul_single,
    Category.id_comp, ← single_sub]
  rw [wordCross_def _ _ _ h, wcrossTo, wordDot, wordDot, Category.assoc,
    S.eqToHom_wdot μ _ (wswap_wordL μ t h)]
  split_ifs with he
  · have hs := sadj_smul_eq_self t h he
    rw [← single_eqToHom _ hs]
    refine congrArg (single t t) ?_
    have key := S.wslide_left_self μ j (wordL RD μ t) _ (wValid_wordL μ t) (t.1 ⟨j, by omega⟩)
      (wordL_fst μ t j (by omega)) ((wordL_fst μ t (j + 1) h).trans (by rw [he]))
      ((wswap_wordL μ t h).trans (by rw [hs]))
    simp only [Preadditive.sub_comp, Category.assoc, eqToHom_trans] at key ⊢
    exact key
  · rw [reassoc_of% (S.wslide_left_ne μ H j _ _ (wValid_wordL μ t) _ _
      (wordL_fst μ t j (by omega)) (wordL_fst μ t (j + 1) h) he), sub_self, single_zero]

omit [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
  [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] in
include H in
/-- KL I (2.4)/(2.6): `(ψ_j x_j - x_{j+1} ψ_j) e(t) = [t_j = t_{j+1}] e(t)`. -/
theorem wordDot_cross_right {j : ℕ} (h : j + 1 < m) (t : Seq ν) :
    ((S.wordΨ μ j * S.wordX μ ⟨j, by omega⟩ - S.wordX μ ⟨j + 1, h⟩ * S.wordΨ μ j) *
        S.wordE μ t : S.WordEnd μ ν) =
      if t.1 ⟨j, by omega⟩ = t.1 ⟨j + 1, h⟩ then S.wordE μ t else 0 := by
  simp only [sub_mul, mul_assoc, wordE_eq, wordX_mul_single, wordΨ_mul_single,
    Category.id_comp, ← single_sub]
  rw [wordCross_def _ _ _ h, wcrossTo, wordDot, wordDot, Category.assoc,
    S.eqToHom_wdot μ _ (wswap_wordL μ t h)]
  split_ifs with he
  · have hs := sadj_smul_eq_self t h he
    rw [← single_eqToHom _ hs]
    refine congrArg (single t t) ?_
    have key := S.wslide_right_self μ j (wordL RD μ t) _ (wValid_wordL μ t) (t.1 ⟨j, by omega⟩)
      (wordL_fst μ t j (by omega)) ((wordL_fst μ t (j + 1) h).trans (by rw [he]))
      ((wswap_wordL μ t h).trans (by rw [hs]))
    simp only [Preadditive.sub_comp, Category.assoc, eqToHom_trans] at key ⊢
    exact key
  · rw [reassoc_of% (S.wslide_right_ne μ H j _ _ (wValid_wordL μ t) _ _
      (wordL_fst μ t j (by omega)) (wordL_fst μ t (j + 1) h) he), sub_self, single_zero]

include H in
/-- KL I (2.3): `ψ_j² e(t) = 0` if `t_j = t_{j+1}`, and `Q_{t_j t_{j+1}}(x_j, x_{j+1}) e(t)`
otherwise. -/
theorem wordCross_sq {j : ℕ} (h : j + 1 < m) (t : Seq ν) :
    (S.wordΨ μ j * S.wordΨ μ j * S.wordE μ t : S.WordEnd μ ν) =
      if t.1 ⟨j, by omega⟩ = t.1 ⟨j + 1, h⟩ then 0 else
        ncEval ![S.wordX μ ⟨j, by omega⟩, S.wordX μ ⟨j + 1, h⟩]
          (Q (t.1 ⟨j, by omega⟩) (t.1 ⟨j + 1, h⟩)) * S.wordE μ t := by
  have hs : sadj m j • sadj m j • t = t := sadj_smul_sadj_smul t j
  simp only [mul_assoc, wordE_eq, wordΨ_mul_single, Category.id_comp]
  rw [← single_eqToHom _ hs, wordCross_def _ _ _ h, wordCross_def _ _ _ h]
  simp only [wcrossTo, Category.assoc]
  rw [S.eqToHom_wcross_assoc μ j (wswap_wordL μ t h)]
  simp only [eqToHom_trans]
  split_ifs with he
  · rw [reassoc_of% (S.wcross_sq_self μ j _ _ (wValid_wordL μ t) _ (wordL_fst μ t j (by omega))
      ((wordL_fst μ t (j + 1) h).trans (by rw [he]))), Limits.zero_comp, single_zero]
  · rw [S.wcross_sq_ne μ H j _ _ (wValid_wordL μ t) _ _ (wordL_fst μ t j (by omega))
      (wordL_fst μ t (j + 1) h) he]
    have e₁ : (![S.wdot μ j (wordL RD μ t) _ (wValid_wordL μ t),
        S.wdot μ (j + 1) (wordL RD μ t) _ (wValid_wordL μ t)] : Fin 2 → End (S.wordCell μ t)) =
        fun r => S.wordDot μ t (![⟨j, by omega⟩, ⟨j + 1, h⟩] r) := by
      funext r; fin_cases r <;> rfl
    have e₂ : (![S.wordX μ ⟨j, by omega⟩, S.wordX μ ⟨j + 1, h⟩] : Fin 2 → S.WordEnd μ ν) =
        fun r => S.wordX μ (![⟨j, by omega⟩, ⟨j + 1, h⟩] r) := by
      funext r; fin_cases r <;> rfl
    rw [e₁, single_ncEval, e₂]
    rfl

include H in
/-- KL I (2.7)/(2.8): the braid relation, with the correction term
`Q̄_{t_j t_{j+1}}(x_j, x_{j+1}, x_{j+2})` when `t_j = t_{j+2} ≠ t_{j+1}`. -/
theorem wordBraid {j : ℕ} (h : j + 2 < m) (t : Seq ν) :
    ((S.wordΨ μ j * S.wordΨ μ (j + 1) * S.wordΨ μ j -
        S.wordΨ μ (j + 1) * S.wordΨ μ j * S.wordΨ μ (j + 1)) * S.wordE μ t : S.WordEnd μ ν) =
      if t.1 ⟨j, by omega⟩ = t.1 ⟨j + 2, h⟩ ∧ t.1 ⟨j, by omega⟩ ≠ t.1 ⟨j + 1, by omega⟩ then
        ncEval ![S.wordX μ ⟨j, by omega⟩, S.wordX μ ⟨j + 1, by omega⟩, S.wordX μ ⟨j + 2, h⟩]
          (qbar (Q (t.1 ⟨j, by omega⟩) (t.1 ⟨j + 1, by omega⟩))) * S.wordE μ t
      else 0 := by
  have h1 : j + 1 < m := by omega
  have h2 : j + 1 + 1 < m := by omega
  have hb := sadj_braid_smul t h
  simp only [sub_mul, mul_assoc, wordE_eq, wordΨ_mul_single, Category.id_comp]
  rw [← single_eqToHom _ hb, ← single_sub]
  simp only [wordCross_def _ _ _ h1, wordCross_def _ _ _ h2, Category.assoc]
  rw [S.wcrossTo_comp_eqToHom μ (j + 1) _ _ _ _ (congrArg (wordL RD μ) hb)]
  split_ifs with he
  · have ht := sadj_braid_smul_eq_self t h he.1
    rw [← single_eqToHom _ ht, Preadditive.sub_comp, Category.assoc, Category.assoc,
      Category.assoc, Category.assoc,
      S.wcrossTo_comp_eqToHom μ j _ _ _ _ (congrArg (wordL RD μ) ht),
      S.wcrossTo_comp_eqToHom μ (j + 1) _ _ _ _ (congrArg (wordL RD μ) ht),
      S.wbraidQ μ H j (wordL RD μ t) _ (wValid_wordL μ t) (t.1 ⟨j, by omega⟩) (t.1 ⟨j + 1, h1⟩)
        (wordL_fst μ t j (by omega)) (wordL_fst μ t (j + 1) h1)
        ((wordL_fst μ t (j + 2) h).trans (by rw [he.1])) he.2]
    have e₁ : (![S.wdot μ j (wordL RD μ t) _ (wValid_wordL μ t),
        S.wdot μ (j + 1) (wordL RD μ t) _ (wValid_wordL μ t),
        S.wdot μ (j + 2) (wordL RD μ t) _ (wValid_wordL μ t)] : Fin 3 → End (S.wordCell μ t)) =
        fun r => S.wordDot μ t (![⟨j, by omega⟩, ⟨j + 1, h1⟩, ⟨j + 2, h⟩] r) := by
      funext r; fin_cases r <;> rfl
    have e₂ : (![S.wordX μ ⟨j, by omega⟩, S.wordX μ ⟨j + 1, h1⟩, S.wordX μ ⟨j + 2, h⟩] :
        Fin 3 → S.WordEnd μ ν) =
        fun r => S.wordX μ (![⟨j, by omega⟩, ⟨j + 1, h1⟩, ⟨j + 2, h⟩] r) := by
      funext r; fin_cases r <;> rfl
    rw [e₁, single_ncEval, e₂]
    rfl
  · rw [S.wbraid μ H j (wordL RD μ t) _ (wValid_wordL μ t) _ _ _ (wordL_fst μ t j (by omega))
      (wordL_fst μ t (j + 1) h1) (wordL_fst μ t (j + 2) h) he, sub_self, single_zero]
    all_goals first
      | exact wValid_wordL μ _
      | exact wswap_wordL μ _ (by omega)
      | exact (wswap_wordL μ _ h2).trans (congrArg (wordL RD μ) hb)

end Local

section Action

variable {Q : I → I → MvPolynomial (Fin 2) k}

theorem klrActFree_rel (H : RouqUpKLR S Q) {a b : FreeAlgebra k (KLR.Gen ν)} (h : Rel k Q ν a b) :
    S.klrActFree k μ ν a = S.klrActFree k μ ν b := by
  cases h with
  | idem_mul i j =>
    simp only [map_mul, klrActFree_fe, wordE_mul_wordE]
    split_ifs <;> simp
  | idem_sum => simp [map_sum, sum_wordE]
  | dot_idem a i => simp [wordX_mul_wordE]
  | cross_idem j i => simp [wordΨ_mul_wordE]
  | cross_zero j h => simp [wordΨ_of_le h]
  | dot_dot a b => simp [wordX_mul_wordX]
  | cross_cross j l h => simp [wordΨ_mul_wordΨ h]
  | dot_cross a j h₁ h₂ => simp [wordX_mul_wordΨ a j h₁ h₂]
  | dot_cross_left j h i =>
    simp only [map_mul, map_sub, klrActFree_fe, klrActFree_fx, klrActFree_fψ,
      wordDot_cross_left H h i]
    split_ifs <;> simp
  | dot_cross_right j h i =>
    simp only [map_mul, map_sub, klrActFree_fe, klrActFree_fx, klrActFree_fψ,
      wordDot_cross_right H h i]
    split_ifs <;> simp
  | cross_sq j h i =>
    simp only [map_mul, klrActFree_fe, klrActFree_fψ, wordCross_sq H h i]
    split_ifs
    · simp
    · rw [map_mul, AlgHom.map_ncEval, klrActFree_fe]
      congr 2
      funext r; fin_cases r <;> simp
  | braid j h i =>
    simp only [map_mul, map_sub, klrActFree_fe, klrActFree_fψ, wordBraid H h i]
    split_ifs
    · rw [map_mul, AlgHom.map_ncEval, klrActFree_fe]
      congr 2
      funext r; fin_cases r <;> simp
    · simp

/-- The action of the KLR algebra `R(ν)` on the words `E_{t_0} ∘ ⋯ ∘ E_{t_{m-1}} 1_μ`,
`t ∈ Seq ν`, of a Rouquier family satisfying Brundan's mixed upward equations
(arXiv:1501.00350v1, Definition 1.1): `e(t)` acts as the identity of the word of `t`, `x_a`
as the dot on its `a`-th strand and `ψ_j` as the crossing of its strands `j` and `j + 1`.
This is the action of `R(ν)` on `E^ν` of R. Rouquier, *2-Kac–Moody algebras*,
arXiv:0812.5023, for the presentation of KL I, arXiv:0803.4121v2, §2.1. -/
def klrAct (H : RouqUpKLR S Q) (μ : X) : KLRAlgebra k Q ν →ₐ[k] S.WordEnd μ ν :=
  RingQuot.liftAlgHom k ⟨S.klrActFree k μ ν, fun _ _ h => klrActFree_rel H h⟩

variable (H : RouqUpKLR S Q)

@[simp] theorem klrAct_mk (a : FreeAlgebra k (KLR.Gen ν)) :
    klrAct H μ (KLRAlgebra.mk k Q ν a) = S.klrActFree k μ ν a :=
  RingQuot.liftAlgHom_mkAlgHom_apply k _ _ a

@[simp] theorem klrAct_e (t : Seq ν) : klrAct H μ (KLRAlgebra.e t) = S.wordE μ t := by
  rw [KLRAlgebra.e, klrAct_mk, klrActFree_fe]

@[simp] theorem klrAct_dot (a : Fin m) : klrAct H μ (KLRAlgebra.x a) = S.wordX μ a := by
  rw [KLRAlgebra.x, klrAct_mk, klrActFree_fx]

@[simp] theorem klrAct_cross (j : ℕ) :
    klrAct H μ (KLRAlgebra.ψ j : KLRAlgebra k Q ν) = S.wordΨ μ j := by
  rw [KLRAlgebra.ψ, klrAct_mk, klrActFree_fψ]

/-- If every dot satisfies `x^M = 0` (for instance in a cyclotomic quotient with all levels at
most `M`), then `x_a^M` acts by zero. -/
theorem klrAct_pol_X_pow {M : ℕ}
    (hM : ∀ (c : I) {x y : X} (h : x + RD.iX c = y), End.of (S.dot c h) ^ M = 0)
    (a : Fin m) : klrAct H μ (KLRAlgebra.pol (MvPolynomial.X a ^ M)) = 0 := by
  rw [map_pow, KLRAlgebra.pol_X, map_pow, klrAct_dot]
  refine ext_wordE fun t => ?_
  rw [wordX_pow_mul_wordE, zero_mul, wordDot,
    S.wdot_pow_eq_zero (μ := μ) hM _ _ _ _ (by simp [length_canon]), single_zero]

end Action

end RouqFamily

end Matrix


end Categorification.TwoRep
