/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqKLRAction

/-!
# Rouquier relations from an action of the KLR algebras

Let `S` be weight-indexed Rouquier data (`RouqData`) whose generators act on words through the
free algebra on the generators of `R(ν)` (`RouqData.klrActFree`). If this action respects the
defining relations of `R(ν)` for a matrix `Q` (`RouqData.RespectsKLR`), every local relation
between the generators of `S` follows, by evaluating the relation of `R(ν)` on a word of length
two or three.

* Single colour (J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1,
  Definition 1.1, (1.2)–(1.4) for `i = j`): `RespectsKLR.square`, `RespectsKLR.braid`,
  `RespectsKLR.slide_left`, `RespectsKLR.slide_right`; the fields `square`, `braid` of
  `RouqFamily` and `slide_left`, `slide_right` of `RouqLoc`.
* Mixed colours (Brundan, Definition 1.1, (1.2)–(1.4) for `i ≠ j`): `RespectsKLR.square_ne`,
  `slide_left_ne`, `slide_right_ne`, `braid_ne`, `braidQ_ne`, assembled as
  `RouqFamily.rouqUpKLR_of_respectsKLR : RouqUpKLR S Q`.
* `RespectsKLR.toRouqFamily`: Rouquier data respecting the KLR relations, with right adjoints
  and the inverses of Rouquier's maps ((1.8), (1.9)), form a `RouqFamily`.

The relations on general words (`RespectsKLR.wsquare_of`, `wslide_left_of`, `wslide_right_of`,
`wbraid_of`, `wbraidQ_of`) are stated for the crossings `wcrossTo` between weighted words.
-/

noncomputable section
namespace Categorification.TwoRep
open CategoryTheory CategoryTheory.Bicategory
open QuantumGroup UDot KLR TypeA
universe w v u u₁

/-- Whiskering by an identity on the left is injective on 2-morphisms between composites of
two 1-morphisms. -/
theorem wl2_one_injective {B : Type u} [Bicategory.{w, v} B] {b c c' d : B} {f : b ⟶ c}
    {g : b ⟶ c'} {f' : c ⟶ d} {g' : c' ⟶ d} {η θ : f ≫ f' ⟶ g ≫ g'}
    (h : wl2 (𝟙 b) η = wl2 (𝟙 b) θ) : η = θ := by
  have := congrArg (fun z => (α_ (𝟙 b) f f').inv ≫ z ≫ (α_ (𝟙 b) g g').hom) h
  simp only [wl2, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc,
    id_whiskerLeft] at this
  simpa using this

variable {k : Type*} [CommRing k] {B : Type u} [Bicategory.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  {I : Type*} [DecidableEq I] {C : CartanDatum I} {X Y : Type u₁} [AddCommGroup X]
  [AddCommGroup Y] {RD : WeightDatum C X Y}

/-- The sequence with the letters of a list. -/
def seqList (l : List I) : Seq (l : Multiset I) :=
  ⟨fun a => l.get (Fin.cast (Multiset.coe_card _) a), by
    rw [Fin.univ_val_map, ← List.ofFn_congr (Multiset.coe_card _).symm, List.ofFn_get]⟩

namespace RouqData
open Diagram MatEnd

omit [DecidableEq I] in
/-- The matrix with a single entry determines the entry. -/
theorem single_inj {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒞 : Type*} [Category 𝒞]
    [Preadditive 𝒞] {Z : ι → 𝒞} {s t : ι} {f g : Z s ⟶ Z t}
    (h : MatEnd.single s t f = MatEnd.single s t g) : f = g := by
  simpa using congrFun (congrFun h s) t

variable (k) in
/-- The action of the free algebra on the generators of `R(ν)` on the words of `S` respects the
defining relations of the KLR algebra `R(ν)` for `Q`, at every bottom weight and every `ν`. -/
def RespectsKLR (S : RouqData (B := B) RD) (Q : I → I → MvPolynomial (Fin 2) k) : Prop :=
  ∀ (μ : X) (ν : Multiset I) {x y : FreeAlgebra k (KLR.Gen ν)}, Rel k Q ν x y →
    S.klrActFree k μ ν x = S.klrActFree k μ ν y

variable {S : RouqData (B := B) RD} {Q : I → I → MvPolynomial (Fin 2) k}

variable [AdditiveWhiskering B] in
/-- Brundan (1.3), single colour: the square of a same-colour crossing is zero. -/
theorem RespectsKLR.square (hS : RespectsKLR k S Q) (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    S.cross i i h₁ h₂ h₁ h₂ ≫ S.cross i i h₁ h₂ h₁ h₂ = 0 := by
  subst h₁
  obtain rfl : c = wtop RD a (([i, i] : List I) : Multiset I) := by
    rw [← h₂, wtop]; simp [add_assoc]
  have key := hS a _ (Rel.cross_sq 0 (by simp) (seqList [i, i]))
  split_ifs at key with hc
  swap; · exact absurd rfl hc
  simp only [map_mul, klrActFree_fe, klrActFree_fψ, map_zero, mul_assoc, wordE_eq,
    wordΨ_mul_single, Category.id_comp] at key
  have key' := congrFun (congrFun key (seqList [i, i])) (sadj (Multiset.card (([i, i] : List I) : Multiset I)) 0 • sadj (Multiset.card (([i, i] : List I) : Multiset I)) 0 • seqList [i, i])
  rw [single_apply_self, wordCross_def _ _ _ (by simp), wordCross_def _ _ _ (by simp)] at key'
  simp only [wcrossTo, Category.assoc] at key'
  rw [S.eqToHom_wcross_assoc a 0 (wswap_wordL a _ (by simp))] at key'
  simp only [eqToHom_trans] at key'
  rw [← Category.assoc] at key'
  change _ = 0 at key'
  rw [comp_eqToHom_iff, Limits.zero_comp] at key'
  have key'' := key'
  dsimp only [wordL] at key''
  change wl2 (𝟙 (S.obj a)) (S.cross i i rfl h₂ rfl h₂) ≫
    wl2 (𝟙 (S.obj a)) (S.cross i i rfl h₂ rfl h₂) = 0 at key''
  rw [wl2_comp, ← wl2_zero] at key''
  exact wl2_one_injective key''

variable [AdditiveWhiskering B] in
/-- Brundan (1.2), single colour: the dot slide with the dot on the right strand. -/
theorem RespectsKLR.slide_left (hS : RespectsKLR k S Q) (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    S.E i h₁ ◁ S.dot i h₂ ≫ S.cross i i h₁ h₂ h₁ h₂ -
      S.cross i i h₁ h₂ h₁ h₂ ≫ S.dot i h₁ ▷ S.E i h₂ = 𝟙 _ := by
  subst h₁
  obtain rfl : c = wtop RD a (([i, i] : List I) : Multiset I) := by
    rw [← h₂, wtop]; simp [add_assoc]
  have hj : 0 + 1 < Multiset.card (([i, i] : List I) : Multiset I) := by simp
  have key := hS a _ (Rel.dot_cross_right 0 hj (seqList [i, i]))
  split_ifs at key with hc
  swap; · exact absurd rfl hc
  have hs := Diagram.sadj_smul_eq_self _ hj hc
  simp only [map_mul, map_sub, klrActFree_fe, klrActFree_fx, klrActFree_fψ, sub_mul, mul_assoc,
    wordE_eq, wordX_mul_single, wordΨ_mul_single, Category.id_comp, ← single_sub] at key
  rw [wordCross_def _ _ _ hj, wcrossTo, wordDot, wordDot, Category.assoc,
    S.eqToHom_wdot a _ (wswap_wordL a _ hj), ← single_eqToHom _ hs] at key
  have key' := congrFun (congrFun key (seqList [i, i])) (seqList [i, i])
  rw [single_apply_self, single_apply_self] at key'
  change ((𝟙 (S.obj a) ≫ S.E i rfl) ◁ S.dot i h₂ ≫ wl2 (𝟙 _) (S.cross i i rfl h₂ rfl h₂) ≫ 𝟙 _ -
    wl2 (𝟙 _) (S.cross i i rfl h₂ rfl h₂) ≫ (𝟙 (S.obj a) ◁ S.dot i rfl) ▷ S.E i h₂ ≫ 𝟙 _) ≫
      𝟙 _ = 𝟙 _ at key'
  simp only [Category.comp_id] at key'
  rw [← wl2_whiskerLeft, ← wl2_whiskerRight, wl2_comp, wl2_comp, wl2_sub, ← wl2_id] at key'
  exact wl2_one_injective key'

/-- Whiskering by an identity on the left is injective on 2-morphisms between composites of
three 1-morphisms. -/
theorem wl3_one_injective {B : Type u} [Bicategory.{w, v} B] {b c c' d d' e : B} {f : b ⟶ c}
    {f' : b ⟶ c'} {g : c ⟶ d} {g' : c' ⟶ d'} {h : d ⟶ e} {h' : d' ⟶ e}
    {η θ : f ≫ (g ≫ h) ⟶ f' ≫ (g' ≫ h')} (H : wl3 (𝟙 b) η = wl3 (𝟙 b) θ) : η = θ := by
  have := congrArg (fun z => (α_ (𝟙 b) f (g ≫ h)).inv ≫ (α_ (𝟙 b ≫ f) g h).inv ≫ z ≫
    (α_ (𝟙 b ≫ f') g' h').hom ≫ (α_ (𝟙 b) f' (g' ≫ h')).hom) H
  simp only [wl3, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc,
    id_whiskerLeft] at this
  simpa using this

/-- Brundan (1.4), single colour: the braid relation. -/
theorem RespectsKLR.braid (hS : RespectsKLR k S Q) (i : I) {a b c d : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) (h₃ : c + RD.iX i = d) :
    S.E i h₁ ◁ S.cross i i h₂ h₃ h₂ h₃ ≫
      ((α_ (S.E i h₁) (S.E i h₂) (S.E i h₃)).inv ≫ S.cross i i h₁ h₂ h₁ h₂ ▷ S.E i h₃ ≫
        (α_ (S.E i h₁) (S.E i h₂) (S.E i h₃)).hom) ≫ S.E i h₁ ◁ S.cross i i h₂ h₃ h₂ h₃ =
    ((α_ (S.E i h₁) (S.E i h₂) (S.E i h₃)).inv ≫ S.cross i i h₁ h₂ h₁ h₂ ▷ S.E i h₃ ≫
      (α_ (S.E i h₁) (S.E i h₂) (S.E i h₃)).hom) ≫ S.E i h₁ ◁ S.cross i i h₂ h₃ h₂ h₃ ≫
    ((α_ (S.E i h₁) (S.E i h₂) (S.E i h₃)).inv ≫ S.cross i i h₁ h₂ h₁ h₂ ▷ S.E i h₃ ≫
      (α_ (S.E i h₁) (S.E i h₂) (S.E i h₃)).hom) := by
  subst h₁ h₂
  obtain rfl : d = wtop RD a (([i, i, i] : List I) : Multiset I) := by
    rw [← h₃, wtop]; simp [add_assoc]
  have hj : 0 + 2 < Multiset.card (([i, i, i] : List I) : Multiset I) := by simp
  have key := hS a _ (Rel.braid 0 hj (seqList [i, i, i]))
  split_ifs at key with hc
  · exact absurd rfl hc.2
  have hb := Diagram.sadj_braid_smul (seqList [i, i, i]) hj
  simp only [map_mul, map_sub, map_zero, klrActFree_fe, klrActFree_fψ, sub_mul, mul_assoc,
    wordE_eq, wordΨ_mul_single, Category.id_comp] at key
  rw [← single_eqToHom _ hb, ← single_sub] at key
  rw [← single_zero] at key
  have key' := sub_eq_zero.1 (single_inj key)
  change ((wl2 (𝟙 (S.obj a) ≫ S.E i rfl) (S.cross i i rfl h₃ rfl h₃) ≫ 𝟙 _) ≫
      (wl2 (𝟙 (S.obj a)) (S.cross i i rfl rfl rfl rfl) ▷ S.E i h₃ ≫ 𝟙 _)) ≫
      (wl2 (𝟙 (S.obj a) ≫ S.E i rfl) (S.cross i i rfl h₃ rfl h₃) ≫ 𝟙 _) =
    (((wl2 (𝟙 (S.obj a)) (S.cross i i rfl rfl rfl rfl) ▷ S.E i h₃ ≫ 𝟙 _) ≫
      (wl2 (𝟙 (S.obj a) ≫ S.E i rfl) (S.cross i i rfl h₃ rfl h₃) ≫ 𝟙 _)) ≫
      (wl2 (𝟙 (S.obj a)) (S.cross i i rfl rfl rfl rfl) ▷ S.E i h₃ ≫ 𝟙 _)) ≫ 𝟙 _ at key'
  simp only [Category.comp_id, Category.assoc] at key'
  rw [← wl3_braid_left, ← wl3_braid_right] at key'
  exact wl3_one_injective key'

local notation "m" => Multiset.card

/-- The braid relation along a word, when the KLR correction term vanishes. -/
theorem RespectsKLR.wbraid_of (hS : RespectsKLR k S Q) (μ : X) {ν : Multiset I} (t : Seq ν)
    {j : ℕ} (hj : j + 2 < m ν)
    (hne : ¬(t.1 ⟨j, by omega⟩ = t.1 ⟨j + 2, hj⟩ ∧ t.1 ⟨j, by omega⟩ ≠ t.1 ⟨j + 1, by omega⟩))
    (L : List (I × X)) (hL : wordL RD μ t = L) (h : wValid RD μ L (wtop RD μ ν))
    (M₁ M₂ M₃ N₁ N₂ : List (I × X)) (h₁ : wValid RD μ M₁ (wtop RD μ ν))
    (h₂ : wValid RD μ M₂ (wtop RD μ ν)) (h₃ : wValid RD μ M₃ (wtop RD μ ν))
    (h₄ : wValid RD μ N₁ (wtop RD μ ν)) (h₅ : wValid RD μ N₂ (wtop RD μ ν))
    (e₁ : wswap RD j L = M₁) (e₂ : wswap RD (j + 1) M₁ = M₂) (e₃ : wswap RD j M₂ = M₃)
    (e₄ : wswap RD (j + 1) L = N₁) (e₅ : wswap RD j N₁ = N₂) (e₆ : wswap RD (j + 1) N₂ = M₃) :
    S.wcrossTo μ j L M₁ _ e₁ h h₁ ≫ S.wcrossTo μ (j + 1) M₁ M₂ _ e₂ h₁ h₂ ≫
        S.wcrossTo μ j M₂ M₃ _ e₃ h₂ h₃ =
      S.wcrossTo μ (j + 1) L N₁ _ e₄ h h₄ ≫ S.wcrossTo μ j N₁ N₂ _ e₅ h₄ h₅ ≫
        S.wcrossTo μ (j + 1) N₂ M₃ _ e₆ h₅ h₃ := by
  subst hL
  have h1 : j + 1 < m ν := by omega
  have h2 : j + 1 + 1 < m ν := by omega
  have key := hS μ ν (Rel.braid j hj t)
  split_ifs at key with hc
  · exact absurd hc hne
  have hb := Diagram.sadj_braid_smul t hj
  simp only [map_mul, map_sub, map_zero, klrActFree_fe, klrActFree_fψ, sub_mul, mul_assoc,
    wordE_eq, wordΨ_mul_single, Category.id_comp] at key
  rw [← single_eqToHom _ hb, ← single_sub, ← single_zero] at key
  have key' := sub_eq_zero.1 (single_inj key)
  simp only [wordCross_def _ _ _ h1, wordCross_def _ _ _ h2, Category.assoc] at key'
  rw [S.wcrossTo_comp_eqToHom μ (j + 1) _ _ _ _ (congrArg (wordL RD μ) hb)] at key'
  obtain rfl : M₁ = wordL RD μ (sadj (m ν) j • t) := e₁.symm.trans (wswap_wordL μ t h1)
  obtain rfl : M₂ = wordL RD μ (sadj (m ν) (j + 1) • sadj (m ν) j • t) :=
    e₂.symm.trans (wswap_wordL μ _ h2)
  obtain rfl : M₃ = wordL RD μ (sadj (m ν) j • sadj (m ν) (j + 1) • sadj (m ν) j • t) :=
    e₃.symm.trans (wswap_wordL μ _ h1)
  obtain rfl : N₁ = wordL RD μ (sadj (m ν) (j + 1) • t) := e₄.symm.trans (wswap_wordL μ t h2)
  obtain rfl : N₂ = wordL RD μ (sadj (m ν) j • sadj (m ν) (j + 1) • t) :=
    e₅.symm.trans (wswap_wordL μ _ h1)
  exact key'

/-- The braid relation along a word with repeated outer label, with its correction term. -/
theorem RespectsKLR.wbraidQ_of (hS : RespectsKLR k S Q) (μ : X) {ν : Multiset I} (t : Seq ν)
    {j : ℕ} (hj : j + 2 < m ν) (he : t.1 ⟨j, by omega⟩ = t.1 ⟨j + 2, hj⟩)
    (hne : t.1 ⟨j, by omega⟩ ≠ t.1 ⟨j + 1, by omega⟩)
    (L : List (I × X)) (hL : wordL RD μ t = L) (h : wValid RD μ L (wtop RD μ ν))
    (M₁ M₂ N₁ N₂ : List (I × X)) (h₁ : wValid RD μ M₁ (wtop RD μ ν))
    (h₂ : wValid RD μ M₂ (wtop RD μ ν))
    (h₄ : wValid RD μ N₁ (wtop RD μ ν)) (h₅ : wValid RD μ N₂ (wtop RD μ ν))
    (e₁ : wswap RD j L = M₁) (e₂ : wswap RD (j + 1) M₁ = M₂) (e₃ : wswap RD j M₂ = L)
    (e₄ : wswap RD (j + 1) L = N₁) (e₅ : wswap RD j N₁ = N₂) (e₆ : wswap RD (j + 1) N₂ = L) :
    S.wcrossTo μ j L M₁ _ e₁ h h₁ ≫ S.wcrossTo μ (j + 1) M₁ M₂ _ e₂ h₁ h₂ ≫
        S.wcrossTo μ j M₂ L _ e₃ h₂ h -
      S.wcrossTo μ (j + 1) L N₁ _ e₄ h h₄ ≫ S.wcrossTo μ j N₁ N₂ _ e₅ h₄ h₅ ≫
        S.wcrossTo μ (j + 1) N₂ L _ e₆ h₅ h =
    KLR.ncEval (A := End (S.wcell μ L _ h))
      ![S.wdot μ j L _ h, S.wdot μ (j + 1) L _ h, S.wdot μ (j + 2) L _ h]
      (qbar (Q (t.1 ⟨j, by omega⟩) (t.1 ⟨j + 1, by omega⟩))) := by
  subst hL
  have h1 : j + 1 < m ν := by omega
  have h2 : j + 1 + 1 < m ν := by omega
  have key := hS μ ν (Rel.braid j hj t)
  split_ifs at key with hc
  swap; · exact absurd ⟨he, hne⟩ hc
  have hb := Diagram.sadj_braid_smul t hj
  have ht := Diagram.sadj_braid_smul_eq_self t hj he
  rw [map_mul (S.klrActFree k μ ν) (KLR.ncEval _ _), AlgHom.map_ncEval] at key
  have e₂' : (fun r => S.klrActFree k μ ν
      (![fx k ν ⟨j, by omega⟩, fx k ν ⟨j + 1, h1⟩, fx k ν ⟨j + 2, hj⟩] r)) =
      fun r => S.wordX μ (![⟨j, by omega⟩, ⟨j + 1, h1⟩, ⟨j + 2, hj⟩] r) := by
    funext r; fin_cases r <;> simp
  rw [e₂', klrActFree_fe, ← single_ncEval] at key
  simp only [map_mul, map_sub, klrActFree_fe, klrActFree_fψ, sub_mul, mul_assoc,
    wordE_eq, wordΨ_mul_single, Category.id_comp] at key
  rw [← single_eqToHom _ hb, ← single_sub, ← single_eqToHom _ ht] at key
  have key' := single_inj key
  simp only [wordCross_def _ _ _ h1, wordCross_def _ _ _ h2, Category.assoc,
    Preadditive.sub_comp] at key'
  simp only [eqToHom_trans] at key'
  rw [S.wcrossTo_comp_eqToHom μ j _ _ _ _ (congrArg (wordL RD μ) ht),
    S.wcrossTo_comp_eqToHom μ (j + 1) _ _ _ _ (congrArg (wordL RD μ) (hb.trans ht))] at key'
  obtain rfl : M₁ = wordL RD μ (sadj (m ν) j • t) := e₁.symm.trans (wswap_wordL μ t h1)
  obtain rfl : M₂ = wordL RD μ (sadj (m ν) (j + 1) • sadj (m ν) j • t) :=
    e₂.symm.trans (wswap_wordL μ _ h2)
  obtain rfl : N₁ = wordL RD μ (sadj (m ν) (j + 1) • t) := e₄.symm.trans (wswap_wordL μ t h2)
  obtain rfl : N₂ = wordL RD μ (sadj (m ν) j • sadj (m ν) (j + 1) • t) :=
    e₅.symm.trans (wswap_wordL μ _ h1)
  have e₁' : (![S.wdot μ j (wordL RD μ t) _ h, S.wdot μ (j + 1) (wordL RD μ t) _ h,
      S.wdot μ (j + 2) (wordL RD μ t) _ h] : Fin 3 → End (S.wordCell μ t)) =
      fun r => S.wordDot μ t (![⟨j, by omega⟩, ⟨j + 1, h1⟩, ⟨j + 2, hj⟩] r) := by
    funext r; fin_cases r <;> rfl
  rw [e₁']
  exact key'

variable [AdditiveWhiskering B] in
/-- Brundan (1.2), single colour: the dot slide with the dot on the left strand. -/
theorem RespectsKLR.slide_right (hS : RespectsKLR k S Q) (i : I) {a b c : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c) :
    S.cross i i h₁ h₂ h₁ h₂ ≫ S.E i h₁ ◁ S.dot i h₂ -
      S.dot i h₁ ▷ S.E i h₂ ≫ S.cross i i h₁ h₂ h₁ h₂ = 𝟙 _ := by
  subst h₁
  obtain rfl : c = wtop RD a (([i, i] : List I) : Multiset I) := by
    rw [← h₂, wtop]; simp [add_assoc]
  have hj : 0 + 1 < Multiset.card (([i, i] : List I) : Multiset I) := by simp
  have key := hS a _ (Rel.dot_cross_left 0 hj (seqList [i, i]))
  split_ifs at key with hc
  swap; · exact absurd rfl hc
  have hs := Diagram.sadj_smul_eq_self _ hj hc
  simp only [map_mul, map_sub, klrActFree_fe, klrActFree_fx, klrActFree_fψ, sub_mul, mul_assoc,
    wordE_eq, wordX_mul_single, wordΨ_mul_single, Category.id_comp, ← single_sub] at key
  rw [wordCross_def _ _ _ hj, wcrossTo, wordDot, wordDot, Category.assoc,
    S.eqToHom_wdot a _ (wswap_wordL a _ hj), ← single_eqToHom _ hs] at key
  have key' := congrFun (congrFun key (seqList [i, i])) (seqList [i, i])
  rw [single_apply_self, single_apply_self] at key'
  change (wl2 (𝟙 _) (S.cross i i rfl h₂ rfl h₂) ≫ (𝟙 (S.obj a) ≫ S.E i rfl) ◁ S.dot i h₂ ≫ 𝟙 _ -
    (𝟙 (S.obj a) ◁ S.dot i rfl) ▷ S.E i h₂ ≫ wl2 (𝟙 _) (S.cross i i rfl h₂ rfl h₂) ≫ 𝟙 _) ≫
      𝟙 _ = 𝟙 _ at key'
  simp only [Category.comp_id] at key'
  rw [← wl2_whiskerLeft, ← wl2_whiskerRight, wl2_comp, wl2_comp, wl2_sub, ← wl2_id] at key'
  exact wl2_one_injective key'

/-- The quadratic relation along a word, for arbitrary labels. -/
theorem RespectsKLR.wsquare_of (hS : RespectsKLR k S Q) (μ : X) {ν : Multiset I} (t : Seq ν)
    {j : ℕ} (hj : j + 1 < m ν) (hne : t.1 ⟨j, by omega⟩ ≠ t.1 ⟨j + 1, hj⟩)
    (L : List (I × X)) (hL : wordL RD μ t = L) (h : wValid RD μ L (wtop RD μ ν))
    (M : List (I × X)) (h₁ : wValid RD μ M (wtop RD μ ν))
    (e₁ : wswap RD j L = M) (e₂ : wswap RD j M = L) :
    S.wcrossTo μ j L M _ e₁ h h₁ ≫ S.wcrossTo μ j M L _ e₂ h₁ h =
      KLR.ncEval (A := End (S.wcell μ L _ h)) ![S.wdot μ j L _ h, S.wdot μ (j + 1) L _ h]
        (Q (t.1 ⟨j, by omega⟩) (t.1 ⟨j + 1, hj⟩)) := by
  subst hL
  have key := hS μ ν (Rel.cross_sq j hj t)
  split_ifs at key with hc
  · exact absurd hc hne
  have hss : sadj (m ν) j • sadj (m ν) j • t = t := by
    rw [smul_smul, sadj_mul_self, one_smul]
  rw [map_mul (S.klrActFree k μ ν) (KLR.ncEval _ _), AlgHom.map_ncEval] at key
  have e₂' : (fun r => S.klrActFree k μ ν (![fx k ν ⟨j, by omega⟩, fx k ν ⟨j + 1, hj⟩] r)) =
      fun r => S.wordX μ (![⟨j, by omega⟩, ⟨j + 1, hj⟩] r) := by
    funext r; fin_cases r <;> simp
  rw [e₂', klrActFree_fe, ← single_ncEval] at key
  simp only [map_mul, klrActFree_fe, klrActFree_fψ, mul_assoc, wordE_eq, wordΨ_mul_single,
    Category.id_comp] at key
  rw [← single_eqToHom _ hss] at key
  have key' := single_inj key
  simp only [wordCross_def _ _ _ hj, Category.assoc] at key'
  rw [S.wcrossTo_comp_eqToHom μ j _ _ _ _ (congrArg (wordL RD μ) hss)] at key'
  obtain rfl : M = wordL RD μ (sadj (m ν) j • t) := e₁.symm.trans (wswap_wordL μ t hj)
  have e₁' : (![S.wdot μ j (wordL RD μ t) _ h, S.wdot μ (j + 1) (wordL RD μ t) _ h] :
      Fin 2 → End (S.wordCell μ t)) =
      fun r => S.wordDot μ t (![⟨j, by omega⟩, ⟨j + 1, hj⟩] r) := by
    funext r; fin_cases r <;> rfl
  rw [e₁']
  exact key'

/-- A dot slides through a crossing of two strands with different labels (left dot). -/
theorem RespectsKLR.wslide_left_of (hS : RespectsKLR k S Q) (μ : X) {ν : Multiset I}
    (t : Seq ν) {j : ℕ} (hj : j + 1 < m ν) (hne : t.1 ⟨j, by omega⟩ ≠ t.1 ⟨j + 1, hj⟩)
    (L : List (I × X)) (hL : wordL RD μ t = L) (h : wValid RD μ L (wtop RD μ ν))
    (M : List (I × X)) (h₁ : wValid RD μ M (wtop RD μ ν)) (e₁ : wswap RD j L = M) :
    S.wdot μ j L _ h ≫ S.wcrossTo μ j L M _ e₁ h h₁ =
      S.wcrossTo μ j L M _ e₁ h h₁ ≫ S.wdot μ (j + 1) M _ h₁ := by
  subst hL
  have key := hS μ ν (Rel.dot_cross_right j hj t)
  split_ifs at key with hc
  · exact absurd hc hne
  simp only [map_mul, map_sub, map_zero, klrActFree_fe, klrActFree_fx, klrActFree_fψ, sub_mul,
    mul_assoc, wordE_eq, wordX_mul_single, wordΨ_mul_single, Category.id_comp,
    ← single_sub] at key
  rw [← single_zero] at key
  have key' := sub_eq_zero.1 (single_inj key)
  rw [wordCross_def _ _ _ hj] at key'
  obtain rfl : M = wordL RD μ (sadj (m ν) j • t) := e₁.symm.trans (wswap_wordL μ t hj)
  exact key'

/-- A dot slides through a crossing of two strands with different labels (right dot). -/
theorem RespectsKLR.wslide_right_of (hS : RespectsKLR k S Q) (μ : X) {ν : Multiset I}
    (t : Seq ν) {j : ℕ} (hj : j + 1 < m ν) (hne : t.1 ⟨j, by omega⟩ ≠ t.1 ⟨j + 1, hj⟩)
    (L : List (I × X)) (hL : wordL RD μ t = L) (h : wValid RD μ L (wtop RD μ ν))
    (M : List (I × X)) (h₁ : wValid RD μ M (wtop RD μ ν)) (e₁ : wswap RD j L = M) :
    S.wdot μ (j + 1) L _ h ≫ S.wcrossTo μ j L M _ e₁ h h₁ =
      S.wcrossTo μ j L M _ e₁ h h₁ ≫ S.wdot μ j M _ h₁ := by
  subst hL
  have key := hS μ ν (Rel.dot_cross_left j hj t)
  split_ifs at key with hc
  · exact absurd hc hne
  simp only [map_mul, map_sub, map_zero, klrActFree_fe, klrActFree_fx, klrActFree_fψ, sub_mul,
    mul_assoc, wordE_eq, wordX_mul_single, wordΨ_mul_single, Category.id_comp,
    ← single_sub] at key
  rw [← single_zero] at key
  have key' := sub_eq_zero.1 (single_inj key)
  rw [wordCross_def _ _ _ hj] at key'
  obtain rfl : M = wordL RD μ (sadj (m ν) j • t) := e₁.symm.trans (wswap_wordL μ t hj)
  exact key'.symm

/-- Brundan (1.2), distinct colours: a dot on the right strand slides through. -/
theorem RespectsKLR.slide_left_ne (hS : RespectsKLR k S Q) (i j : I) (hij : i ≠ j) {a b c d : X}
    (h₁ : a + RD.iX j = b) (h₂ : b + RD.iX i = d)
    (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d) :
    S.E j h₁ ◁ S.dot i h₂ ≫ S.cross i j h₁ h₂ h₃ h₄ =
      S.cross i j h₁ h₂ h₃ h₄ ≫ S.dot i h₃ ▷ S.E j h₄ := by
  subst h₁ h₃
  obtain rfl : d = wtop RD a (([i, j] : List I) : Multiset I) := by
    rw [← h₂, wtop]; simp; abel
  have key := hS.wslide_left_of a (seqList [i, j]) (j := 0) (by simp) hij
    [(i, a + RD.iX j), (j, a)] rfl (wValid_wordL (RD := RD) a (seqList [i, j])) [(j, a + RD.iX i), (i, a)]
    ⟨⟨rfl, rfl⟩, h₄⟩ rfl
  change (𝟙 (S.obj a) ≫ S.E j rfl) ◁ S.dot i h₂ ≫ (wl2 (𝟙 _) (S.cross i j rfl h₂ rfl h₄) ≫ 𝟙 _) =
    (wl2 (𝟙 _) (S.cross i j rfl h₂ rfl h₄) ≫ 𝟙 _) ≫ (𝟙 (S.obj a) ◁ S.dot i rfl) ▷ S.E j h₄ at key
  rw [Category.comp_id, ← wl2_whiskerLeft, ← wl2_whiskerRight, wl2_comp, wl2_comp] at key
  exact wl2_one_injective key

/-- Brundan (1.2), distinct colours: a dot on the left strand slides through. -/
theorem RespectsKLR.slide_right_ne (hS : RespectsKLR k S Q) (i j : I) (hij : i ≠ j)
    {a b c d : X} (h₁ : a + RD.iX j = b) (h₂ : b + RD.iX i = d)
    (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d) :
    S.dot j h₁ ▷ S.E i h₂ ≫ S.cross i j h₁ h₂ h₃ h₄ =
      S.cross i j h₁ h₂ h₃ h₄ ≫ S.E i h₃ ◁ S.dot j h₄ := by
  subst h₁ h₃
  obtain rfl : d = wtop RD a (([i, j] : List I) : Multiset I) := by
    rw [← h₂, wtop]; simp; abel
  have key := hS.wslide_right_of a (seqList [i, j]) (j := 0) (by simp) hij
    [(i, a + RD.iX j), (j, a)] rfl (wValid_wordL (RD := RD) a (seqList [i, j]))
    [(j, a + RD.iX i), (i, a)] ⟨⟨rfl, rfl⟩, h₄⟩ rfl
  change (𝟙 (S.obj a) ◁ S.dot j rfl) ▷ S.E i h₂ ≫ (wl2 (𝟙 _) (S.cross i j rfl h₂ rfl h₄) ≫ 𝟙 _) =
    (wl2 (𝟙 _) (S.cross i j rfl h₂ rfl h₄) ≫ 𝟙 _) ≫ (𝟙 (S.obj a) ≫ S.E i rfl) ◁ S.dot j h₄ at key
  rw [Category.comp_id, ← wl2_whiskerLeft, ← wl2_whiskerRight, wl2_comp, wl2_comp] at key
  exact wl2_one_injective key

variable [AdditiveWhiskering B] in
/-- Brundan (1.3), distinct colours: the square of a crossing is `Q i j` of the dots. -/
theorem RespectsKLR.square_ne
    [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
    [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] (hS : RespectsKLR k S Q) (i j : I) (hij : i ≠ j) {a b c d : X}
    (h₁ : a + RD.iX j = b) (h₂ : b + RD.iX i = d)
    (h₃ : a + RD.iX i = c) (h₄ : c + RD.iX j = d) :
    S.cross i j h₁ h₂ h₃ h₄ ≫ S.cross j i h₃ h₄ h₁ h₂ =
      KLR.ncEval (A := End (S.E j h₁ ≫ S.E i h₂))
        ![S.E j h₁ ◁ S.dot i h₂, S.dot j h₁ ▷ S.E i h₂] (Q i j) := by
  subst h₁ h₃
  obtain rfl : d = wtop RD a (([i, j] : List I) : Multiset I) := by
    rw [← h₂, wtop]; simp; abel
  have key := hS.wsquare_of a (seqList [i, j]) (j := 0) (by simp) hij
    [(i, a + RD.iX j), (j, a)] rfl (wValid_wordL (RD := RD) a (seqList [i, j]))
    [(j, a + RD.iX i), (i, a)] ⟨⟨rfl, rfl⟩, h₄⟩ rfl rfl
  change (wl2 (𝟙 _) (S.cross i j rfl h₂ rfl h₄) ≫ 𝟙 _) ≫
      (wl2 (𝟙 _) (S.cross j i rfl h₄ rfl h₂) ≫ 𝟙 _) =
    KLR.ncEval (A := End ((𝟙 (S.obj a) ≫ S.E j rfl) ≫ S.E i h₂))
      ![(𝟙 (S.obj a) ≫ S.E j rfl) ◁ S.dot i h₂, (𝟙 (S.obj a) ◁ S.dot j rfl) ▷ S.E i h₂]
      (Q i j) at key
  rw [Category.comp_id, Category.comp_id, ← wl2_whiskerLeft, ← wl2_whiskerRight,
    ← wl2_ncEval₂, wl2_comp] at key
  exact wl2_one_injective key

/-- Brundan (1.4), distinct outer colours: the braid relation. -/
theorem RespectsKLR.braid_ne (hS : RespectsKLR k S Q) (i j c : I) (hb : i ≠ c)
    {l w₁ w₂ w₃ w₄ w₅ w₆ μ : X} (e1 : l + RD.iX c = w₁) (e2 : w₁ + RD.iX j = w₂)
    (e3 : w₂ + RD.iX i = μ) (e4 : w₁ + RD.iX i = w₃) (e5 : w₃ + RD.iX j = μ)
    (e6 : l + RD.iX i = w₄) (e7 : w₄ + RD.iX c = w₃) (e8 : w₄ + RD.iX j = w₅)
    (e9 : w₅ + RD.iX c = μ) (e10 : l + RD.iX j = w₆) (e11 : w₆ + RD.iX c = w₂)
    (e12 : w₆ + RD.iX i = w₅) :
    S.E c e1 ◁ S.cross i j e2 e3 e4 e5 ≫
        ((α_ (S.E c e1) (S.E i e4) (S.E j e5)).inv ≫ S.cross i c e1 e4 e6 e7 ▷ S.E j e5 ≫
          (α_ (S.E i e6) (S.E c e7) (S.E j e5)).hom) ≫
        S.E i e6 ◁ S.cross j c e7 e5 e8 e9 =
      ((α_ (S.E c e1) (S.E j e2) (S.E i e3)).inv ≫ S.cross j c e1 e2 e10 e11 ▷ S.E i e3 ≫
          (α_ (S.E j e10) (S.E c e11) (S.E i e3)).hom) ≫
        S.E j e10 ◁ S.cross i c e11 e3 e12 e9 ≫
        ((α_ (S.E j e10) (S.E i e12) (S.E c e9)).inv ≫ S.cross i j e10 e12 e6 e8 ▷ S.E c e9 ≫
          (α_ (S.E i e6) (S.E j e8) (S.E c e9)).hom) := by
  subst e1 e2 e4 e6 e8 e10
  obtain rfl : μ = wtop RD l (([i, j, c] : List I) : Multiset I) := by
    rw [← e3, wtop]; simp; abel
  have hj : 0 + 2 < Multiset.card (([i, j, c] : List I) : Multiset I) := by simp
  have key := hS.wbraid_of l (seqList [i, j, c]) hj (fun h => hb h.1)
    [(i, l + RD.iX c + RD.iX j), (j, l + RD.iX c), (c, l)] rfl
    (wValid_wordL (RD := RD) l (seqList [i, j, c]))
    [(j, l + RD.iX c + RD.iX i), (i, l + RD.iX c), (c, l)]
    [(j, l + RD.iX c + RD.iX i), (c, l + RD.iX i), (i, l)]
    [(c, l + RD.iX i + RD.iX j), (j, l + RD.iX i), (i, l)]
    [(i, l + RD.iX c + RD.iX j), (c, l + RD.iX j), (j, l)]
    [(c, l + RD.iX i + RD.iX j), (i, l + RD.iX j), (j, l)]
    ⟨⟨⟨rfl, rfl⟩, rfl⟩, e5⟩ ⟨⟨⟨rfl, rfl⟩, e7⟩, e5⟩ ⟨⟨⟨rfl, rfl⟩, rfl⟩, e9⟩
    ⟨⟨⟨rfl, rfl⟩, e11⟩, e3⟩ ⟨⟨⟨rfl, rfl⟩, e12⟩, e9⟩
    rfl rfl rfl rfl (congrArg (fun x => (c, x) :: (i, l + RD.iX j) :: [(j, l)]) e12) rfl
  erw [S.wcrossTo_zero l i c _ _ _ _ _ _ _ _ e12] at key
  erw [S.wcrossTo_succ, S.wcrossTo_succ, S.wcrossTo_succ] at key
  erw [S.wcrossTo_zero_rfl, S.wcrossTo_zero_rfl, S.wcrossTo_zero_rfl, S.wcrossTo_zero_rfl,
    S.wcrossTo_zero_rfl] at key
  apply wl3_one_injective
  rw [wl3_braid_left, wl3_braid_right]
  exact key

variable [AdditiveWhiskering B] in
/-- Brundan (1.4), repeated outer colour: the braid relation with correction `qbar (Q i j)`. -/
theorem RespectsKLR.braidQ_ne
    [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
    [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] (hS : RespectsKLR k S Q) (i j : I) (hij : i ≠ j) {a b c d e f : X}
    (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX j = c) (h₃ : c + RD.iX i = f)
    (h₄ : b + RD.iX i = d) (h₅ : d + RD.iX j = f)
    (h₆ : a + RD.iX j = e) (h₇ : e + RD.iX i = c) :
    (S.E i h₁ ◁ S.cross i j h₂ h₃ h₄ h₅ ≫
      ((α_ (S.E i h₁) (S.E i h₄) (S.E j h₅)).inv ≫
        S.cross i i h₁ h₄ h₁ h₄ ▷ S.E j h₅ ≫
        (α_ (S.E i h₁) (S.E i h₄) (S.E j h₅)).hom) ≫
      S.E i h₁ ◁ S.cross j i h₄ h₅ h₂ h₃) -
    (((α_ (S.E i h₁) (S.E j h₂) (S.E i h₃)).inv ≫
      S.cross j i h₁ h₂ h₆ h₇ ▷ S.E i h₃ ≫
      (α_ (S.E j h₆) (S.E i h₇) (S.E i h₃)).hom) ≫
      S.E j h₆ ◁ S.cross i i h₇ h₃ h₇ h₃ ≫
      ((α_ (S.E j h₆) (S.E i h₇) (S.E i h₃)).inv ≫
        S.cross i j h₆ h₇ h₁ h₂ ▷ S.E i h₃ ≫
        (α_ (S.E i h₁) (S.E j h₂) (S.E i h₃)).hom)) =
      KLR.ncEval (A := End (S.E i h₁ ≫ (S.E j h₂ ≫ S.E i h₃)))
        ![S.E i h₁ ◁ (S.E j h₂ ◁ S.dot i h₃),
          S.E i h₁ ◁ (S.dot j h₂ ▷ S.E i h₃),
          S.dot i h₁ ▷ (S.E j h₂ ≫ S.E i h₃)] (KLR.qbar (Q i j)) := by
  subst h₁ h₂ h₄ h₆
  obtain rfl : f = wtop RD a (([i, j, i] : List I) : Multiset I) := by
    rw [← h₃, wtop]; simp; abel
  have hj : 0 + 2 < Multiset.card (([i, j, i] : List I) : Multiset I) := by simp
  have key := hS.wbraidQ_of a (seqList [i, j, i]) hj rfl hij
    [(i, a + RD.iX i + RD.iX j), (j, a + RD.iX i), (i, a)] rfl
    (wValid_wordL (RD := RD) a (seqList [i, j, i]))
    [(j, a + RD.iX i + RD.iX i), (i, a + RD.iX i), (i, a)]
    [(j, a + RD.iX i + RD.iX i), (i, a + RD.iX i), (i, a)]
    [(i, a + RD.iX i + RD.iX j), (i, a + RD.iX j), (j, a)]
    [(i, a + RD.iX i + RD.iX j), (i, a + RD.iX j), (j, a)]
    ⟨⟨⟨rfl, rfl⟩, rfl⟩, h₅⟩ ⟨⟨⟨rfl, rfl⟩, rfl⟩, h₅⟩ ⟨⟨⟨rfl, rfl⟩, h₇⟩, h₃⟩ ⟨⟨⟨rfl, rfl⟩, h₇⟩, h₃⟩
    rfl rfl rfl rfl (congrArg (fun x => (i, x) :: (i, a + RD.iX j) :: [(j, a)]) h₇) rfl
  erw [S.wcrossTo_zero a i i _ _ _ _ _ _ _ _ h₇] at key
  erw [S.wcrossTo_succ, S.wcrossTo_succ, S.wcrossTo_succ] at key
  erw [S.wcrossTo_zero_rfl, S.wcrossTo_zero_rfl, S.wcrossTo_zero_rfl, S.wcrossTo_zero_rfl,
    S.wcrossTo_zero_rfl] at key
  apply wl3_one_injective
  rw [← wl3_sub, wl3_braid_left, wl3_braid_right, wl3_ncEval₃, wl3_dot₀, wl3_dot₁, wl3_dot₂]
  exact key

variable [AdditiveWhiskering B] in
/-- **A Rouquier family from an action of the KLR algebras.** Rouquier data whose generators
satisfy the defining relations of `R(ν)`, together with right adjoints and the inverses of
Rouquier's maps (Brundan, Definition 1.1, (1.8)/(1.9)), form a Rouquier family. -/
def RespectsKLR.toRouqFamily (hS : RespectsKLR k S Q)
    (F : ∀ (i : I) {x y : X}, x + RD.iX i = y → (S.obj y ⟶ S.obj x))
    (adj : ∀ (i : I) {x y : X} (h : x + RD.iX i = y), S.E i h ⊣ F i h)
    (invPos : ∀ (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c),
      0 ≤ RD.pair (RD.iY i) b →
      SumInvTo (RightwardCrossing.sigma (adj i h₂).unit (S.cross i i h₁ h₂ h₁ h₂)
        (adj i h₁).counit) (fun n => F i h₁ ◁ powComp (S.dot i h₁) n ≫ (adj i h₁).counit)
        (RD.pair (RD.iY i) b).toNat)
    (invNeg : ∀ (i : I) {a b c : X} (h₁ : a + RD.iX i = b) (h₂ : b + RD.iX i = c),
      RD.pair (RD.iY i) b ≤ 0 →
      SumInvFrom (RightwardCrossing.sigma (adj i h₂).unit (S.cross i i h₁ h₂ h₁ h₂)
        (adj i h₁).counit) (fun n => (adj i h₂).unit ≫ powComp (S.dot i h₂) n ▷ F i h₂)
        (-RD.pair (RD.iY i) b).toNat) :
    RouqFamily (B := B) RD where
  toRouqData := S
  F := F
  adj := adj
  square i _ _ _ h₁ h₂ := hS.square i h₁ h₂
  braid i _ _ _ _ h₁ h₂ h₃ := hS.braid i h₁ h₂ h₃
  loc i _ _ _ h₁ h₂ :=
    { slide_left := hS.slide_left i h₁ h₂
      slide_right := hS.slide_right i h₁ h₂
      invPos := invPos i h₁ h₂
      invNeg := invNeg i h₁ h₂ }

end RouqData

variable [AdditiveWhiskering B] in
/-- **Brundan, arXiv:1501.00350v1, Definition 1.1, (1.2)–(1.4)** for a Rouquier family whose
generators satisfy the defining relations of the KLR algebras `R(ν)` for `Q`: the mixed
upward equations hold. -/
theorem RouqFamily.rouqUpKLR_of_respectsKLR
    [∀ (a b c : B) (f : a ⟶ b), (precomp c f).Linear k]
    [∀ (a b c : B) (f : b ⟶ c), (postcomp a f).Linear k] {S : RouqFamily (B := B) RD}
    {Q : I → I → MvPolynomial (Fin 2) k} (hS : S.toRouqData.RespectsKLR k Q) :
    RouqUpKLR S Q where
  square i j hij _ _ _ _ h₁ h₂ h₃ h₄ := hS.square_ne i j hij h₁ h₂ h₃ h₄
  slide_left i j hij _ _ _ _ h₁ h₂ h₃ h₄ := hS.slide_left_ne i j hij h₁ h₂ h₃ h₄
  slide_right i j hij _ _ _ _ h₁ h₂ h₃ h₄ := hS.slide_right_ne i j hij h₁ h₂ h₃ h₄
  braid i j c hb _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 :=
    hS.braid_ne i j c hb e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  braidQ i j hij _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ := hS.braidQ_ne i j hij h₁ h₂ h₃ h₄ h₅ h₆ h₇

end Categorification.TwoRep
