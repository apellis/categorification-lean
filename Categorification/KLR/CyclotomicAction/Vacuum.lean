/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.GlobalFamily
import Categorification.TwoRep.RouqKLRAction
import Categorification.KLR.Symmetries

/-!
# Words of the cyclotomic family applied to the vacuum

In the cyclotomic Rouquier family `cyclotomicFamily` (cyclotomic induction of Kang–Kashiwara,
arXiv:1102.4677v4, §4.2), a word `E_{t_0} ⋯ E_{t_{m-1}}` applied to the vacuum `R^Λ(∅) = k`
is the cyclotomic module `R^Λ(ν) e(rev t)`: induction adds the new strand at the right end, and
the first functor applied is the last letter. This file computes the action of the KLR algebra
on these words through the generator `wgen t ↦ e(rev t)` (`wcoord_wgen`):

* `wordDot_wgen`, `wordCross_wgen`: the dot on strand `b` acts by `x_{rev b}`, the crossing of
  the strands `j, j + 1` by `± ψ_{m-2-j}` (the sign of the crossing for equal colours);
* `klrAct_wgen`: the `(t, s)` entry of `klrAct r` sends the generator of `t` to
  `hflip (σ (e(s) r e(t)))` times the generator of `s`, where `σ` is the left–right mirror and
  `hflip` the top–bottom flip of Khovanov–Lauda I (arXiv:0803.4121v2, end of §2.1);
* `mk_hflip_sigma_eq_zero`: if `r` acts by zero on the words of weight `ν` at the weight `-Λ`,
  then `hflip (σ r) = 0` in `R^Λ(ν)`.

This is the cyclotomic corner of Webster's argument for nondegeneracy (Webster,
*Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the nondegeneracy
theorem): the images of the words at the vacuum are the cyclotomic quotients, read through the
anti-involution `hflip ∘ σ`.
-/

namespace Categorification.KLR.CyclotomicAction

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits TwoRep KLRAlgebra
open InductionAlong (Ind unitGen)

universe u v w u₁

noncomputable section

section Seqs

variable {I : Type u} {X : Type u₁} {k : Type v}

/-! ### The idempotent of a word applied to the vacuum -/

theorem coe_reverse_map_fst {L : List (I × X)} {β : Multiset I} (hβ : β = ↑(L.map Prod.fst)) :
    (↑(L.map Prod.fst).reverse : Multiset I) = β := by
  rw [Multiset.coe_reverse, hβ]

/-- The sequence of the strands of a word applied to the vacuum: the letters in reverse order
(the last 1-morphism adds the last strand). -/
def wseq (L : List (I × X)) {β : Multiset I} (hβ : β = ↑(L.map Prod.fst)) : Seq β :=
  ⟨fun x => (L.map Prod.fst).reverse.get (Fin.cast (by rw [← coe_reverse_map_fst hβ,
      Multiset.coe_card]) x), by
    rw [Fin.univ_val_map, ← List.ofFn_congr (by rw [← coe_reverse_map_fst hβ,
      Multiset.coe_card]) (L.map Prod.fst).reverse.get, List.ofFn_get, coe_reverse_map_fst hβ]⟩

theorem labels_wseq (c : I) (ν : X) (L : List (I × X)) {β δ : Multiset I}
    (hβ : β = ↑(L.map Prod.fst)) (hδ : δ = ↑(((c, ν) :: L).map Prod.fst)) :
    Labels (wseq L hβ) (fun _ => c) (wseq ((c, ν) :: L) hδ) := by
  intro x
  have hcard : Multiset.card β = L.length := by rw [hβ, Multiset.coe_card, List.length_map]
  simp only [wseq, List.map_cons, List.reverse_cons, List.get_eq_getElem, Fin.val_cast]
  split_ifs with hx
  · rw [List.getElem_append_left (by simp; omega)]
  · rw [List.getElem_append_right (by simp; omega)]
    simp

variable (k) in
/-- The sign of the crossing of the letters `j`, `j + 1` of a list: `-1` if they are equal. -/
def lsgn [DecidableEq I] [CommRing k] (j : ℕ) (l : List I) : k := if l[j]? = l[j + 1]? then -1 else 1

variable [AddCommGroup X] {C : QuantumGroup.CartanDatum I} {Y : Type u₁} [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y}

theorem map_fst_wswap_perm : ∀ (j : ℕ) (L : List (I × X)),
    ((wswap RD j L).map Prod.fst).Perm (L.map Prod.fst)
  | 0, (_, _) :: (_, _) :: _ => List.Perm.swap _ _ _
  | j + 1, _ :: L => (map_fst_wswap_perm j L).cons _
  | 0, [] => List.Perm.refl _
  | 0, [_] => List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _

theorem map_fst_wswap {j : ℕ} {L : List (I × X)} {β : Multiset I} (hβ : β = ↑(L.map Prod.fst)) :
    β = ↑((wswap RD j L).map Prod.fst) := by
  rw [hβ]
  exact Multiset.coe_eq_coe.2 (map_fst_wswap_perm j L).symm

end Seqs

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {a : I → Polynomial k}
  (hQ : KLRSymm Q)
  (hlead : ∀ j l, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type u₁} [AddCommGroup X] [AddCommGroup Y]
  {RD : QuantumGroup.UDot.WeightDatum C X Y} {Λ : X}
  (hΛ : ∀ i, ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ i j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cyclotomicFamily.{u, v, w} hQ hlead ha RD Λ hΛ hdeg

variable {μ : X} (V : weightSpace.{u, v, w} Q a RD Λ μ)

omit [DecidableEq I] in
/-- The block of a weighted word from `μ`, when `μ` is the weight of the empty block. -/
theorem blockWeight_wValid (h0 : blockWeight RD Λ 0 = μ) :
    ∀ (L : List (I × X)) (μ' : X), wValid RD μ L μ' →
      blockWeight RD Λ (↑(L.map Prod.fst) : Multiset I) = μ'
  | [], μ', h => by simpa using h0.trans h
  | (c, ν) :: L, μ', h => by
    rw [List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add, blockWeight_cons,
      blockWeight_wValid h0 L ν h.1, h.2]

/-- The block of the letters of a weighted word. -/
def wblk (h0 : blockWeight RD Λ 0 = μ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ') :
    WeightBlocks RD Λ μ' :=
  ⟨↑(L.map Prod.fst), blockWeight_wValid h0 L μ' h⟩

omit [DecidableEq I] in
theorem blockSucc_wblk (h0 : blockWeight RD Λ 0 = μ) (c : I) (ν : X) (L : List (I × X))
    {μ' : X} (h : wValid RD μ ((c, ν) :: L) μ') {δ : WeightBlocks RD Λ μ'}
    (hδ : δ.1 = ↑(((c, ν) :: L).map Prod.fst)) :
    blockSucc RD Λ c h.2 (wblk h0 L ν h.1) = δ := by
  apply Subtype.ext
  rw [blockSucc_val, hδ, List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add]
  rfl

variable (h0 : blockWeight RD Λ 0 = μ) (v₀ : V ⟨0, h0⟩)

/-- **The generator of a word applied to the vacuum**: `z_∅ ↦ e(β, c) ⊗ ⋯`, built one strand
at a time. -/
def vgen : ∀ (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ') (δ : WeightBlocks RD Λ μ'),
    δ.1 = ↑(L.map Prod.fst) → ((RouqFamily.wcell (S) μ L μ' h).obj.obj V δ : Type _)
  | [], μ', h, δ, hδ => by
    subst h
    obtain ⟨δ, hw⟩ := δ
    simp only [List.map_nil, Multiset.coe_nil] at hδ
    subst hδ
    exact v₀
  | (c, ν) :: L, μ', h, δ, hδ =>
    (blockι (blockSucc RD Λ c h.2) (indBlock Q a RD Λ c h.2)
      ((RouqFamily.wcell (S) μ L ν h.1).obj.obj V) ⟨wblk h0 L ν h.1, blockSucc_wblk h0 c ν L h hδ⟩).hom
      (InductionAlong.Ind.tmul (InductionAlong.unitGen _) (vgen L ν h.1 (wblk h0 L ν h.1) rfl))

variable (Ψ₀ : V ⟨0, h0⟩ →ₗ[CycKLR k Q a 0] CycKLR k Q a 0)

/-- **The coordinate of a word applied to the vacuum**: the `R^Λ(δ)`-linear map to `R^Λ(δ)`,
`z ⊗ n ↦ z · ι(Ψ n)`, built one strand at a time from `Ψ₀`. -/
def vcoord : ∀ (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ') (δ : WeightBlocks RD Λ μ'),
    δ.1 = ↑(L.map Prod.fst) →
      (((RouqFamily.wcell (S) μ L μ' h).obj.obj V δ : Type _) →ₗ[CycKLR k Q a δ.1] CycKLR k Q a δ.1)
  | [], μ', h, δ, hδ => by
    subst h
    obtain ⟨δ, hw⟩ := δ
    simp only [List.map_nil, Multiset.coe_nil] at hδ
    subst hδ
    exact Ψ₀
  | (c, ν) :: L, μ', h, δ, hδ =>
    (InductionAlong.Ind.lift
      (fun z n => z.1 * lastEmb Q a c (blockSucc_eq RD Λ c (blockSucc_wblk h0 c ν L h hδ))
        (vcoord L ν h.1 (wblk h0 L ν h.1) rfl n))
      (fun z z' n => add_mul _ _ _)
      (fun z n n' => by rw [map_add, map_add, mul_add])
      (fun z r n => by
        change z.1 * _ * _ = _
        rw [map_smul, smul_eq_mul, map_mul, mul_assoc]; rfl)
      (fun b z n => mul_assoc _ _ _)).comp
      (biproduct.π (fun p : {β // blockSucc RD Λ c h.2 β = δ} =>
        (indBlock Q a RD Λ c h.2 p.1 δ p.2).obj ((RouqFamily.wcell (S) μ L ν h.1).obj.obj V p.1))
        ⟨wblk h0 L ν h.1, blockSucc_wblk h0 c ν L h hδ⟩).hom

/-! ### Induction, dots and crossings on generators -/

section Generators

open InductionAlong

/-- Acting on `φ(1) ⊗ n` by `φ(r)` is acting on `n` by `r`. -/
theorem smul_tmul_unitGen.{w₂, w₃} {A B : Type w₂} [Ring A] [Ring B] {φ : A →ₙ+* B}
    {N : Type w₃} [AddCommGroup N] [Module A N] (r : A) (n : N) :
    φ r • (InductionAlong.Ind.tmul (InductionAlong.unitGen φ) n : InductionAlong.Ind N φ) =
      InductionAlong.Ind.tmul (InductionAlong.unitGen φ) (r • n) := by
  rw [InductionAlong.Ind.smul_tmul, ← InductionAlong.Ind.op_smul_tmul]
  congr 1
  exact Subtype.ext (by
    change φ r * φ 1 = φ 1 * φ r
    rw [← map_mul, ← map_mul, mul_one, one_mul])

theorem biproduct_ι_map_apply.{w₂, w₃} {R : Type*} [Ring R] {J : Type w₃}
    {F G : J → ModuleCat.{w₂} R} [HasBiproduct F] [HasBiproduct G] (f : ∀ j, F j ⟶ G j) (p : J)
    (y : F p) :
    (biproduct.map f).hom ((biproduct.ι F p).hom y) = (biproduct.ι G p).hom ((f p).hom y) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, biproduct.ι_map]
  rfl

theorem blockι_map_apply.{w₂, w₃, w₄, w₅, w₆, w₇} {A : Type w₃} {Dd : Type w₄} (s : A → Dd)
    {Cc : A → Type w₅} [∀ a, Category.{w₆} (Cc a)] {R : Dd → Type w₂} [∀ d, Ring (R d)] [∀ d, Finite {a // s a = d}]
    (L : ∀ (a : A) (d : Dd), s a = d → Cc a ⥤ ModuleCat.{max w₂ w₇} (R d)) {M M' : ∀ a, Cc a}
    (f : M ⟶ M') {d : Dd} (p : {a // s a = d}) (y : (L p.1 d p.2).obj (M p.1)) :
    ((blockSum s L).map f d).hom ((blockι s L M p).hom y) =
      (blockι s L M' p).hom (((L p.1 d p.2).map (f p.1)).hom y) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, blockι_map]
  rfl

theorem blockι_blockSumMap_apply.{w₂, w₃, w₄, w₅, w₆, w₇} {A : Type w₃} {Dd : Type w₄}
    (s : A → Dd) {Cc : A → Type w₅} [∀ a, Category.{w₆} (Cc a)] {R : Dd → Type w₂}
    [∀ d, Ring (R d)] [∀ d, Finite {a // s a = d}]
    {L L' : ∀ (a : A) (d : Dd), s a = d → Cc a ⥤ ModuleCat.{max w₂ w₇} (R d)}
    (α : ∀ (a : A) (d : Dd) (h : s a = d), L a d h ⟶ L' a d h) (M : ∀ a, Cc a) {d : Dd}
    (p : {a // s a = d}) (y : (L p.1 d p.2).obj (M p.1)) :
    ((blockSumMap s α).app M d).hom ((blockι s L M p).hom y) =
      (blockι s L' M p).hom (((α p.1 d p.2).app (M p.1)).hom y) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, blockι_blockSumMap]
  rfl

theorem ind_map_tmul.{w₂, w₃} {A B : Type w₂} [Ring A] [Ring B] {φ : A →ₙ+* B}
    {N N' : ModuleCat.{max w₂ w₃} A} (g : N ⟶ N') (z : InductionAlong.Corner φ) (n : N) :
    ((InductionAlong.functor.{w₂, w₃} φ).map g).hom (Ind.tmul z n) = Ind.tmul z (g.hom n) := rfl

theorem dot_app_unitGen (i : I) {β δ : Multiset I} (h : {i} + β = δ)
    (N : ModuleCat.{max (max u v) w} (CycKLR k Q a β)) (n : N) :
    ((dot.{u, v, w} Q a i h).app N).hom (Ind.tmul (unitGen _) n) =
      dotElt Q a i h • (Ind.tmul (unitGen _) n : Ind N (lastEmb Q a i h)) := by
  change Ind.tmul (cornerMul _ _) n = _
  rw [Ind.smul_tmul]
  congr 1
  exact Subtype.ext ((intertwines_dotElt Q a i h 1))

theorem cross_app_unitGen (i j : I) {γ β β' δ : Multiset I} (h₁ : {j} + γ = β)
    (h₂ : {i} + β = δ) (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ)
    (N : ModuleCat.{max (max u v) w} (CycKLR k Q a γ)) (n : N) :
    ((cross.{u, v, w} Q a i j h₁ h₂ h₃ h₄).app N).hom
        (Ind.tmul (unitGen (lastEmb Q a i h₂)) (Ind.tmul (unitGen (lastEmb Q a j h₁)) n)) =
      crossElt Q a (γ := γ) (δ := δ) •
        Ind.tmul (unitGen (lastEmb Q a j h₄)) (Ind.tmul (unitGen (lastEmb Q a i h₃)) n) := by
  change Ind.tmul (outer _ _ (cornerMul (intertwines_crossElt Q a i j h₁ h₂ h₃ h₄)
      (compMul _ _ (unitGen _) (unitGen _)))) (Ind.tmul (unitGen _) n) = _
  have hu : outer (lastEmb Q a i h₃) (lastEmb Q a j h₄)
      (cornerMul (intertwines_crossElt Q a i j h₁ h₂ h₃ h₄)
        (compMul (lastEmb Q a j h₁) (lastEmb Q a i h₂) (unitGen _) (unitGen _))) =
      MulOpposite.op (lastEmb Q a i h₃ 1) • (crossElt Q a (γ := γ) (δ := δ) • unitGen _) := by
    apply Subtype.ext
    change lastEmb Q a i h₂ 1 * lastEmb Q a i h₂ (lastEmb Q a j h₁ 1) * crossElt Q a =
      crossElt Q a * lastEmb Q a j h₄ 1 * lastEmb Q a j h₄ (lastEmb Q a i h₃ 1)
    rw [← map_mul, one_mul, mul_assoc, ← map_mul, one_mul]
    exact intertwines_crossElt Q a i j h₁ h₂ h₃ h₄ 1
  rw [hu, Ind.op_smul_tmul, smul_tmul_unitGen, one_smul, Ind.smul_tmul]

theorem signedCross_app_unitGen (i j : I) {γ β β' δ : Multiset I} (h₁ : {j} + γ = β)
    (h₂ : {i} + β = δ) (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ)
    (N : ModuleCat.{max (max u v) w} (CycKLR k Q a γ)) (n : N) :
    ((signedCross.{u, v, w} Q a i j h₁ h₂ h₃ h₄).app N).hom
        (Ind.tmul (unitGen (lastEmb Q a i h₂)) (Ind.tmul (unitGen (lastEmb Q a j h₁)) n)) =
      ((if i = j then -1 else 1 : k) • crossElt Q a (γ := γ) (δ := δ)) •
        Ind.tmul (unitGen (lastEmb Q a j h₄)) (Ind.tmul (unitGen (lastEmb Q a i h₃)) n) := by
  rw [signedCross]
  split_ifs with hij
  · rw [NatTrans.app_neg, ModuleCat.hom_neg]
    erw [LinearMap.neg_apply, cross_app_unitGen]
    rw [neg_smul, one_smul, neg_smul]
    rfl
  · rw [cross_app_unitGen, one_smul]

theorem lastEmb_smul (i : I) {β δ : Multiset I} (h : {i} + β = δ) (c : k)
    (r : CycKLR k Q a β) : lastEmb Q a i h (c • r) = c • lastEmb Q a i h r := by
  rw [Algebra.smul_def, map_mul, lastEmb_scalarCompatible Q a i h c, mul_assoc, ← map_mul,
    one_mul, ← Algebra.smul_def]

end Generators

omit [AddCommGroup X] in
theorem lastIncl_e_wseq (c : I) (ν : X) (L : List (I × X)) {β δ : Multiset I}
    (hβ : β = ↑(L.map Prod.fst)) (hδ : δ = ↑(((c, ν) :: L).map Prod.fst)) (hc : {c} + β = δ) :
    lastIncl Q c hc (e (wseq L hβ)) = e (wseq ((c, ν) :: L) hδ) := by
  obtain ⟨t, ht, hl⟩ := (isLeftBlock_lastIncl (Q := Q) c hc).e_eq (wseq L hβ)
  rw [ht, hl.unique (labels_wseq c ν L hβ hδ)]

theorem e_seq_zero (s : Seq (0 : Multiset I)) : (e s : KLRAlgebra k Q 0) = 1 := by
  rw [← sum_e, Finset.sum_eq_single s (fun b _ hb => (hb (Subsingleton.elim _ _)).elim)
    (fun h => (h (Finset.mem_univ _)).elim)]

/-- The projection of the inclusion of a summand of a biproduct of modules. -/
theorem biproduct_ι_π_apply.{w₂, w₃} {R : Type*} [Ring R] {J : Type w₃} (F : J → ModuleCat.{w₂} R)
    [HasBiproduct F] (p : J) (y : F p) :
    (biproduct.π F p).hom ((biproduct.ι F p).hom y) = y := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, biproduct.ι_π_self]
  rfl

/-! ### The generator and its coordinate -/

variable {V h0 v₀} in
/-- The generator of a nonempty word, through any representative of the intermediate block. -/
theorem vgen_cons (c : I) (ν : X) (L : List (I × X)) {μ' : X} (h : wValid RD μ ((c, ν) :: L) μ')
    {δ : WeightBlocks RD Λ μ'} (hδ : δ.1 = ↑(((c, ν) :: L).map Prod.fst))
    (β : WeightBlocks RD Λ ν) (p : blockSucc RD Λ c h.2 β = δ) (hβ : β.1 = ↑(L.map Prod.fst)) :
    vgen hQ hlead ha hΛ hdeg V h0 v₀ ((c, ν) :: L) μ' h δ hδ =
      (blockι (blockSucc RD Λ c h.2) (indBlock Q a RD Λ c h.2)
        ((RouqFamily.wcell (S) μ L ν h.1).obj.obj V) ⟨β, p⟩).hom
        (InductionAlong.Ind.tmul (InductionAlong.unitGen _)
          (vgen hQ hlead ha hΛ hdeg V h0 v₀ L ν h.1 β hβ)) := by
  obtain rfl : β = wblk h0 L ν h.1 := Subtype.ext hβ
  rfl

variable {Ψ₀} in
/-- **The coordinate of the generator is the idempotent of the reversed word.** -/
theorem vcoord_vgen (hΨ₀ : Ψ₀ v₀ = 1) : ∀ (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ')
    (δ : WeightBlocks RD Λ μ') (hδ : δ.1 = ↑(L.map Prod.fst)),
    vcoord hQ hlead ha hΛ hdeg V h0 Ψ₀ L μ' h δ hδ (vgen hQ hlead ha hΛ hdeg V h0 v₀ L μ' h δ hδ) =
      CycKLR.mk k Q a δ.1 (e (wseq L hδ))
  | [], μ', h, δ, hδ => by
    subst h
    obtain ⟨δ, hw⟩ := δ
    simp only [List.map_nil, Multiset.coe_nil] at hδ
    subst hδ
    rw [e_seq_zero, map_one]
    exact hΨ₀
  | (c, ν) :: L, μ', h, δ, hδ => by
    rw [vcoord, vgen]
    erw [LinearMap.coe_comp, Function.comp_apply, biproduct_ι_π_apply, InductionAlong.Ind.lift_tmul, vcoord_vgen hΨ₀ L ν h.1 (wblk h0 L ν h.1) rfl]
    change lastEmb Q a c _ 1 * lastEmb Q a c _ _ = _
    rw [← map_mul, one_mul, lastEmb_mk]
    exact congrArg _ (lastIncl_e_wseq c ν L _ hδ _)

/-- **The idempotent of the reversed word fixes the generator.** -/
theorem e_smul_vgen : ∀ (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ')
    (δ : WeightBlocks RD Λ μ') (hδ : δ.1 = ↑(L.map Prod.fst)),
    CycKLR.mk k Q a δ.1 (e (wseq L hδ)) • vgen hQ hlead ha hΛ hdeg V h0 v₀ L μ' h δ hδ =
      vgen hQ hlead ha hΛ hdeg V h0 v₀ L μ' h δ hδ
  | [], μ', h, δ, hδ => by
    subst h
    obtain ⟨δ, hw⟩ := δ
    simp only [List.map_nil, Multiset.coe_nil] at hδ
    subst hδ
    rw [e_seq_zero, map_one, one_smul]
  | (c, ν) :: L, μ', h, δ, hδ => by
    rw [vgen]
    erw [← map_smul]
    congr 1
    rw [← congrArg (CycKLR.mk k Q a δ.1) (lastIncl_e_wseq c ν L (rfl : (wblk h0 L ν h.1).1 = _) hδ
      (blockSucc_eq RD Λ c (blockSucc_wblk h0 c ν L h hδ))), ← lastEmb_mk]
    erw [smul_tmul_unitGen, e_smul_vgen L ν h.1 (wblk h0 L ν h.1) rfl]

/-! ### Whiskered transformations on generators -/

/-- A transformation of the inner word acting on the generator by `r` acts on the generator of
the word with one more strand by the image of `r` under the last-strand inclusion. -/
theorem vgen_whiskerRight (c : I) (ν : X) (L L' : List (I × X)) {μ' : X}
    (h : wValid RD μ ((c, ν) :: L) μ') (h' : wValid RD μ ((c, ν) :: L') μ')
    (f : RouqFamily.wcell (S) μ L ν h.1 ⟶ RouqFamily.wcell (S) μ L' ν h'.1)
    {δ : WeightBlocks RD Λ μ'} (hδ : δ.1 = ↑(((c, ν) :: L).map Prod.fst))
    (hδ' : δ.1 = ↑(((c, ν) :: L').map Prod.fst))
    (hβ' : (wblk h0 L ν h.1).1 = ↑(L'.map Prod.fst)) (r : CycKLR k Q a (wblk h0 L ν h.1).1)
    (hf : (f.hom.app V (wblk h0 L ν h.1)).hom (vgen hQ hlead ha hΛ hdeg V h0 v₀ L ν h.1 _ rfl) =
      r • vgen hQ hlead ha hΛ hdeg V h0 v₀ L' ν h'.1 _ hβ') :
    ((f ▷ (S).E c h.2).hom.app V δ).hom (vgen hQ hlead ha hΛ hdeg V h0 v₀ _ μ' h δ hδ) =
      lastEmb Q a c (blockSucc_eq RD Λ c (blockSucc_wblk h0 c ν L h hδ)) r •
        vgen hQ hlead ha hΛ hdeg V h0 v₀ _ μ' h' δ hδ' := by
  rw [vgen, vgen_cons hQ hlead ha hΛ hdeg c ν L' h' hδ' _ (blockSucc_wblk h0 c ν L h hδ) hβ']
  change ((blockSum (blockSucc RD Λ c h.2) (indBlock Q a RD Λ c h.2)).map (f.hom.app V) δ).hom
    ((blockι (blockSucc RD Λ c h.2) (indBlock Q a RD Λ c h.2)
      ((RouqFamily.wcell (S) μ L ν h.1).obj.obj V) ⟨wblk h0 L ν h.1, _⟩).hom _) = _
  refine (blockι_map_apply (blockSucc RD Λ c h.2)
    (R := fun δ : WeightBlocks RD Λ μ' => CycKLR k Q a δ.1) (indBlock Q a RD Λ c h.2)
    (f.hom.app V) _ _).trans ?_
  erw [ind_map_tmul, hf, ← smul_tmul_unitGen, map_smul]
  rfl

/-- **The dot on the last letter acts on the generator by the dot on the last strand.** -/
theorem vgen_dot (c : I) (ν : X) (L : List (I × X)) {μ' : X} (h : wValid RD μ ((c, ν) :: L) μ')
    {δ : WeightBlocks RD Λ μ'} (hδ : δ.1 = ↑(((c, ν) :: L).map Prod.fst)) :
    ((RouqFamily.wcell (S) μ L ν h.1 ◁ (S).dot c h.2).hom.app V δ).hom
        (vgen hQ hlead ha hΛ hdeg V h0 v₀ _ μ' h δ hδ) =
      dotElt Q a c (blockSucc_eq RD Λ c (blockSucc_wblk h0 c ν L h hδ)) •
        vgen hQ hlead ha hΛ hdeg V h0 v₀ _ μ' h δ hδ := by
  rw [vgen]
  refine (blockι_blockSumMap_apply (blockSucc RD Λ c h.2)
    (R := fun δ : WeightBlocks RD Λ μ' => CycKLR k Q a δ.1)
    (fun _ _ hβ => dot.{u, v, w} Q a c (blockSucc_eq RD Λ c hβ)) _ _ _).trans ?_
  erw [dot_app_unitGen, map_smul]
  rfl

omit [DecidableEq I] in
theorem map_fst_wswap_zero (c d : I) (ν₁ ν₂ : X) (L : List (I × X)) {β : Multiset I}
    (hβ : β = ↑(((c, ν₁) :: (d, ν₂) :: L).map Prod.fst)) :
    β = ↑((wswap RD 0 ((c, ν₁) :: (d, ν₂) :: L)).map Prod.fst) := by
  rw [hβ]
  exact Multiset.coe_eq_coe.2 (List.Perm.swap _ _ _).symm

/-- **The crossing of the last two letters acts on the generator by the crossing of the last
two strands**, with the sign `-1` for equal letters (`signedCross`). -/
theorem vgen_cross (c d : I) (ν₁ ν₂ : X) (L : List (I × X)) {μ' : X}
    (h : wValid RD μ ((c, ν₁) :: (d, ν₂) :: L) μ') {δ : WeightBlocks RD Λ μ'}
    (hδ : δ.1 = ↑(((c, ν₁) :: (d, ν₂) :: L).map Prod.fst)) :
    ((RouqFamily.wcross (S) μ 0 _ μ' h).hom.app V δ).hom
        (vgen hQ hlead ha hΛ hdeg V h0 v₀ _ μ' h δ hδ) =
      ((if c = d then -1 else 1 : k) • crossElt Q a (γ := (wblk h0 L ν₂ h.1.1).1) (δ := δ.1)) •
        vgen hQ hlead ha hΛ hdeg V h0 v₀ _ μ' (wValid_wswap 0 _ h) δ
          (map_fst_wswap_zero c d ν₁ ν₂ L hδ) := by
  have h4 : ν₂ + RD.iX c + RD.iX d = μ' := by rw [← h.2, ← h.1.2, add_right_comm]
  have hq : blockSucc RD Λ d h.1.2 (wblk h0 L ν₂ h.1.1) = wblk h0 ((d, ν₂) :: L) ν₁ h.1 :=
    blockSucc_wblk h0 d ν₂ L h.1 rfl
  have hp := blockSucc_wblk h0 c ν₁ ((d, ν₂) :: L) h hδ
  have hp' : blockSucc RD Λ d h4 (blockSucc RD Λ c rfl (wblk h0 L ν₂ h.1.1)) = δ :=
    Subtype.ext (by
      rw [blockSucc_val, blockSucc_val, hδ]
      simp only [wblk, List.map_cons, ← Multiset.cons_coe, ← Multiset.singleton_add]
      exact add_left_comm _ _ _)
  have key := congrArg (fun f => ModuleCat.Hom.hom f
      (Ind.tmul (unitGen (lastEmb Q a c (blockSucc_eq RD Λ c hp)))
        (Ind.tmul (unitGen (lastEmb Q a d (blockSucc_eq RD Λ d hq)))
        (vgen hQ hlead ha hΛ hdeg V h0 v₀ L ν₂ h.1.1 (wblk h0 L ν₂ h.1.1) rfl))))
    (gen₂_globalCross Q a RD Λ c d h.1.2 h.2 rfl h4
      ((RouqFamily.wcell (S) μ L ν₂ h.1.1).obj.obj V) (wblk h0 L ν₂ h.1.1) hq hp rfl hp')
  erw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  rw [vgen, vgen_cons hQ hlead ha hΛ hdeg d ν₂ L h.1 rfl (wblk h0 L ν₂ h.1.1) hq rfl]
  erw [← ind_map_tmul]
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  erw [vgen, vgen_cons hQ hlead ha hΛ hdeg c ν₂ L (wValid_wswap 0 _ h).1 rfl (wblk h0 L ν₂ h.1.1) rfl rfl]
  erw [← ind_map_tmul, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [signedCross_app_unitGen, map_smul]
  rfl

/-! ### Dots and crossings of weighted words on the generator -/

/-- The unit of the last-strand inclusion fixes the generator. -/
theorem lastEmb_one_smul_vgen (c : I) (ν : X) (L : List (I × X)) {μ' : X}
    (h : wValid RD μ ((c, ν) :: L) μ') {δ : WeightBlocks RD Λ μ'}
    (hδ : δ.1 = ↑(((c, ν) :: L).map Prod.fst)) {β : Multiset I} (hβ : β = ↑(L.map Prod.fst))
    (hc : {c} + β = δ.1) :
    lastEmb Q a c hc 1 • vgen hQ hlead ha hΛ hdeg V h0 v₀ _ μ' h δ hδ =
      vgen hQ hlead ha hΛ hdeg V h0 v₀ _ μ' h δ hδ := by
  obtain rfl : β = (wblk h0 L ν h.1).1 := hβ
  rw [vgen]
  erw [← map_smul, smul_tmul_unitGen, one_smul]
  rfl

/-- Transport along an equality of weighted words preserves the generator. -/
theorem vgen_eqToHom {L L' : List (I × X)} (e : L = L') {μ' : X} (h : wValid RD μ L μ')
    (h' : wValid RD μ L' μ') {δ : WeightBlocks RD Λ μ'} (hδ : δ.1 = ↑(L.map Prod.fst))
    (hδ' : δ.1 = ↑(L'.map Prod.fst)) :
    ((eqToHom (RouqFamily.wcell_congr (S) μ e h h')).hom.app V δ).hom
        (vgen hQ hlead ha hΛ hdeg V h0 v₀ L μ' h δ hδ) =
      vgen hQ hlead ha hΛ hdeg V h0 v₀ L' μ' h' δ hδ' := by
  subst e
  rfl

omit [DecidableEq I] [AddCommGroup X] in
theorem length_lt_card {L : List (I × X)} {β : Multiset I} (hβ : β = ↑(L.map Prod.fst))
    {n : ℕ} (hn : n < L.length) : n < Multiset.card β := by
  rw [hβ, Multiset.coe_card, List.length_map]; exact hn

/-- **The dot on the `a`-th letter acts on the generator by the dot on the strand
`|L| - 1 - a`.** -/
theorem vgen_wdot : ∀ (b : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ')
    (δ : WeightBlocks RD Λ μ') (hδ : δ.1 = ↑(L.map Prod.fst)) (hb : b < L.length),
    ((RouqFamily.wdot (S) μ b L μ' h).hom.app V δ).hom
        (vgen hQ hlead ha hΛ hdeg V h0 v₀ L μ' h δ hδ) =
      CycKLR.mk k Q a δ.1 (x ⟨L.length - 1 - b, length_lt_card hδ (by omega)⟩) •
        vgen hQ hlead ha hΛ hdeg V h0 v₀ L μ' h δ hδ
  | 0, (c, ν) :: L, μ', h, δ, hδ, _ => by
    refine (vgen_dot hQ hlead ha hΛ hdeg V h0 v₀ c ν L h hδ).trans ?_
    rw [dotElt]
    congr 3
    simp [wblk]
  | b + 1, (c, ν) :: L, μ', h, δ, hδ, hb => by
    refine (vgen_whiskerRight hQ hlead ha hΛ hdeg V h0 v₀ c ν L L h h _ hδ hδ rfl _
      (vgen_wdot b L ν h.1 (wblk h0 L ν h.1) rfl (by simp at hb; omega))).trans ?_
    rw [lastEmb_mk, ((isLeftBlock_lastIncl (Q := Q) c _).x_eq _), map_mul, ← lastEmb_mk,
      map_one, mul_smul]
    refine (congrArg (fun y => CycKLR.mk k Q a δ.1 (x _) • y) (lastEmb_one_smul_vgen hQ hlead ha
      hΛ hdeg V h0 v₀ c ν L h hδ rfl _)).trans ?_
    congr 3
    simp only [List.length_cons, Fin.mk.injEq]
    omega

/-- **The crossing of the letters `j`, `j + 1` acts on the generator by the crossing of the
strands `|L| - 2 - j`, `|L| - 1 - j`**, with the sign `-1` for equal letters. -/
theorem vgen_wcross : ∀ (j : ℕ) (L : List (I × X)) (μ' : X) (h : wValid RD μ L μ')
    (δ : WeightBlocks RD Λ μ') (hδ : δ.1 = ↑(L.map Prod.fst)), j + 1 < L.length →
    ((RouqFamily.wcross (S) μ j L μ' h).hom.app V δ).hom
        (vgen hQ hlead ha hΛ hdeg V h0 v₀ L μ' h δ hδ) =
      (lsgn k j (L.map Prod.fst) • CycKLR.mk k Q a δ.1 (ψ (L.length - 2 - j))) •
        vgen hQ hlead ha hΛ hdeg V h0 v₀ (wswap RD j L) μ' (wValid_wswap j L h) δ
          (map_fst_wswap hδ)
  | 0, (c, ν₁) :: (d, ν₂) :: L, μ', h, δ, hδ, _ => by
    refine (vgen_cross hQ hlead ha hΛ hdeg V h0 v₀ c d ν₁ ν₂ L h hδ).trans ?_
    congr 2
    · simp [lsgn]
    · simp [crossElt, wblk]
  | j + 1, (c, ν) :: L, μ', h, δ, hδ, hj => by
    have h' : wValid RD μ ((c, ν) :: wswap RD j L) μ' := ⟨wValid_wswap j L h.1, h.2⟩
    have hδ' : δ.1 = ↑(((c, ν) :: wswap RD j L).map Prod.fst) := map_fst_wswap (j := j + 1) hδ
    refine (vgen_whiskerRight hQ hlead ha hΛ hdeg V h0 v₀ c ν L (wswap RD j L) h
      h' _ hδ hδ' (map_fst_wswap rfl) _
      (vgen_wcross j L ν h.1 (wblk h0 L ν h.1) rfl (by simp at hj; omega))).trans ?_
    have hl : (wblk h0 L ν h.1).1 = ↑(L.map Prod.fst) := rfl
    rw [lastEmb_smul, lastEmb_mk, (isLeftBlock_lastIncl (Q := Q) c _).ψ_eq _
      (by rw [hl, Multiset.coe_card, List.length_map]; simp at hj; omega), map_mul, ← lastEmb_mk,
      map_one, ← smul_mul_assoc, mul_smul]
    refine (congrArg (fun y => (lsgn k j (L.map Prod.fst) • CycKLR.mk k Q a δ.1
      (ψ (L.length - 2 - j))) • y) (lastEmb_one_smul_vgen hQ hlead ha hΛ hdeg V h0 v₀ c ν
        (wswap RD j L) h' hδ' (map_fst_wswap rfl) _)).trans ?_
    have hn : L.length - 2 - j = ((c, ν) :: L).length - 2 - (j + 1) := by
      simp only [List.length_cons]; omega
    have hs : lsgn k j (L.map Prod.fst) • CycKLR.mk k Q a δ.1 (ψ (L.length - 2 - j)) =
        lsgn k (j + 1) (((c, ν) :: L).map Prod.fst) •
          CycKLR.mk k Q a δ.1 (ψ (((c, ν) :: L).length - 2 - (j + 1))) := by
      rw [hn]; rfl
    exact congrArg (· • _) hs

/-! ### Words of sequences -/

variable {ν : Multiset I}

omit [DecidableEq I] in
include h0 in
theorem blockWeight_wtop : blockWeight RD Λ ν = wtop RD μ ν := by
  rw [wtop, ← h0]
  simp only [blockWeight, Multiset.map_zero, Multiset.sum_zero, zero_sub]
  abel

/-- The block `R^Λ(ν)` at the top of the words of weight `ν`. -/
abbrev topBlk : WeightBlocks RD Λ (wtop RD μ ν) := ⟨ν, blockWeight_wtop h0⟩

omit [DecidableEq I] in
theorem topBlk_eq (t : Seq ν) : (topBlk h0 (ν := ν)).1 = ↑((wordL RD μ t).map Prod.fst) := by
  rw [map_fst_canon, Diagram.word, ← Fin.univ_val_map, t.2]

omit [DecidableEq I] in
theorem wseq_wordL (t : Seq ν) : wseq (wordL RD μ t) (topBlk_eq h0 t) = t.rev := by
  apply Subtype.ext
  funext x
  simp only [wseq, map_fst_canon, Diagram.word, List.get_eq_getElem, Fin.val_cast,
    List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
  exact (congrArg t.1 (Fin.ext (by change Multiset.card ν - 1 - x.1 = Multiset.card ν - (x.1 + 1); omega))).trans (Seq.rev_apply t x).symm

/-- The vacuum module `V`, viewed as an object of the weight-`μ` category of the cyclotomic
family. -/
def familyObj : ((S).obj μ).carrier := V

/-- **The generator of the word of `t` applied to the vacuum**, an element of the
`R^Λ(ν)`-module `E_t 𝕍`. -/
def wgen (t : Seq ν) :
    ((RouqFamily.wordCell (S) μ t).obj.obj (familyObj hQ hlead ha hΛ hdeg V) (topBlk h0) : Type _) :=
  vgen hQ hlead ha hΛ hdeg V h0 v₀ _ _ (wValid_wordL μ t) _ (topBlk_eq h0 t)

/-- The coordinate of the word of `t` applied to the vacuum. -/
def wcoord (t : Seq ν) :
    ((RouqFamily.wordCell (S) μ t).obj.obj (familyObj hQ hlead ha hΛ hdeg V) (topBlk h0) : Type _) →ₗ[CycKLR k Q a (topBlk h0 (ν := ν)).1]
      CycKLR k Q a (topBlk h0 (ν := ν)).1 :=
  vcoord hQ hlead ha hΛ hdeg V h0 Ψ₀ _ _ (wValid_wordL μ t) _ (topBlk_eq h0 t)

variable {Ψ₀} in
theorem wcoord_wgen (hΨ₀ : Ψ₀ v₀ = 1) (t : Seq ν) :
    wcoord hQ hlead ha hΛ hdeg V h0 Ψ₀ t (wgen hQ hlead ha hΛ hdeg V h0 v₀ t) =
      CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (e t.rev) := by
  exact (vcoord_vgen hQ hlead ha hΛ hdeg V h0 v₀ hΨ₀ _ _ (wValid_wordL μ t) _
    (topBlk_eq h0 t)).trans (by rw [wseq_wordL])

theorem e_smul_wgen (t : Seq ν) :
    CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (e t.rev) • wgen hQ hlead ha hΛ hdeg V h0 v₀ t =
      wgen hQ hlead ha hΛ hdeg V h0 v₀ t := by
  have := e_smul_vgen hQ hlead ha hΛ hdeg V h0 v₀ _ _ (wValid_wordL μ t) _ (topBlk_eq h0 t)
  rwa [wseq_wordL] at this

theorem comp_app_apply {μ' : X} {F G H : (S).obj μ ⟶ (S).obj μ'}
    (f : F ⟶ G) (g : G ⟶ H) (W : ((S).obj μ).carrier) (δ : WeightBlocks RD Λ μ')
    (y : F.obj.obj W δ) :
    ((f ≫ g).hom.app W δ).hom y = (g.hom.app W δ).hom ((f.hom.app W δ).hom y) := rfl

/-- The dot on the `b`-th strand of the word of `t` acts on the generator by `x_{rev b}`. -/
theorem wordDot_wgen (t : Seq ν) (b : Fin (Multiset.card ν)) :
    ((RouqFamily.wordDot (S) μ t b).hom.app (familyObj hQ hlead ha hΛ hdeg V) (topBlk h0)).hom
        (wgen hQ hlead ha hΛ hdeg V h0 v₀ t) =
      CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (x b.rev) • wgen hQ hlead ha hΛ hdeg V h0 v₀ t := by
  have hl : (wordL RD μ t).length = Multiset.card ν := by simp
  refine (vgen_wdot hQ hlead ha hΛ hdeg V h0 v₀ b _ _ (wValid_wordL μ t) _ (topBlk_eq h0 t)
    (by omega)).trans ?_
  congr 3
  ext
  change (wordL RD μ t).length - 1 - b.1 = Multiset.card ν - (b.1 + 1)
  omega

/-- The crossing of the strands `j`, `j + 1` of the word of `t` acts on the generator by
`± ψ_{m - 2 - j}`. -/
theorem wordCross_wgen (t : Seq ν) {j : ℕ} (hj : j + 1 < Multiset.card ν) :
    ((RouqFamily.wordCross (S) μ t j).hom.app (familyObj hQ hlead ha hΛ hdeg V) (topBlk h0)).hom
        (wgen hQ hlead ha hΛ hdeg V h0 v₀ t) =
      (lsgn k j (Diagram.word t) • CycKLR.mk k Q a (topBlk h0 (ν := ν)).1
        (ψ (Multiset.card ν - 2 - j))) • wgen hQ hlead ha hΛ hdeg V h0 v₀ (TypeA.sadj _ j • t) := by
  have hl : (wordL RD μ t).length = Multiset.card ν := by simp
  rw [RouqFamily.wordCross_def _ _ _ hj, RouqFamily.wcrossTo]
  erw [comp_app_apply]
  erw [vgen_wcross hQ hlead ha hΛ hdeg V h0 v₀ j _ _ (wValid_wordL μ t) _ (topBlk_eq h0 t)
    (by omega), map_smul, vgen_eqToHom]
  rw [map_fst_canon, hl]
  rfl
  exact wswap_wordL (RD := RD) μ t hj


theorem add_app_apply {μ' : X} {F G : (S).obj μ ⟶ (S).obj μ'}
    (f g : F ⟶ G) (W : ((S).obj μ).carrier) (δ : WeightBlocks RD Λ μ')
    (y : F.obj.obj W δ) :
    ((f + g).hom.app W δ).hom y = (f.hom.app W δ).hom y + (g.hom.app W δ).hom y := rfl

theorem zero_app_apply {μ' : X} {F G : (S).obj μ ⟶ (S).obj μ'}
    (W : ((S).obj μ).carrier) (δ : WeightBlocks RD Λ μ')
    (y : F.obj.obj W δ) :
    (((0 : F ⟶ G)).hom.app W δ).hom y = 0 := rfl

theorem smul_app_apply {μ' : X} {F G : (S).obj μ ⟶ (S).obj μ'}
    (c : k) (f : F ⟶ G) (W : ((S).obj μ).carrier) (δ : WeightBlocks RD Λ μ')
    (y : F.obj.obj W δ) :
    ((c • f).hom.app W δ).hom y = algebraMap k (CycKLR k Q a δ.1) c • (f.hom.app W δ).hom y := rfl

theorem id_app_apply {μ' : X} {F : (S).obj μ ⟶ (S).obj μ'}
    (W : ((S).obj μ).carrier) (δ : WeightBlocks RD Λ μ')
    (y : F.obj.obj W δ) :
    (((𝟙 F : F ⟶ F)).hom.app W δ).hom y = y := rfl


theorem sum_app_apply {μ' : X} {F G : (S).obj μ ⟶ (S).obj μ'}
    {ι : Type*} (T : Finset ι) (f : ι → (F ⟶ G)) (W : ((S).obj μ).carrier)
    (δ : WeightBlocks RD Λ μ') (y : F.obj.obj W δ) :
    ((∑ i ∈ T, f i).hom.app W δ).hom y = ∑ i ∈ T, ((f i).hom.app W δ).hom y :=
  map_sum (AddMonoidHom.mk' (fun g : F ⟶ G => (g.hom.app W δ).hom y) fun _ _ => rfl) f T

theorem lsgn_word (t : Seq ν) {j : ℕ} (hj : j + 1 < Multiset.card ν) :
    lsgn k j (Diagram.word t) =
      if t.lbl ⟨j, by omega⟩ = t.lbl ⟨j + 1, hj⟩ then -1 else 1 := by
  simp [lsgn, Diagram.word, hj, show j < Multiset.card ν by omega]

omit [DecidableEq I] in
/-- An entry of a matrix of morphisms is the corresponding entry of its product with the
diagonal unit at the source. -/
theorem entry_eq_mul_single {ι : Type*} [Fintype ι] [DecidableEq ι] {D : Type*} [Category D]
    [Preadditive D] {Z : ι → D} (f : Diagram.MatEnd Z) (t s : ι) :
    f t s = (f * Diagram.MatEnd.single t t (𝟙 (Z t))) t s := by
  rw [Diagram.MatEnd.mul_apply, Finset.sum_eq_single t, Diagram.MatEnd.single_apply_self,
    Category.id_comp]
  · intro u _ hu
    rw [Diagram.MatEnd.single_apply_of_ne _ (fun h => hu h.2), Limits.zero_comp]
  · simp

theorem smul_wgen_congr {z z' : CycKLR k Q a (topBlk h0 (ν := ν)).1} (hz : z = z') (s : Seq ν) :
    z • wgen hQ hlead ha hΛ hdeg V h0 v₀ s = z' • wgen hQ hlead ha hΛ hdeg V h0 v₀ s :=
  hz ▸ rfl

theorem klrAct_wgen (r : KLRAlgebra k Q ν) (t s : Seq ν) :
    (((RouqFamily.klrAct (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg) μ r) t s).hom.app (familyObj hQ hlead ha hΛ hdeg V)
        (topBlk h0)).hom (wgen hQ hlead ha hΛ hdeg V h0 v₀ t) =
      CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ (e s * r * e t))) •
        wgen hQ hlead ha hΛ hdeg V h0 v₀ s := by
  induction r using KLRAlgebra.IsLeftBlock.induction generalizing t s with
  | scalar c =>
    have hc : CycKLR.mk k Q a (topBlk h0 (ν := ν)).1
        (hflip (sigma hQ (e s * algebraMap k (KLRAlgebra k Q ν) c * e t))) =
        if t = s then algebraMap k _ c * CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (e t.rev)
        else 0 := by
      rw [← Algebra.commutes, mul_assoc, e_mul_e]
      by_cases h : s = t
      · subst h; simpa [hflip_mul] using (Algebra.commutes c _).symm
      · simp [h, Ne.symm h]
    refine Eq.trans ?_ (smul_wgen_congr hQ hlead ha hΛ hdeg V h0 v₀ hc.symm s)
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Diagram.MatEnd.smul_apply]
    by_cases h : t = s
    · subst h
      rw [Diagram.MatEnd.one_apply_self, ite_eq_left rfl, mul_smul, e_smul_wgen]
      rfl
    · rw [Diagram.MatEnd.one_apply_of_ne h, smul_zero, ite_eq_right h, zero_smul]
      rfl
  | he u =>
    have hc : (e s * e u * e t : KLRAlgebra k Q ν) = if t = u ∧ s = u then e t else 0 := by
      by_cases h1 : s = u
      · subst h1
        by_cases h2 : t = s
        · subst h2; simp [e_mul_e]
        · simp [e_mul_e, h2, Ne.symm h2]
      · simp [e_mul_e, h1]
    refine Eq.trans ?_ (smul_wgen_congr hQ hlead ha hΛ hdeg V h0 v₀
      (congrArg (fun z => CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ z))) hc).symm s)
    rw [RouqFamily.klrAct_e, RouqFamily.wordE_eq]
    by_cases h : t = u ∧ s = u
    · obtain ⟨rfl, rfl⟩ := h
      rw [Diagram.MatEnd.single_apply_self, ite_eq_left ⟨rfl, rfl⟩, sigma_e, hflip_e, e_smul_wgen]
      rfl
    · rw [Diagram.MatEnd.single_apply_of_ne _ h, ite_eq_right h, map_zero, hflip_zero, map_zero,
        zero_smul]
      rfl
  | hx b =>
    have hc : CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ (e s * x b * e t))) =
        if t = s then CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (x b.rev) *
          CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (e t.rev) else 0 := by
      rw [mul_assoc, x_mul_e, ← mul_assoc, e_mul_e]
      by_cases h : s = t
      · subst h; simp [hflip_mul]
      · simp [h, Ne.symm h]
    refine Eq.trans ?_ (smul_wgen_congr hQ hlead ha hΛ hdeg V h0 v₀ hc.symm s)
    rw [RouqFamily.klrAct_dot, entry_eq_mul_single (RouqFamily.wordX (S) μ b) t s, RouqFamily.wordX_mul_single, Category.id_comp]
    by_cases h : t = s
    · subst h
      rw [Diagram.MatEnd.single_apply_self, ite_eq_left rfl, mul_smul, e_smul_wgen]
      exact wordDot_wgen hQ hlead ha hΛ hdeg V h0 v₀ t b
    · rw [Diagram.MatEnd.single_apply_of_ne _ (fun h' => h h'.2.symm), ite_eq_right h, zero_smul]
      rfl
  | hψ j =>
    by_cases hj : j + 1 < Multiset.card ν
    · have hc : CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ (e s * ψ j * e t))) =
          if s = TypeA.sadj (Multiset.card ν) j • t then
            (lsgn k j (Diagram.word t) • CycKLR.mk k Q a (topBlk h0 (ν := ν)).1
              (ψ (Multiset.card ν - 2 - j))) * CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (e s.rev)
          else 0 := by
        rw [e_mul_ψ, mul_assoc, e_mul_e]
        by_cases h : s = TypeA.sadj (Multiset.card ν) j • t
        · subst h
          rw [sadj_smul_smul, ite_eq_left rfl, ite_eq_left rfl, sigma_ψ_mul_e hQ hj, hflip_smul, hflip_mul,
            hflip_e, hflip_ψ]
          have hψe := ψ_rev_mul_e_rev (k := k) (Q := Q) hj (TypeA.sadj (Multiset.card ν) j • t)
          rw [sadj_smul_smul] at hψe
          rw [← hψe, map_smul, map_mul, smul_mul_assoc,
            lsgn_word t hj]
        · have h' : ¬ TypeA.sadj (Multiset.card ν) j • s = t := fun h' => h (by
            rw [← h', sadj_smul_smul])
          rw [ite_eq_right h', ite_eq_right h, mul_zero, map_zero, hflip_zero, map_zero]
      refine Eq.trans ?_ (smul_wgen_congr hQ hlead ha hΛ hdeg V h0 v₀ hc.symm s)
      rw [RouqFamily.klrAct_cross, entry_eq_mul_single (RouqFamily.wordΨ (S) μ j) t s, RouqFamily.wordΨ_mul_single,
        Category.id_comp]
      by_cases h : s = TypeA.sadj (Multiset.card ν) j • t
      · subst h
        rw [Diagram.MatEnd.single_apply_self, ite_eq_left rfl, mul_smul, e_smul_wgen]
        exact wordCross_wgen hQ hlead ha hΛ hdeg V h0 v₀ t hj
      · rw [Diagram.MatEnd.single_apply_of_ne _ (fun h' => h h'.2), ite_eq_right h, zero_smul]
        rfl
    · rw [RouqFamily.klrAct_cross, RouqFamily.wordΨ_of_le (by exact not_lt.mp hj), map_mul,
        map_mul, sigma_ψ_of_le hQ (by exact not_lt.mp hj), mul_zero, zero_mul, hflip_zero, map_zero, zero_smul]
      rfl
  | add r r' hr hr' =>
    rw [map_add, Diagram.MatEnd.add_apply]
    erw [add_app_apply]
    rw [hr, hr']
    refine Eq.trans ?_ (smul_wgen_congr hQ hlead ha hΛ hdeg V h0 v₀
      (congrArg (fun z => CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ z)))
        (show e s * (r + r') * e t = e s * r * e t + e s * r' * e t by noncomm_ring)).symm s)
    simp only [map_add, hflip_add, add_smul]
  | mul r r' hr hr' =>
    rw [map_mul, Diagram.MatEnd.mul_apply]
    erw [sum_app_apply]
    have key : ∀ u, (((((RouqFamily.klrAct (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg) μ r')
        t u ≫ (RouqFamily.klrAct (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg) μ r) u s)).hom.app (familyObj hQ hlead ha hΛ hdeg V)
          (topBlk h0)).hom (wgen hQ hlead ha hΛ hdeg V h0 v₀ t)) =
        (CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ (e u * r' * e t))) *
          CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ (e s * r * e u)))) •
          wgen hQ hlead ha hΛ hdeg V h0 v₀ s := by
      intro u
      erw [comp_app_apply, hr', map_smul, hr]
      rw [mul_smul]
    have hsum : (e s * (r * r') * e t : KLRAlgebra k Q ν) =
        ∑ u, (e s * r * e u) * (e u * r' * e t) := by
      have h1 : ∀ u, (e s * r * e u) * (e u * r' * e t : KLRAlgebra k Q ν) =
          e s * r * e u * r' * e t := fun u => by
        rw [show (e s * r * e u) * (e u * r' * e t : KLRAlgebra k Q ν) =
          e s * r * (e u * e u) * r' * e t by noncomm_ring, e_mul_self]
      simp_rw [h1]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, sum_e, mul_one, ← mul_assoc]
    refine (Finset.sum_congr rfl fun u _ => key u).trans ?_
    rw [← Finset.sum_smul]
    refine smul_wgen_congr hQ hlead ha hΛ hdeg V h0 v₀ ?_ s
    rw [hsum, map_sum, hflip_sum, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_mul (sigma hQ) (e s * r * e u) (e u * r' * e t), hflip_mul]
    exact (map_mul _ _ _).symm


variable {Ψ₀} in
/-- The coordinate of an entry of `klrAct r` on the generator of the word of `t`: the coefficient
`hflip (σ (e(s) r e(t)))`, read in `R^Λ(ν)`. -/
theorem wcoord_klrAct_wgen (hΨ₀ : Ψ₀ v₀ = 1) (r : KLRAlgebra k Q ν) (t s : Seq ν) :
    wcoord hQ hlead ha hΛ hdeg V h0 Ψ₀ s
        ((((RouqFamily.klrAct (cyclotomicFamily_upKLR hQ hlead ha RD Λ hΛ hdeg) μ r) t s).hom.app
          (familyObj hQ hlead ha hΛ hdeg V) (topBlk h0)).hom (wgen hQ hlead ha hΛ hdeg V h0 v₀ t)) =
      CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ (e s * r * e t))) := by
  rw [klrAct_wgen, map_smul, wcoord_wgen hQ hlead ha hΛ hdeg V h0 v₀ hΨ₀, smul_eq_mul, ← map_mul]
  congr 1
  rw [map_mul, map_mul, sigma_e, hflip_mul, hflip_mul, hflip_e]
  simp only [mul_assoc, e_mul_self]

variable {Ψ₀} in
/-- **The cyclotomic quotient through the vacuum.** If `r ∈ R(ν)` acts by zero on the words of
weight `ν` at the vacuum, then `hflip (σ r)` vanishes in `R^Λ(ν)`. -/
theorem mk_hflip_sigma_eq_zero_of_klrAct (hΨ₀ : Ψ₀ v₀ = 1) (r : KLRAlgebra k Q ν)
    (hr : RouqFamily.klrAct (cyclotomicFamily_upKLR.{u, v, w} hQ hlead ha RD Λ hΛ hdeg) μ r = 0) :
    CycKLR.mk k Q a ν (hflip (sigma hQ r)) = 0 := by
  have hst : ∀ t s : Seq ν,
      CycKLR.mk k Q a (topBlk h0 (ν := ν)).1 (hflip (sigma hQ (e s * r * e t))) = 0 := by
    intro t s
    refine (wcoord_klrAct_wgen hQ hlead ha hΛ hdeg V h0 v₀ hΨ₀ r t s).symm.trans ?_
    have key : ∀ f : RouqFamily.WordEnd (S) μ ν, f = 0 →
        wcoord hQ hlead ha hΛ hdeg V h0 Ψ₀ s (((f t s).hom.app (familyObj hQ hlead ha hΛ hdeg V)
          (topBlk h0)).hom (wgen hQ hlead ha hΛ hdeg V h0 v₀ t)) = 0 := by
      rintro f rfl
      exact map_zero _
    exact key _ hr
  have hsum : r = ∑ s : Seq ν, ∑ t : Seq ν, e s * r * e t := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sum_e, one_mul, mul_one]
  rw [hsum, map_sum, hflip_sum, map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [map_sum, hflip_sum, map_sum]
  exact Finset.sum_eq_zero fun t _ => hst t s


/-- The regular object at the weight `-Λ` of the empty block: every block `β` carries the
regular module `R^Λ(β)`. On the block `β = ∅` it is the vacuum `R^Λ(∅) = k`. -/
def regularObj : weightSpace.{u, v, w} Q a RD Λ (blockWeight RD Λ 0) :=
  fun β => ModuleCat.of (CycKLR k Q a β.1) (ULift.{w} (CycKLR k Q a β.1))

/-- **The cyclotomic quotient through the 2-representation.** If `r ∈ R(ν)` acts by zero on the
words of weight `ν` at the weight `-Λ` of the cyclotomic family, then `hflip (σ r)` vanishes in
`R^Λ(ν)`. -/
theorem mk_hflip_sigma_eq_zero (r : KLRAlgebra k Q ν)
    (hr : RouqFamily.klrAct (cyclotomicFamily_upKLR.{u, v, w} hQ hlead ha RD Λ hΛ hdeg)
      (blockWeight RD Λ 0) r = 0) :
    CycKLR.mk k Q a ν (hflip (sigma hQ r)) = 0 :=
  mk_hflip_sigma_eq_zero_of_klrAct hQ hlead ha hΛ hdeg (regularObj.{u, v, w} (Q := Q) (a := a) (RD := RD) (Λ := Λ)) rfl
    (ULift.up 1) (Ψ₀ := (ULift.moduleEquiv : ULift.{w} (CycKLR k Q a 0) ≃ₗ[CycKLR k Q a 0] _).toLinearMap)
    rfl r hr

end

end Categorification.KLR.CyclotomicAction
