/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapSliding
import Categorification.WeightedKLR.Rigidity.CupCapModelMap
import Categorification.WeightedKLR.RedStrands.StendhalGrading

/-!
# Degrees of the diagrams in the relations of `K̃^{λ⁺}_λ`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3,
Definitions 7.14 and 7.15, and the grading of Definitions 4.4–4.7. These are the degree
computations behind the grading of the cap bimodule (`Rigidity/CupCapGrading.lean`): the three
algebras `T̃^λ` (above the cap), `T̃^{λ⁺}` (below it) and `T̃^{(μ, μ*)}` (at the maximum) are
graded by Webster's degrees (`stendhalGradingDatum`) for one grading datum `G` of the black
strands and the symmetrizer `d`, so that a black/red crossing with the red label `λ_r` has
degree `d_i λ_r^i`.

* The quotient maps of the KLR algebras onto the three Stendhal algebras, and the placement
  `ι_{s,n}` of the diagrams at the maximum below the cap, preserve degrees
  (`topMap_mem_grade`, `insertMap_mem_grade`).
* A dot or a crossing of the top that passes below the cap keeps its degree (`dx_dotPos`,
  `dψ_crossPos`).
* A black strand of colour `i` crossing all the strands at the maximum (the two legs `μ, μ*` and
  the black strands of weight `ν₀`) has degree `d_i (μ^i + μ*^i) + ∑_{i' ∈ ν₀} deg ψ(i', i)`
  (`degW_underRight`, `degW_underLeft`). This vanishes in Webster's setting, where `ν₀` is the
  weight `μ - w₀μ = μ + μ*` of the strands at the maximum of `L_μ` (`CapBalanced`): this is what
  makes the relations (max1) and (max2) homogeneous. For the KL degrees
  `deg ψ(i', i) = -(α_{i'}, α_i)` and `d_i λ^i = (α_i, λ)`, `CapBalanced` says
  `(α_i, μ + μ* - ν₀) = 0` for all `i`.

All degrees are integers: Webster's gradings lie in `(1/D)ℤ` only because of the red/red
crossings, which do not occur in `K̃^{λ⁺}_λ` beyond those of `T̃`.
-/

noncomputable section

namespace Categorification.KLR.GradingDatum

open TypeA KL2

variable {I : Type*} {k : Type*} [CommRing k] {Q : I → I → MvPolynomial (Fin 2) k}
  (G : GradingDatum Q) {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- **The degree of a strand passing to the left under `N` strands**: `ψ_q ψ_{q+1} ⋯ ψ_{q+N-1}
1_i` takes the strand at the bottom position `q + N` to the top position `q`, crossing the
strands at `q, …, q + N - 1`. -/
theorem degW_range' (N : ℕ) : ∀ (q : ℕ) (h : q + N < m) (i : Seq ν),
    G.degW (List.range' q N) i =
      ∑ b : Fin N, G.degΨ (i.lbl ⟨q + b, by omega⟩) (i.lbl ⟨q + N, h⟩) := by
  induction N with
  | zero => intro q h i; simp [degW]
  | succ N ih =>
    intro q h i
    rw [List.range'_succ, degW, ih (q + 1) (by omega) i, G.dψ_of_lt (by omega),
      Fin.sum_univ_succ]
    have h1 := lbl_range'_smul (q := q + 1) (l := N) (by omega) i ⟨q, by omega⟩ ⟨q, by omega⟩
      (by simp only [rfun]; split_ifs <;> omega)
    have h2 := lbl_range'_smul (q := q + 1) (l := N) (by omega) i ⟨q + 1, by omega⟩
      ⟨q + (N + 1), h⟩ (by simp only [rfun]; split_ifs <;> omega)
    rw [h1, h2]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 2 <;> ext <;> simp <;> omega

/-- **The degree of a strand passing to the right under `N` strands**: `ψ_{q+N-1} ⋯ ψ_q 1_i`
takes the strand at the bottom position `q` to the top position `q + N`, crossing the strands
at `q + 1, …, q + N`. -/
theorem degW_range'_reverse (q : ℕ) : ∀ (N : ℕ) (h : q + N < m) (i : Seq ν),
    G.degW (List.range' q N).reverse i =
      ∑ b : Fin N, G.degΨ (i.lbl ⟨q, by omega⟩) (i.lbl ⟨q + 1 + b, by omega⟩) := by
  intro N
  induction N with
  | zero => intro h i; simp [degW]
  | succ N ih =>
    intro h i
    rw [List.range'_concat, List.reverse_append, List.reverse_singleton, List.singleton_append,
      degW, ih (by omega) i, G.dψ_of_lt (by omega), Fin.sum_univ_castSucc, add_comm]
    have h1 := lbl_range'_reverse_smul (q := q) (l := N) (by omega) i ⟨q + 1 * N, by omega⟩
      ⟨q, by omega⟩ (by simp only [lfun]; split_ifs <;> omega)
    have h2 := lbl_range'_reverse_smul (q := q) (l := N) (by omega) i ⟨q + 1 * N + 1, by omega⟩
      ⟨q + 1 + N, by omega⟩ (by simp only [lfun]; split_ifs <;> omega)
    rw [h1, h2]
    rfl

end Categorification.KLR.GradingDatum

namespace Categorification.KLR.Seq

variable {J : Type*} {μ : Multiset J}

/-- A sum over the positions of a loading is the sum over its weight. -/
theorem sum_lbl {M : Type*} [AddCommMonoid M] (t : Seq μ) (f : J → M) :
    ∑ b, f (t.lbl b) = (μ.map f).sum := by
  conv_rhs => rw [← t.2, Multiset.map_map]
  rfl

end Categorification.KLR.Seq

namespace Categorification.KLR.GradingDatum

open KLRAlgebra

variable {k : Type*} [CommRing k] {I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
  {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
  {ν₁ : Multiset I₁} {ν₂ : Multiset I₂} (R : SeqRelabel k Q₁ Q₂ ν₁ ν₂)
  (G₁ : GradingDatum Q₁) (G₂ : GradingDatum Q₂)

include R in
private theorem relabelHom_coaction
    (hx : ∀ a i, G₂.dx (Fin.cast R.card_eq a) (R.equiv i) = G₁.dx a i)
    (hψ : ∀ j i, G₂.dψ j (R.equiv i) = G₁.dψ j i) (z : KLRAlgebra k Q₁ ν₁) :
    G₂.coaction (relabelHom R z) =
      AddMonoidAlgebra.mapAlgHom ℤ (relabelHom R) (G₁.coaction z) := by
  induction z using klr_induction with
  | hr r => simp only [AlgHom.commutes]
  | hadd x y h₁ h₂ => simp only [map_add, h₁, h₂]
  | hmul x y h₁ h₂ => simp only [map_mul, h₁, h₂]
  | he s => simp only [relabelHom_e, coaction_e, AddMonoidAlgebra.mapAlgHom_single]
  | hx a =>
    simp only [relabelHom_x, coaction_x, map_sum, AddMonoidAlgebra.mapAlgHom_single, map_mul,
      relabelHom_e]
    exact (Fintype.sum_equiv R.equiv _ _ fun i => by rw [hx]).symm
  | hψ j =>
    simp only [relabelHom_ψ, coaction_ψ, map_sum, AddMonoidAlgebra.mapAlgHom_single, map_mul,
      relabelHom_e]
    exact (Fintype.sum_equiv R.equiv _ _ fun i => by rw [hψ]).symm

/-- A relabelling of the strands that matches the degrees of dots and crossings preserves
degrees. -/
theorem relabelHom_mem_grade
    (hx : ∀ a i, G₂.dx (Fin.cast R.card_eq a) (R.equiv i) = G₁.dx a i)
    (hψ : ∀ j i, G₂.dψ j (R.equiv i) = G₁.dψ j i) {n : ℤ} {z : KLRAlgebra k Q₁ ν₁}
    (hz : z ∈ G₁.grade ν₁ n) : relabelHom R z ∈ G₂.grade ν₂ n := by
  rw [mem_grade, relabelHom_coaction R G₁ G₂ hx hψ, G₁.mem_grade.mp hz,
    AddMonoidAlgebra.mapAlgHom_single]

end Categorification.KLR.GradingDatum

namespace Categorification.Stendhal

open KLR

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {Q : I → I → MvPolynomial (Fin 2) k}
  {Λ : Fin ℓ → I →₀ ℕ} (G : KLR.GradingDatum (stendhalQ Q Λ)) {ν : Multiset I}

/-- The quotient map of the KLR algebra onto `T̃^λ` preserves degrees. -/
theorem orderProjection_ofKLR_mem_stendhalGrade {n : ℤ}
    {y : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)}
    (hy : y ∈ G.grade (stendhalWeight ℓ ν) n) :
    orderProjection Q Λ ν (StendhalAlgebraAllOrders.ofKLR k Q Λ ν y) ∈ stendhalGrade G ν n := by
  change StendhalAlgebraAllOrders.ofKLR k Q Λ ν y *
    StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν ∈ allOrdersGrade G ν n
  have ha := Graded.mem_map_of_mem _ (StendhalAlgebraAllOrders.ofKLR k Q Λ ν).toLinearMap hy
  have hE : StendhalAlgebraAllOrders.redOrderedIdem k Q Λ ν ∈ allOrdersGrade G ν 0 :=
    Submodule.sum_mem _ fun i _ => Graded.mem_map_of_mem _ _ (G.e_mem_grade i)
  simpa using SetLike.mul_mem_graded (A := allOrdersGrade G ν) ha hE

end Categorification.Stendhal

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}
  (G : KLR.GradingDatum Q) (d : I → ℤ) (hd : ∀ i, G.degX i = 2 * d i)

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "M" => Multiset.card (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Gt" => stendhalGradingDatum Λ G d hd
local notation "Gb" => stendhalGradingDatum (plusLabels Λ Λc j hj) G d hd
local notation "Gc" => stendhalGradingDatum Λc G d hd

/-! ### The colours of `λ` and of the strands at the maximum inside `λ⁺` -/

section Colours

omit [DecidableEq I]

theorem degX_oldColour (a : I ⊕ Fin ℓ) : (Gb).degX (oldColour j hj a) = (Gt).degX a := by
  rcases a with a | a <;> rfl

theorem degΨ_oldColour (a b : I ⊕ Fin ℓ) :
    (Gb).degΨ (oldColour j hj a) (oldColour j hj b) = (Gt).degΨ a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [stendhalGradingDatum]

theorem degX_cupColour (a : I ⊕ Fin 2) :
    (Gb).degX (cupColour (ℓ := ℓ) j hj a) = (Gc).degX a := by
  rcases a with a | a <;> rfl

theorem degΨ_cupColour (a b : I ⊕ Fin 2) :
    (Gb).degΨ (cupColour j hj a) (cupColour j hj b) = (Gc).degΨ a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [stendhalGradingDatum]

end Colours

/-! ### The quotient maps and the diagrams at the maximum -/

theorem topMap_mem_grade {n : ℤ} {y : KLRAlgebra k (stendhalQ Q Λ) (stendhalWeight ℓ ν)}
    (hy : y ∈ (Gt).grade _ n) : topMap k Q Λ ν y ∈ stendhalGrade (Gt) ν n :=
  orderProjection_ofKLR_mem_stendhalGrade _ hy

theorem botMap_mem_grade {n : ℤ}
    {y : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))}
    (hy : y ∈ (Gb).grade _ n) : botMap k Q Λ Λc j hj ν ν₀ y ∈ stendhalGrade (Gb) (ν + ν₀) n :=
  orderProjection_ofKLR_mem_stendhalGrade _ hy

theorem cupMap_mem_grade {n : ℤ} {y : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)}
    (hy : y ∈ (Gc).grade _ n) : cupMap k Q Λc ν₀ y ∈ stendhalGrade (Gc) ν₀ n :=
  orderProjection_ofKLR_mem_stendhalGrade _ hy

omit [DecidableEq I] in
theorem dψ_cupRelabel (q : ℕ) (w : Seq (stendhalWeight 2 ν₀)) :
    (Gb).dψ q ((cupRelabel (j := j) (hj := hj) (ν₀ := ν₀) k Q Λ Λc).equiv w) = (Gc).dψ q w := by
  unfold GradingDatum.dψ
  by_cases hq : q + 1 < Multiset.card (stendhalWeight 2 ν₀)
  · have hq' : q + 1 < Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (ℓ := ℓ) j hj)) := by
      rwa [Multiset.card_map]
    simp only [hq, hq', ↓reduceDIte]
    change (Gb).degΨ (cupColour j hj _) (cupColour j hj _) = _
    rw [degΨ_cupColour]
    rfl
  · have hq' : ¬ q + 1 < Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (ℓ := ℓ) j hj)) := by
      rwa [Multiset.card_map]
    simp only [hq, hq', ↓reduceDIte]

/-- **`ι_{s,n}` preserves degrees**: a homogeneous diagram on the strands at the maximum, placed
below the cap, keeps its degree. -/
theorem insertMap_mem_grade (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m) {e : ℤ}
    {x : KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)} (hx : x ∈ (Gc).grade _ e) :
    insertMap (j := j) (hj := hj) Q Λ Λc s n hn x ∈ (Gb).grade _ e := by
  have h := GradingDatum.relabelHom_mem_grade
    (cupRelabel (j := j) (hj := hj) (ν₀ := ν₀) k Q Λ Λc) (Gc) (Gb)
    (fun a w => by
      change (Gb).degX (cupColour j hj _) = _
      rw [degX_cupColour]
      rfl)
    (fun q w => dψ_cupRelabel G d hd q w) hx
  exact (insertEmb s n hn).valHom_mem_grade (Gb) h

/-! ### Dots and crossings passing below the cap -/

omit [DecidableEq I] in
theorem insertSeq_lbl_of_val_old (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) (c : Fin M) (a : Fin m)
    (hc : c.val = if a.val < n then a.val else a.val + Multiset.card
      ((stendhalWeight 2 ν₀).map (cupColour (ℓ := ℓ) j hj))) :
    (insertSeq s n hn t).lbl c = oldColour j hj (s.lbl a) := by
  have h : c = Fin.cast (card_plus j hj ν ν₀).symm (insertPos _ _ n hn (.inl a)) :=
    Fin.ext (by rw [Fin.val_cast, insertPos_inl_val, hc])
  rw [h, insertSeq_lbl_old]

omit [DecidableEq I] in
theorem insertSeq_lbl_of_val_new (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) (c : Fin M)
    (b : Fin (Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (ℓ := ℓ) j hj))))
    (hc : c.val = n + b.val) : (insertSeq s n hn t).lbl c = t.lbl b := by
  have h : c = Fin.cast (card_plus j hj ν ν₀).symm (insertPos _ _ n hn (.inr b)) :=
    Fin.ext (by rw [Fin.val_cast, insertPos_inr_val, hc])
  rw [h, insertSeq_lbl_new]

omit [DecidableEq I] in
/-- A dot of the top keeps its degree below the cap. -/
theorem dx_dotPos (s : Seq (stendhalWeight ℓ ν)) (n : Fin (m + 1))
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) (a : Fin m) :
    (Gb).dx (dotPos (j := j) (hj := hj) (ν₀ := ν₀) n a)
        (insertSeq s n (Nat.lt_succ_iff.1 n.2) t) = (Gt).dx a s := by
  unfold GradingDatum.dx dotPos
  rw [insertSeq_lbl_old, degX_oldColour]

omit [DecidableEq I] in
/-- A crossing of the top on one side of the maximum keeps its degree below the cap. -/
theorem dψ_crossPos (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hn : n ≤ m)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) {p : ℕ} (hp : p + 1 < n ∨ n ≤ p) :
    (Gb).dψ (crossPos n N p) (insertSeq s n hn t) = (Gt).dψ p s := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hN : Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (ℓ := ℓ) j hj)) = N :=
    Multiset.card_map _ _
  unfold GradingDatum.dψ crossPos
  by_cases h : p + 1 < m
  · have h' : (if p < n then p else p + N) + 1 < M := by split_ifs <;> omega
    simp only [h, h', ↓reduceDIte]
    rw [insertSeq_lbl_of_val_old (j := j) (hj := hj) s hn t _ ⟨p, by omega⟩
        (by simp only [hN]),
      insertSeq_lbl_of_val_old (j := j) (hj := hj) s hn t _ ⟨p + 1, h⟩
        (by simp only [hN]; split_ifs <;> omega),
      degΨ_oldColour]
  · have h' : ¬ (if p < n then p else p + N) + 1 < M := by split_ifs <;> omega
    simp only [h, h', ↓reduceDIte]

/-! ### A black strand crossing the cap -/

variable (Λc ν₀) in
/-- **The balance condition at the maximum of the cap**: for every colour `i`, a black strand of
colour `i` crossing all strands at the maximum, in either direction, has degree zero. With the
KL degrees this says that the strands at the maximum have total weight `μ + μ*`; it holds for
Webster's `L_μ`, whose strands at the maximum have weight `μ - w₀μ` (§7.3, before
Definition 7.15). It makes the relations (max1) and (max2) homogeneous. -/
def CapBalanced : Prop :=
  ∀ i, (ν₀.map fun i' => G.degΨ i' i).sum + d i * (Λc 0 i + Λc 1 i) = 0 ∧
    (ν₀.map fun i' => G.degΨ i i').sum + d i * (Λc 0 i + Λc 1 i) = 0

omit [DecidableEq I] in
theorem sum_degΨ_cup_left (t : Seq ((stendhalWeight 2 ν₀).map (cupColour (ℓ := ℓ) j hj)))
    (i : I) : ∑ b, (Gb).degΨ (t.lbl b) (.inl i) =
      (ν₀.map fun i' => G.degΨ i' i).sum + d i * (Λc 0 i + Λc 1 i) := by
  refine (Seq.sum_lbl t ((Gb).degΨ · (.inl i))).trans ?_
  rw [Multiset.map_map]
  have h : ((Gb).degΨ · (.inl i)) ∘ cupColour (ℓ := ℓ) j hj = ((Gc).degΨ · (.inl i)) :=
    funext fun a => degΨ_cupColour G d hd a (.inl i)
  rw [h, stendhalWeight, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
    Multiset.map_map]
  simp [stendhalGradingDatum]
  ring

omit [DecidableEq I] in
theorem sum_degΨ_cup_right (t : Seq ((stendhalWeight 2 ν₀).map (cupColour (ℓ := ℓ) j hj)))
    (i : I) : ∑ b, (Gb).degΨ (.inl i) (t.lbl b) =
      (ν₀.map fun i' => G.degΨ i i').sum + d i * (Λc 0 i + Λc 1 i) := by
  refine (Seq.sum_lbl t ((Gb).degΨ (.inl i) ·)).trans ?_
  rw [Multiset.map_map]
  have h : ((Gb).degΨ (.inl i) ·) ∘ cupColour (ℓ := ℓ) j hj = ((Gc).degΨ (.inl i) ·) :=
    funext fun a => degΨ_cupColour G d hd (.inl i) a
  rw [h, stendhalWeight, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
    Multiset.map_map]
  simp [stendhalGradingDatum]
  ring

omit [DecidableEq I] in
/-- **The degree of the passage in (max1)**: the black strand of colour `i` at the bottom
position `q + N`, right of the strands at the maximum, crossing them to the top position `q`. -/
theorem degW_underRight (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) {i : I}
    (hi : s.lbl ⟨q, by omega⟩ = .inl i)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) :
    (Gb).degW (List.range' q N) (insertSeq s q (by omega) t) =
      (ν₀.map fun i' => G.degΨ i' i).sum + d i * (Λc 0 i + Λc 1 i) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hN : Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (ℓ := ℓ) j hj)) = N :=
    Multiset.card_map _ _
  rw [GradingDatum.degW_range' _ N q (by omega)]
  rw [← sum_degΨ_cup_left G d hd t i]
  refine Fintype.sum_equiv (finCongr hN.symm) _ _ fun b => ?_
  rw [insertSeq_lbl_of_val_new (j := j) (hj := hj) s _ t _ (finCongr hN.symm b) rfl,
    insertSeq_lbl_of_val_old (j := j) (hj := hj) s _ t _ ⟨q, by omega⟩
      (by simp only [hN, lt_irrefl, ↓reduceIte]), hi]
  rfl

omit [DecidableEq I] in
/-- **The degree of the passage in (max2)**: the black strand of colour `i` at the bottom
position `q`, left of the strands at the maximum, crossing them to the top position `q + N`. -/
theorem degW_underLeft (s : Seq (stendhalWeight ℓ ν)) {q : ℕ} (hq : q + 1 ≤ m) {i : I}
    (hi : s.lbl ⟨q, by omega⟩ = .inl i)
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) :
    (Gb).degW (List.range' q N).reverse (insertSeq s (q + 1) hq t) =
      (ν₀.map fun i' => G.degΨ i i').sum + d i * (Λc 0 i + Λc 1 i) := by
  have hM := card_plus' (I := I) (ℓ := ℓ) (ν := ν) (ν₀ := ν₀)
  have hN : Multiset.card ((stendhalWeight 2 ν₀).map (cupColour (ℓ := ℓ) j hj)) = N :=
    Multiset.card_map _ _
  rw [GradingDatum.degW_range'_reverse _ q N (by omega)]
  rw [← sum_degΨ_cup_right G d hd t i]
  refine Fintype.sum_equiv (finCongr hN.symm) _ _ fun b => ?_
  rw [insertSeq_lbl_of_val_old (j := j) (hj := hj) s _ t _ ⟨q, by omega⟩
      (by simp), hi,
    insertSeq_lbl_of_val_new (j := j) (hj := hj) s _ t _ (finCongr hN.symm b)
      (by simp only [finCongr_apply, Fin.val_cast])]
  rfl

end Categorification.Stendhal.CupCap
