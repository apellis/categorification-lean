/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OneBlackCrossingTest
import Categorification.WeightedKLR.RedStrands.OneBlackHigherKernelChain
import Categorification.WeightedKLR.RedStrands.ZeroSpectatorKernelChain

/-!
# The one-black higher-kernel filtration for a first pair of reds

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
Moving the unique black left across the spectator reds constructs the actual
higher partial-standard filtration in canonical red order.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA BraidedStendhalAlgebra

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {i : I}
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "n" => Multiset.card μ

/-- Swapping the unique black past an adjacent retained red strictly raises
the retained root. -/
theorem adjacentBlockRoot_oneBlack_lt_sadj {a b r : Fin ℓ} {L M : List (Fin ℓ)}
    (s : Seq μ) (hs : redWord s = L ++ a :: b :: M) {j : ℕ} (hj : j + 1 < n)
    (hr : s.lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ = .inr r)
    (hb : s.lbl ⟨j + 1, hj⟩ = .inl i) (hretained : r ≠ b) :
    adjacentBlockRoot a b s < adjacentBlockRoot a b (sadj n j • s) := by
  let u : Fin n := ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩
  let v : Fin n := ⟨j + 1, hj⟩
  let t := sadj n j • s
  have hswap (q : Fin n) : t.lbl q = s.lbl (sadj n j q) := sadj_smul_apply j s q
  have ht : redWord t = redWord s :=
    redWord_sadj_smul s hj (by rw [hr, hb]; simp)
  have htu : t.lbl u = .inl i := by
    rw [hswap, show sadj n j u = v from sadj_apply_left hj]
    exact hb
  have htv : t.lbl v = .inr r := by
    rw [hswap, show sadj n j v = u from sadj_apply_right hj]
    exact hr
  apply (adjacentBlockRoot_oneBlack_lt_iff hs (ht.trans hs) v u hb htu).2
  refine ⟨?_, r, u, v, hretained, hr, htv, Nat.le_succ _, Nat.lt_succ_self _⟩
  apply (adjacentBlockRoot_oneBlack_le_iff hs (ht.trans hs) v u hb htu).2
  intro q _ ps pt hps hpt hlt
  have hpos : ps = sadj n j pt := lbl_inj_of_inr s q hps ((hswap pt).symm.trans hpt)
  have hneL : ps.val ≠ j := by change j + 1 < ps.val at hlt; omega
  have hneR : ps.val ≠ j + 1 := by change j + 1 < ps.val at hlt; omega
  have hfix : sadj n j ps = ps := sadj_apply_of_ne ps hneL hneR
  have hq : pt = ps := calc
    pt = sadj n j (sadj n j pt) := (TypeA.sadj_sadj_apply n j pt).symm
    _ = sadj n j ps := congrArg (sadj n j) hpos.symm
    _ = ps := hfix
  rw [hq]
  exact Nat.lt_trans (Nat.lt_succ_self j) hlt

end Categorification.Stendhal


namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [CommRing k] {ℓ : ℕ} {i : I}
local notation "ν" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
local notation "C" => {s : Seq μ // redWord s = List.finRange ℓ}

omit [DecidableEq I] in
/-- With one black, every other position has a red label. -/
theorem oneBlack_hasRed_at_ne (s : Seq μ) {x y : Fin n}
    (hx : s.lbl x = .inl i) (hne : y ≠ x) :
    ∃ r : Fin ℓ, s.lbl y = .inr r := by
  cases h : s.lbl y with
  | inr r => exact ⟨r, rfl⟩
  | inl c =>
    exfalso
    have hmem := Seq.mem s y
    change s.lbl y ∈ μ at hmem
    rw [h] at hmem
    have hc : c = i := by simpa [stendhalWeight] using hmem
    subst c
    have hn : (Finset.univ.val.map s.lbl).Nodup := by
      rw [show Finset.univ.val.map s.lbl = μ from s.2]
      simp [stendhalWeight, List.nodup_ofFn, Sum.inr_injective]
    exact hne (Multiset.inj_on_of_nodup_map hn y (by simp) x (by simp) (h.trans hx.symm))

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
variable (hQ : KLRSymm Q)
/-- Ordinary crossing tests for every position of the unique black. -/
def OrdinaryOneBlackTests : Prop := ∀ (s : Seq μ) (_ : IsRedOrdered s) (j : ℕ) (hj : j + 1 < n),
    s.lbl ⟨j + 1, hj⟩ = .inl i →
    ∀ x : TensorProductAlgebra k Q Λ ν,
      x * tensorOfKLR Q Λ ν (KLRAlgebra.e (sadj n j • s)) = x →
      x * tensorOfKLR Q Λ ν (KLRAlgebra.ψ j * KLRAlgebra.e s) = 0 → x = 0


private theorem oneBlack_firstPair_chainEnd
    (a b : Fin ℓ) (ha : a.val = 0) (hb : b.val = 1)
    (M : List (Fin ℓ)) (hword : List.finRange ℓ = a :: b :: M)
    (s : C) (p : Fin n) (hp : s.1.lbl p = .inl i)
    (hk : p.val ≤ 2) :
    HigherProjectiveChain Q Λ a b (List.finRange ℓ) s [] := by
  have hs : IsRedOrdered s.1 := (redWord_eq_finRange_iff _).1 s.2
  have hbefore : ∀ r : Fin ℓ, r ≠ a → r ≠ b →
      ∀ q : Fin n, s.1.lbl q = .inr r → p < q := by
    intro r hra hrb q hq
    have hrr : b < r := by
      change b.val < r.val
      have hna : r.val ≠ a.val := fun e => hra (Fin.ext e)
      have hnb : r.val ≠ b.val := fun e => hrb (Fin.ext e)
      omega
    obtain ⟨pa, hpa⟩ := exists_lbl_eq_inr s.1 a
    obtain ⟨pb, hpb⟩ := exists_lbl_eq_inr s.1 b
    have hlt_of_lt {q₁ q₂ : Fin n} {r₁ r₂ : Fin ℓ}
        (hq₁ : s.1.lbl q₁ = .inr r₁) (hq₂ : s.1.lbl q₂ = .inr r₂)
        (hr : r₁ < r₂) : q₁ < q₂ := by
      by_contra! he
      rcases eq_or_lt_of_le he with heq | hlt
      · subst q₁
        exact hr.ne (Sum.inr.inj (hq₁.symm.trans hq₂))
      · exact (not_lt_of_ge hr.le) (hs _ _ _ _ hlt hq₂ hq₁)
    have hab : a < b := by change a.val < b.val; omega
    have h01 := hlt_of_lt hpa hpb hab
    have h12 := hlt_of_lt hpb hq hrr
    have hneq : p.val ≠ q.val := by
      intro h
      have he : p = q := Fin.ext h
      rw [he] at hp
      have hh := hp.symm.trans hq
      cases hh
    change p.val < q.val
    change pa.val < pb.val at h01
    change pb.val < q.val at h12
    omega
  exact HigherProjectiveChain.nil_of_maximal Q Λ fun _ ho hlt =>
    isViolated_of_strictly_higher_beforeSpectators (s.2.trans hword) ho p hp hbefore hlt

private theorem oneBlack_firstPair_next
    (a b : Fin ℓ) (hb : b.val = 1)
    (M : List (Fin ℓ)) (hword : List.finRange ℓ = a :: b :: M)
    (s : C) (p : Fin n) (hp : s.1.lbl p = .inl i)
    (hk : 2 < p.val) :
    ∃ (t : C) (u : Fin n) (j : ℕ) (hj : j + 1 < n) (r : Fin ℓ),
      u.val + 1 = p.val ∧ t.1.lbl u = .inl i ∧
      adjacentBlockRoot a b s.1 < adjacentBlockRoot a b t.1 ∧
      sadj n j • s.1 = t.1 ∧
      s.1.lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ = .inr r ∧
      s.1.lbl ⟨j + 1, hj⟩ = .inl i := by
  have hs : IsRedOrdered s.1 := (redWord_eq_finRange_iff _).1 s.2
  let j := p.val - 1
  have hj : j + 1 < n := by have hp' := p.isLt; omega
  let v : Fin n := ⟨j + 1, hj⟩
  let u : Fin n := ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩
  have hv : v = p := Fin.ext (by change j + 1 = p.val; omega)
  have hbL : s.1.lbl v = .inl i := hv.symm ▸ hp
  have hne : u ≠ v := fun h => (Nat.ne_of_lt (Nat.lt_succ_self j)) (congrArg Fin.val h)
  obtain ⟨r, hr⟩ := oneBlack_hasRed_at_ne s.1 hbL hne
  let p0 : Fin n := ⟨0, by have := p.isLt; omega⟩
  let p1 : Fin n := ⟨1, by have := p.isLt; omega⟩
  obtain ⟨r0, hr0⟩ := oneBlack_hasRed_at_ne s.1 hbL
    (show p0 ≠ v from fun h => by have e := congrArg Fin.val h; change 0 = j + 1 at e; omega)
  obtain ⟨r1, hr1⟩ := oneBlack_hasRed_at_ne s.1 hbL
    (show p1 ≠ v from fun h => by have e := congrArg Fin.val h; change 1 = j + 1 at e; omega)
  have h01 : r0 < r1 := hs p0 p1 _ _ (Nat.zero_lt_succ _) hr0 hr1
  have h1r : r1 < r := hs p1 u _ _ (by change 1 < j; omega) hr1 hr
  have hrb : r ≠ b := fun e => by
    subst r
    change r1.val < b.val at h1r
    change r0.val < r1.val at h01
    omega
  let t : C := ⟨sadj n j • s.1,
    (redWord_sadj_smul s.1 hj (by rw [show s.1.lbl ⟨j + 1, hj⟩ = .inl i from hbL]; simp)).trans s.2⟩
  have ht : t.1.lbl u = .inl i := by
    change (sadj n j • s.1).1 u = _
    rw [sadj_smul_apply, show sadj n j u = v from sadj_apply_left hj]
    exact hbL
  have hlt : adjacentBlockRoot a b s.1 < adjacentBlockRoot a b t.1 :=
    adjacentBlockRoot_oneBlack_lt_sadj s.1 (a := a) (b := b) (r := r)
      (L := []) (s.2.trans hword) hj hr hbL hrb
  exact ⟨t, u, j, hj, r, by change j + 1 = p.val; omega, ht, hlt, rfl, hr, hbL⟩

include hQ in
private theorem firstPair_cons_swap
    (allTests : OrdinaryOneBlackTests Q Λ (i := i))
    {a b r : Fin ℓ} {M : List (Fin ℓ)}
    {s t : C} {tail : List C}
    (hs : redWord s.1 = [] ++ a :: b :: M)
    (j : ℕ) (hj : j + 1 < n)
    (hlt : adjacentBlockRoot a b s.1 < adjacentBlockRoot a b t.1)
    (hstep : sadj n j • s.1 = t.1)
    (hr : s.1.lbl ⟨j, lt_trans (Nat.lt_succ_self _) hj⟩ = .inr r)
    (hblack : s.1.lbl ⟨j+1,hj⟩ = .inl i)
    (hchain : HigherProjectiveChain Q Λ a b (List.finRange ℓ) t tail) :
    HigherProjectiveChain Q Λ a b (List.finRange ℓ) s (t :: tail) := by
  apply HigherProjectiveChain.cons_of_oneBlack_ordinary_test Q Λ hs hlt j hj hstep hr hblack hQ _ hchain
  intro x hx hc
  have he := congrArg (fun w : Seq μ => x * tensorOfKLR Q Λ ν (KLRAlgebra.e w)) hstep
  exact allTests s.1 ((redWord_eq_finRange_iff _).1 s.2) j hj hblack x (he.trans hx) hc

include hQ in
private theorem oneBlack_firstPair_chainStep
    (allTests : OrdinaryOneBlackTests Q Λ (i := i))
    (a b : Fin ℓ) (hb : b.val = 1)
    (M : List (Fin ℓ)) (hword : List.finRange ℓ = a :: b :: M)
    (s : C) (p : Fin n) (hp : s.1.lbl p = .inl i)
    (hk : 2 < p.val) :
    ∃ (t : C) (u : Fin n), u.val + 1 = p.val ∧ t.1.lbl u = .inl i ∧
      ∀ tail : List C, HigherProjectiveChain Q Λ a b (List.finRange ℓ) t tail →
        HigherProjectiveChain Q Λ a b (List.finRange ℓ) s (t :: tail) := by
  obtain ⟨t, u, j, hj, r, hdec, ht, hlt, hstep, hr, hbL⟩ :=
    oneBlack_firstPair_next a b hb M hword s p hp hk
  have hs' : redWord s.1 = [] ++ a :: b :: M := s.2.trans hword
  refine ⟨t, u, hdec, ht, ?_⟩
  intro tail htail
  exact firstPair_cons_swap Q Λ hQ allTests hs' j hj hlt hstep hr hbL htail

include hQ in
/-- Moving the unique black left across the spectators of the first pair
gives a finite higher-projective chain in the canonical order. -/
theorem oneBlack_firstPair_higherProjectiveChain_of_tests
    (tests : OrdinaryOneBlackTests Q Λ (i := i))
    (a b : Fin ℓ) (ha : a.val = 0) (hb : b.val = 1)
    (M : List (Fin ℓ)) (hword : List.finRange ℓ = a :: b :: M)
    (s : C) (p : Fin n) (hp : s.1.lbl p = .inl i) :
    ∃ tail : List C, tail.length = p.val - 2 ∧
      HigherProjectiveChain Q Λ a b (List.finRange ℓ) s tail := by
  suffices aux : ∀ k : ℕ, ∀ (s : C) (p : Fin n), s.1.lbl p = .inl i → p.val = k →
      ∃ tail : List C, tail.length = p.val - 2 ∧
      HigherProjectiveChain Q Λ a b (List.finRange ℓ) s tail from aux _ s p hp rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s p hp hlen
    by_cases hk : 2 < p.val
    · obtain ⟨t, u, hlt, ht, step⟩ :=
        oneBlack_firstPair_chainStep Q Λ hQ tests a b hb M hword s p hp hk
      have hdec : u.val < k := by omega
      obtain ⟨tail, hlenTail, htail⟩ := ih u.val hdec t u ht rfl
      refine ⟨t :: tail, ?_, step tail htail⟩
      simp only [List.length_cons]
      omega
    · exact ⟨[], by simp [Nat.sub_eq_zero_of_le (le_of_not_gt hk)],
        oneBlack_firstPair_chainEnd Q Λ a b ha hb M hword s p hp (le_of_not_gt hk)⟩

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA ModuleFiltration
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [CommRing k] {m : ℕ}
variable {i : I}
local notation "ℓ" => (m + 2)
local notation "ν" => (Singleton.singleton i : Multiset I)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
local notation "C" => {s : Seq μ // redWord s = List.finRange ℓ}

private theorem finRange_starts_with_pair :
    ∃ M : List (Fin ℓ), List.finRange ℓ = (0 : Fin ℓ) :: 1 :: M := by
  rw [List.finRange_succ, List.finRange_succ, List.map_cons]
  exact ⟨_, rfl⟩

/-- With the first two reds as the paired block, the one-black kernel has an
actual finite higher-partial-standard filtration whenever the crossing tests hold. -/
theorem oneBlack_firstPair_hasFiltration_of_tests
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
    (hQ : KLRSymm Q)
    (tests : OrdinaryOneBlackTests Q Λ (i := i))
    (s : C) :
    ∃ p : Fin n, s.1.lbl p = .inl i ∧
      ∃ tail : List C, tail.length = p.val - 2 ∧
        HasFiltration (fun t : C => blockPartialStandardAt Q Λ t.1 0 1 (List.finRange ℓ) t.2)
          tail (fixedOrderKernelObj Q Λ 0 1 (List.finRange ℓ) s) := by
  obtain ⟨M, hM⟩ := finRange_starts_with_pair (m := m)
  have hm : (Sum.inl i : I ⊕ Fin ℓ) ∈ μ := by simp [stendhalWeight]
  rw [← show Finset.univ.val.map s.1.lbl = μ from s.1.2, Multiset.mem_map] at hm
  obtain ⟨p, _, hp⟩ := hm
  obtain ⟨tail, hlen, chain⟩ :=
    oneBlack_firstPair_higherProjectiveChain_of_tests Q Λ hQ tests 0 1 rfl rfl M hM s p hp
  exact ⟨p, hp, tail, hlen, HigherProjectiveChain.hasFiltration Q Λ 0 1 (List.finRange ℓ) chain⟩

end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR ModuleFiltration QuantumGroup KL3.Diagram
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [DecidableEq I] [Field k] {m : ℕ}
variable {D : CartanDatum I}
local notation "ℓ" => (m + 2)
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)

/-- At standard Khovanov–Lauda parameters, the one-black kernel for the first
two reds has one retained partial-standard layer per spectator left of the
black, in the canonical red order. -/
theorem oneBlack_firstPair_hasFiltration_standard
    (hR : IsRouquierQ D QL) (hQ : KLRSymm QL) (i : I) (Λ : Fin ℓ → I →₀ ℕ)
    (s : {s : Seq (stendhalWeight ℓ ({i} : Multiset I)) // redWord s = List.finRange ℓ}) :
    ∃ p : Fin (stendhalWeight ℓ ({i} : Multiset I)).card, s.1.lbl p = .inl i ∧
      ∃ tail : List {t : Seq (stendhalWeight ℓ ({i} : Multiset I)) // redWord t = List.finRange ℓ},
        tail.length = p.val - 2 ∧
        HasFiltration (fun t => blockPartialStandardAt QL Λ t.1 0 1 (List.finRange ℓ) t.2)
          tail (fixedOrderKernelObj QL Λ 0 1 (List.finRange ℓ) s) := by
  have tests : OrdinaryOneBlackTests QL Λ (i := i) :=
    oneBlack_crossing_injective_standard hR hQ i Λ
  exact oneBlack_firstPair_hasFiltration_of_tests QL Λ hQ tests s

end Categorification.Stendhal.BraidedStendhalAlgebra
