/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.K0Relations

/-!
# Divided powers and the Serre relations in `K₀(U̇)` (upward strands)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.6, proof of
Proposition 3.27: the divided-power decomposition `E_{+i^m} 1_λ ≅ (E_{+i^{(m)}} 1_λ)^{⊕[m]_i!}`
(display after (3.55)) and the categorified Serre relation (Proposition 3.24, first display)
"descend to relations in the Grothendieck group `K₀(U̇)`".

## Main results

* `cl_kobj_split`: a graded splitting `f' = ∑_j a_j f b_j` (`b_j a_{j'} = δ f`, `a_j` of degree
  `d_j`, `b_j` of degree `-d_j`) of idempotents of `R(ν)` gives
  `[(E_s 1_μ, ϕ(f'))] = (∑_j q^{d_j}) [(E_s 1_μ, ϕ(f))]` in `K₀(U̇)`.
* `exists_split_block`: `1_{…}` splits through the divided-power idempotent of any constant block
  of a sequence (in the presence of other blocks), with generating function
  `∏_{n<N} ∑_{r≤n} q^{(c·c)(r-n)}` (a generalization of
  `Categorification.Diagrams.KL3.exists_split` to arbitrary sequences and blocks).
* `eC_pow`: **divided powers in `K₀`**: in any context `a`, `b`,
  `[E_{a (+i)^m b} 1_λ] = [m]_i! [E_a E_{+i^{(m)}} E_b 1_λ]`, where
  `[m]_i! = qfac (d_i) m = ∏_{n=1}^{m} [n]_i` (symmetric quantum factorial).
* `eC_serre`: **the Serre relation in `K₀`**: for `i ≠ j`, `N = d_ij + 1` and any context,
  there are classes `Y_n` (`n ≤ N`; `Y_n = q^{-((n choose 2) + ((N-n) choose 2)) d_i}` times the
  class of `E_a E_{+i^{(n)} +j +i^{(N-n)}} E_b 1_λ`) with
  `[E_{a (+i)^n (+j) (+i)^{N-n} b} 1_λ] = [n]_i! [N-n]_i! Y_n` and
  `∑_{n even} Y_n = ∑_{n odd} Y_n`.

Over `ℚ(q)` this is the vanishing of the image of the Serre element
`∑_{n} (-1)^n E_i^{(n)} E_j E_i^{(N-n)}` of `U̇`. Only upward strands are treated, as in
`Categorification.Diagrams.KL3.SerreKaroubi`: the downward versions (the `F`-Serre relation and
`F`-divided powers) need the homomorphism `ϕ_{-ν,λ}` or the symmetry `ω̃`, not available here.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory CategoryTheory.Limits StringDiagrams QuantumGroup UDot Presentation
  Categorification.GradedBicat KLR KLR.KLRAlgebra KLR.Diagram KLR.KL2 LaurentPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k] [DecidableEq I]

/-! ## Splitting along an arbitrary block -/

section SplitBlock

variable {k} {ν : Multiset I} (t : Seq ν) (c : I) (p : ℕ) (bs : List (ℕ × ℕ))

local notation "G2" => klGradingDatum2 k C

omit [DecidableEq I] in
theorem IsBlocks.shrink {N : ℕ} (h : IsBlocks t ((p, N + 1) :: bs)) : IsBlocks t ((p, N) :: bs) where
  le b hb := by
    rcases List.mem_cons.1 hb with rfl | hb
    · have := h.le _ List.mem_cons_self; simp only at this ⊢; omega
    · exact h.le b (List.mem_cons_of_mem _ hb)
  const b hb := by
    rcases List.mem_cons.1 hb with rfl | hb
    · intro a a' h1 h2 h3 h4
      exact h.const _ List.mem_cons_self a a' h1 (by simp only at h2 ⊢; omega) h3
        (by simp only at h4 ⊢; omega)
    · exact h.const b (List.mem_cons_of_mem _ hb)
  disj := by
    have := h.disj
    rw [List.pairwise_cons] at this ⊢
    refine ⟨fun b hb => ?_, this.2⟩
    have := this.1 b hb
    simp only at this ⊢
    omega

/-- **Splitting along a block**: for a block `[p, p + N)` of `t` with constant label `c` (and
further divided-power blocks `bs`), `1_{…} = divIdem t bs` splits through
`divIdem t ((p, N) :: bs)` with `N!` summands and degrees
`∑_j q^{d_j} = ∏_{n<N} ∑_{r≤n} q^{(c·c)(r-n)}`. -/
theorem exists_split_block : ∀ N : ℕ, IsBlocks t ((p, N) :: bs) →
    (∀ a : Fin (Multiset.card ν), p ≤ (a : ℕ) → (a : ℕ) < p + N → t.lbl a = c) →
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (a b : ι → R2 k C ν) (dg : ι → ℤ),
      Graded.IsSplitting (divIdem t bs) (fun _ => divIdem t ((p, N) :: bs)) a b ∧
      (∀ j, a j ∈ (klGradingDatum2 k C).grade ν (dg j)) ∧ (∀ j, b j ∈ (klGradingDatum2 k C).grade ν (-dg j)) ∧
      ∑ j, (T (dg j) : LaurentPolynomial ℤ) =
        ∏ n ∈ Finset.range N, ∑ r ∈ Finset.range (n + 1), T (C.dot c c * ((r : ℤ) - n))
  | 0, hB, _ => by
    have h0 : (divIdem t ((p, 0) :: bs) : R2 k C ν) = divIdem t bs := by
      rw [divIdem, divIdem, blocksElt_cons, blockElt_zero, one_mul]
    have hE := isIdempotentElem_divIdem (k := k) (Q := klQ2 k C) hB.tail
    refine ⟨Unit, inferInstance, inferInstance, fun _ => divIdem t bs, fun _ => divIdem t bs,
      fun _ => 0, ⟨fun _ _ => ?_, ?_⟩, fun _ => ?_, fun _ => ?_, ?_⟩
    · rw [if_pos rfl, h0, hE.eq]
    · simp [hE.eq]
    · exact divIdem_mem_grade G2 hB.tail
    · simpa using divIdem_mem_grade G2 hB.tail
    · simp
  | N + 1, hB, hcl => by
    obtain ⟨ι, _, _, a, b, dg, hS, ha, hb, hgen⟩ := exists_split_block N (IsBlocks.shrink t p bs hB)
      (fun a h1 h2 => hcl a h1 (by omega))
    have hstep := isSplitting_divIdem_succ (k := k) (Q := klQ2 k C) hB
    have hpn := hB.le _ List.mem_cons_self
    have hc' := hB.const _ List.mem_cons_self
    refine ⟨ι × Fin (N + 1), inferInstance, inferInstance,
      fun q => a q.1 * (divIdem t bs * blockA k (klQ2 k C) t hpn q.2),
      fun q => blockB k (klQ2 k C) t hpn q.2 * b q.1,
      fun q => dg q.1 + C.dot c c * ((q.2 : ℤ) - N),
      hS.trans hstep (isIdempotentElem_divIdem hB) (isIdempotentElem_divIdem hB.tail),
      fun q => ?_, fun q => ?_, ?_⟩
    · have h1 := blockA_mem_grade G2 hpn hcl hc' q.2
      have h2 := SetLike.mul_mem_graded (divIdem_mem_grade G2 hB.tail) h1
      have h3 := SetLike.mul_mem_graded (ha q.1) h2
      convert h3 using 2
      simp [klGradingDatum2]
    · have h1 := blockB_mem_grade G2 hpn hcl hc' (j := q.2) (by omega)
      have h3 := SetLike.mul_mem_graded h1 (hb q.1)
      convert h3 using 2
      simp only [klGradingDatum2]
      ring
    · rw [Fintype.sum_prod_type, Finset.prod_range_succ, ← hgen, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun r => (T (dg j) * T (C.dot c c * ((r : ℤ) - N)) :
        LaurentPolynomial ℤ)) (N + 1)]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [T_add]

end SplitBlock

/-! ## Classes of the 1-morphisms `(E_s 1_μ, ϕ(f))` -/

section KObj

variable {RD k} {μ : X} {ν : Multiset I}

/-- `[(E_s 1_μ {t}, ϕ(f))] = q^t [(E_s 1_μ, ϕ(f))]`. -/
theorem kobj_shift {s : Seq ν} (F : CornerIdem C k s) (t : ℤ) :
    K0U.cl (kobj RD μ F t) = (T t : LaurentPolynomial ℤ) • K0U.cl (kobj RD μ F 0) :=
  K0U.idemObj_shift _ _ _ _ _

/-- **Graded splittings in `K₀`**: if `f' = ∑_j a_j b_j` with `b_j a_{j'} = δ_{j j'} f`
(`Graded.IsSplitting`), `a_j` of degree `d_j` and `b_j` of degree `-d_j`, then
`[(E_s 1_μ, ϕ(f'))] = (∑_j q^{d_j}) [(E_s 1_μ, ϕ(f))]`. -/
theorem cl_kobj_split {s : Seq ν} (F' F : CornerIdem C k s) {ι : Type} [Fintype ι]
    [DecidableEq ι] {a b : ι → R2 k C ν} {dg : ι → ℤ}
    (hS : Graded.IsSplitting F'.f (fun _ => F.f) a b)
    (ha : ∀ j, a j ∈ (klGradingDatum2 k C).grade ν (dg j))
    (hb : ∀ j, b j ∈ (klGradingDatum2 k C).grade ν (-dg j)) :
    K0U.cl (kobj RD μ F' 0) = (∑ j, (T (dg j) : LaurentPolynomial ℤ)) • K0U.cl (kobj RD μ F 0) := by
  obtain ⟨ho, hsum, hpair⟩ := hS.orthogonalIdempotents F.idem F'.idem
  have hdeg : ∀ j, a j * F.f * b j ∈ (klGradingDatum2 k C).grade ν 0 := fun j => by
    have := SetLike.mul_mem_graded (SetLike.mul_mem_graded (ha j) F.deg0) (hb j)
    rwa [add_zero, add_neg_cancel] at this
  have hF'g : ∀ j, F'.f * (a j * F.f * b j) = a j * F.f * b j := fun j => by
    rw [← hsum, Finset.sum_mul, Finset.sum_eq_single j (fun j' _ h => ho.ortho h)
      (fun h => absurd (Finset.mem_univ j) h), (ho.idem j).eq]
  let Gs : ι → CornerIdem C k s := fun j =>
    { f := a j * F.f * b j
      deg0 := hdeg j
      idem := ho.idem j
      left := by rw [← hF'g j, ← mul_assoc, F'.left] }
  have iso1 := kOrthIso (RD := RD) (μ := μ) F' Gs hsum (fun j j' h => ho.ortho h) 0
  have iso2 : ∀ j, kobj RD μ (Gs j) 0 ≅ kobj RD μ F (0 + dg j) := fun j =>
    kIso (Gs j) F (hpair j)
      (by have := SetLike.mul_mem_graded (ha j) F.deg0; rwa [add_zero] at this)
      (by have := SetLike.mul_mem_graded F.deg0 (hb j); rwa [zero_add] at this) 0
  show SplitK0.of (kobj RD μ F' 0) = _ • SplitK0.of (kobj RD μ F 0)
  rw [SplitK0.of_iso iso1, SplitK0.of_biproduct, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [SplitK0.of_iso (iso2 j), zero_add]
  exact kobj_shift F (dg j)

end KObj

/-! ## Divided powers in `K₀` -/

/-- The symmetric quantum factorial `[m]!` in the variable `q^d`:
`∏_{n<m} ∑_{r≤n} q^{d (2r - n)} = ∏_{n=1}^{m} [n]_{q^d}`. -/
def qfac (d : ℤ) (m : ℕ) : LaurentPolynomial ℤ :=
  ∏ n ∈ Finset.range m, ∑ r ∈ Finset.range (n + 1), T (d * (2 * (r : ℤ) - n))

section Pow

variable {RD k}

/-- **Divided powers in `K₀(U̇)`** (KL III, display after (3.55), in context): for signed
sequences `a`, `b`,
`[E_{a (+i)^m b} 1_λ] = [m]_i! [E_a E_{+i^{(m)}} E_b 1_λ]`, where `E_{+i^{(m)}} 1_μ` is the
1-morphism `objEdiv` of KL III (3.54) and `[m]_i! = qfac d_i m`. -/
theorem eC_pow (i : I) (m : ℕ) {ρ μ lam : X} (a b : List (Letter I))
    (ha : wt RD (wν RD (Multiset.replicate m i) + μ) a = ρ) (hb : wt RD lam b = μ)
    (h : wt RD lam (a ++ ups (List.replicate m i) ++ b) = ρ) :
    eC RD k ρ lam (a ++ ups (List.replicate m i) ++ b) h =
      qfac (di C i) m • K0U.cl ((wRDot (deg RD) (nfHom RD k μ lam b hb)).obj
        ((wLDot (deg RD) (nfHom RD k ρ _ a ha)).obj (objEdiv RD k i m μ 0))) := by
  obtain ⟨ι, _, _, sh, _, hgen, ⟨e⟩⟩ := Epow_decomp RD k i m μ
  let G := wLDot (deg RD) (nfHom RD k ρ _ a ha) ⋙ wRDot (deg RD) (nfHom RD k μ lam b hb)
  have h1 := congrArg (SplitK0.map G) (SplitK0.of_iso e)
  rw [SplitK0.of_biproduct, map_sum, SplitK0.map_of] at h1
  simp only [SplitK0.map_of] at h1
  erw [ctx_nfObj ha _ hb h] at h1
  refine h1.trans ?_
  have hs : ∀ s, K0U.cl (G.obj (objEdiv RD k i m μ s)) =
      (T s : LaurentPolynomial ℤ) • K0U.cl (G.obj (objEdiv RD k i m μ 0)) := fun s => by
    have e2 : objEdiv RD k i m μ s ≅ (shDot (deg RD) s).obj (objEdiv RD k i m μ 0) :=
      eqToIso (kobj_congr_shift RD k μ _ (by ring)) ≪≫ K0U.idemObjShift _ _ _ _ _ _
    exact (SplitK0.of_iso (G.mapIso e2)).trans (K0U.ctx_shift _ _ s _)
  rw [qfac, ← hgen, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => hs (sh j)

end Pow

omit [DecidableEq I] in
/-- `∏_{n<m} ∑_{r≤n} q^{2d(r-n)} = q^{-(m choose 2) d} [m]_{q^d}!`. -/
theorem prod_sum_T_eq (d : ℤ) (m : ℕ) :
    ∏ n ∈ Finset.range m, ∑ r ∈ Finset.range (n + 1), (T (2 * d * ((r : ℤ) - n)) :
      LaurentPolynomial ℤ) = T (-((m.choose 2 : ℕ) : ℤ) * d) * qfac d m := by
  have h : ∀ n ∈ Finset.range m, ∑ r ∈ Finset.range (n + 1), (T (2 * d * ((r : ℤ) - n)) :
      LaurentPolynomial ℤ) = T (-d * n) * ∑ r ∈ Finset.range (n + 1), T (d * (2 * (r : ℤ) - n)) :=
    fun n _ => by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← T_add]; congr 1; ring
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, qfac, prod_T_eq, ← Finset.mul_sum,
    sum_range_choose_two]
  congr 2; ring

/-! ## The Serre relation in `K₀` -/

section Serre

variable {RD k} {ν : Multiset I} {t : Seq ν} {p N : ℕ} {i j : I}
  (hpN : p + N < Multiset.card ν)
  (ht₀ : ∀ r : Fin (Multiset.card ν), (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin (Multiset.card ν), p < r → (r : ℕ) ≤ p + N → t.lbl r = i)
  (hij : i ≠ j)

omit [DecidableEq I] in
theorem isBlocks_nil_seq : IsBlocks t [] := ⟨by simp, by simp, List.Pairwise.nil⟩

theorem hbs_nil : ∀ b ∈ ([] : List (ℕ × ℕ)), b.1 + b.2 ≤ p ∨ p + N + 1 ≤ b.1 := by simp

include hpN ht₀ ht hij in
/-- `[E_{S n} 1_μ] = q^{-((n choose 2) + ((N-n) choose 2)) d_i} [n]_i! [N-n]_i!
[E_{…i^{(n)} j i^{(N-n)}…} 1_μ]` for the Serre sequences `S n = …i^n j i^{N-n}…` (no context
blocks), where `E_{…i^{(n)} j i^{(N-n)}…} 1_μ = (E_{S n} 1_μ, ϕ(1_{…i^{(n)} j i^{(N-n)}…}))`. -/
theorem cl_serre_split (μ : X) {n : ℕ} (hn : n ≤ N) :
    K0U.cl (kobj RD μ (CornerIdem.ofE (C := C) (k := k) (serreSeq t p n)) 0) =
      (qfac (di C i) n * qfac (di C i) (N - n) *
        T (-((((n.choose 2 : ℕ) : ℤ) + (((N - n).choose 2 : ℕ) : ℤ)) * di C i))) •
        K0U.cl (kobj RD μ (serreCorner C k hpN ht₀ ht isBlocks_nil_seq hbs_nil hij n hn) 0) := by
  have hB := isBlocks_etop (N := N) hpN ht₀ ht hn
  obtain ⟨ι₁, _, _, a₁, b₁, dg₁, hS₁, ha₁, hb₁, hg₁⟩ :=
    exists_split_block (k := k) (C := C) (serreSeq t p n) i (p + n + 1) [] (N - n) hB.tail
      (fun r h1 h2 => serreSeq_lbl_eq_i hpN ht₀ ht hn r (by omega) (by omega) (by omega))
  obtain ⟨ι₂, _, _, a₂, b₂, dg₂, hS₂, ha₂, hb₂, hg₂⟩ :=
    exists_split_block (k := k) (C := C) (serreSeq t p n) i p [(p + n + 1, N - n)] n hB
      (fun r h1 h2 => serreSeq_lbl_eq_i hpN ht₀ ht hn r (by omega) (by omega) (by omega))
  have hS := hS₁.trans hS₂ (isIdempotentElem_divIdem hB) (isIdempotentElem_divIdem hB.tail.tail)
  have hsI : (serreCorner C k hpN ht₀ ht isBlocks_nil_seq hbs_nil hij n hn).f =
      divIdem (serreSeq t p n) [(p, n), (p + n + 1, N - n)] :=
    serreIdem_eq_divIdem hbs_nil hn
  have hS' : Graded.IsSplitting (CornerIdem.ofE (C := C) (k := k) (serreSeq t p n)).f
      (fun _ => (serreCorner C k hpN ht₀ ht isBlocks_nil_seq hbs_nil hij n hn).f)
      (fun q : ι₁ × ι₂ => a₁ q.1 * a₂ q.2) (fun q : ι₁ × ι₂ => b₂ q.2 * b₁ q.1) := by
    rw [hsI]
    have : (CornerIdem.ofE (C := C) (k := k) (serreSeq t p n)).f = divIdem (serreSeq t p n) [] := by
      rw [divIdem_nil]; rfl
    rw [this]
    exact hS
  rw [cl_kobj_split _ _ hS' (dg := fun q : ι₁ × ι₂ => dg₁ q.1 + dg₂ q.2)
    (fun q : ι₁ × ι₂ => SetLike.mul_mem_graded (ha₁ q.1) (ha₂ q.2))
    (fun q : ι₁ × ι₂ => by
      have := SetLike.mul_mem_graded (hb₂ q.2) (hb₁ q.1)
      rwa [show -dg₂ q.2 + -dg₁ q.1 = -(dg₁ q.1 + dg₂ q.2) by ring] at this)]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [T_add, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hg₁, hg₂, ← two_mul_di C i, prod_sum_T_eq, prod_sum_T_eq]
  have e1 : ∀ a b : ℤ, (T a : LaurentPolynomial ℤ) * T b = T (a + b) := fun a b => (T_add a b).symm
  rw [show (T (-(((N - n).choose 2 : ℕ) : ℤ) * di C i) * qfac (di C i) (N - n)) *
      (T (-((n.choose 2 : ℕ) : ℤ) * di C i) * qfac (di C i) n) =
      qfac (di C i) n * qfac (di C i) (N - n) *
        (T (-(((N - n).choose 2 : ℕ) : ℤ) * di C i) * T (-((n.choose 2 : ℕ) : ℤ) * di C i)) by ring,
    e1]
  congr 2; ring

include hpN ht₀ ht hij in
/-- **KL III Proposition 3.24 (first display) in `K₀`, in context**: for `i ≠ j`,
`N = d_ij + 1`, signed sequences `a`, `b`, and the Serre sequences
`S n = …i^n j i^{N-n}…` (`n ≤ N`), there are classes `Y_n` with
`[E_{a S_n b} 1_λ] = [n]_i! [N-n]_i! Y_n` and `∑_{n even} Y_n = ∑_{n odd} Y_n`.
(`Y_n = q^{-((n choose 2) + ((N-n) choose 2)) d_i} [E_a (E_{S n} 1_μ, ϕ(1_{…i^{(n)} j i^{(N-n)}…})) E_b]`,
the class of `E_a E_{+i^{(n)} +j +i^{(N-n)}} E_b 1_λ` with the shifts of KL III (3.54).) -/
theorem eC_serre (hN : N = C.dij i j + 1) {ρ μ lam : X} (a b : List (Letter I))
    (ha : wt RD (wν RD ν + μ) a = ρ) (hb : wt RD lam b = μ) :
    ∃ Yc : ℕ → K0Kar RD k ρ lam,
      (∀ n, n ≤ N → ∀ h : wt RD lam (a ++ ups (word (serreSeq t p n)) ++ b) = ρ,
        eC RD k ρ lam (a ++ ups (word (serreSeq t p n)) ++ b) h =
          (qfac (di C i) n * qfac (di C i) (N - n)) • Yc n) ∧
      ∑ n ∈ serreEvens N, Yc n = ∑ n ∈ serreOdds N, Yc n := by
  let aH := nfHom RD k ρ (wν RD ν + μ) a ha
  let bH := nfHom RD k μ lam b hb
  let ctxK : K0Kar RD k (wν RD ν + μ) μ →ₗ[LaurentPolynomial ℤ] K0Kar RD k ρ lam :=
    (K0U.wR bH).comp (K0U.wL aH)
  have hctx : ∀ A, ctxK (K0U.cl A) = K0U.cl ((wRDot (deg RD) bH).obj ((wLDot (deg RD) aH).obj A)) :=
    fun A => by simp [ctxK]
  let Yc : ℕ → K0Kar RD k ρ lam := fun n =>
    if hn : n ≤ N then
      (T (-((((n.choose 2 : ℕ) : ℤ) + (((N - n).choose 2 : ℕ) : ℤ)) * di C i)) :
        LaurentPolynomial ℤ) •
        ctxK (K0U.cl (kobj RD μ (serreCorner C k hpN ht₀ ht isBlocks_nil_seq hbs_nil hij n hn) 0))
    else 0
  refine ⟨Yc, fun n hn h => ?_, ?_⟩
  · have e1 := ctx_nfObj (k := k) ha (wt_ups_word (RD := RD) (μ := μ) (serreSeq t p n)) hb h 0
    have e2 := kobj_ofE (RD := RD) (k := k) (μ := μ) (serreSeq t p n) 0
    show K0U.cl _ = _
    rw [← e1, ← hctx, ← e2, cl_serre_split hpN ht₀ ht hij μ hn, map_smul, mul_smul]
    simp only [Yc, dif_pos hn]
  · have iso := prop324 RD k hpN ht₀ ht isBlocks_nil_seq hbs_nil hij hN μ 0
    have h := congrArg ctxK (SplitK0.of_iso iso)
    rw [SplitK0.of_biproduct, SplitK0.of_biproduct, map_sum, map_sum] at h
    rw [← Finset.sum_coe_sort (serreEvens N), ← Finset.sum_coe_sort (serreOdds N)]
    have hY : ∀ n (hn : n ≤ N), ctxK (K0U.cl (kobj RD μ (serreCorner C k hpN ht₀ ht
        isBlocks_nil_seq hbs_nil hij n hn) (0 - (((n.choose 2 : ℕ) : ℤ) +
          (((N - n).choose 2 : ℕ) : ℤ)) * di C i))) = Yc n := fun n hn => by
      rw [kobj_shift, map_smul, zero_sub]
      simp only [Yc, dif_pos hn]
    convert h using 1
    · exact Finset.sum_congr rfl fun n _ => (hY n.1 (mem_serreEvens.1 n.2).1).symm
    · exact Finset.sum_congr rfl fun n _ => (hY n.1 (mem_serreOdds.1 n.2).1).symm

end Serre

end Categorification.KL3.Diagram
