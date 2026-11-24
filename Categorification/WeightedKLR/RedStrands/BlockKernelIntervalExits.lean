/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelExits
import Categorification.WeightedKLR.RedStrands.BlockKernelSweep

/-!
# The two extreme exits across a run of black strands

Webster, arXiv:1309.3796v2, §6.1, Definition 6.3, proof after (6.21) in Lemma 6.8.
A red strand at the far end of an interval can exchange with its other endpoint by
either outside route. Peel the crossings from both ends. Disjoint end crossings
commute, and the three-strand case has distinct outer labels. Returning to a mark
at the left exit costs the product of (4.2) over the intervening blacks. This
compares these particular cuts in `K ⊗ B`, not all PBW relations at this loading.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "asc" => List.range'
local notation "desc" p:arg d:arg => List.reverse (List.range' p d)
local notation "Lw" p:arg d:arg => ((p+d) :: desc p d)
local notation "Rw" p:arg d:arg => (p :: asc (p+1) d)
local notation "leftPath" p:arg d:arg => (ψw (asc p d ++ Lw p d) : R)
local notation "rightPath" p:arg d:arg => (ψw (desc (p+1) d ++ Rw p d) : R)

private theorem left_succ (p d : ℕ) : leftPath p (d+1) = ψ p * leftPath (p+1) d * ψ p := by
  simp [List.range'_succ, mul_assoc, show p+1+d = p+(d+1) by omega]

private theorem right_succ (p d : ℕ) : rightPath p (d+1) = ψ (p+d+1) * rightPath p d * ψ (p+d+1) := by
  have hw : asc (p+1) (d+1) = asc (p+1) d ++ [p+d+1] := by simp [List.range'_concat, Nat.add_right_comm p 1 d]
  simp [hw, mul_assoc]

private theorem wrap (p : ℕ) (X Y : R) (s : KLR.Seq μ)
    (h : X * e (sadj m p • s) = Y * e (sadj m p • s)) :
    ψ p * X * ψ p * e s = ψ p * Y * ψ p * e s := by
  calc _ = ψ p * (X * e (sadj m p • s)) * ψ p := by simp only [mul_assoc, ψ_mul_e]
       _ = _ := by rw [h]; simp only [mul_assoc, ψ_mul_e]

private theorem extreme_paths (d p : ℕ) (s : KLR.Seq μ) (hd : p+d+1 < m) (a : Fin ℓ)
    (ha : s.lbl ⟨p+d+1,hd⟩ = .inr a) : leftPath p d * e s = rightPath p d * e s := by
  induction d using Nat.strong_induction_on generalizing p s with
  | _ d ih =>
    match d with
    | 0 => simp
    | 1 =>
      have hn : s.lbl ⟨p,by omega⟩ ≠ s.lbl ⟨p+2,hd⟩ := by
        intro h; have eq := lbl_inj_of_inr s a (h.trans ha) ha
        have hv := congrArg Fin.val eq; dsimp at hv; omega
      have rel := KLRAlgebra.braid (Q := stendhalQ Q Λ) p hd s
      rw [ite_eq_right (fun h => hn h.1), sub_mul, sub_eq_zero] at rel
      simpa only [List.range'_succ, List.range'_zero, List.reverse_singleton, List.singleton_append,
        ψw_cons, ψw_nil, mul_one, mul_assoc] using rel
    | d+2 =>
      let q := p+d+2
      have hq : q+1 < m := hd
      have far : Commute (ψ p : R) (ψ q) := ψ_mul_ψ _ _ (by dsimp [q]; omega)
      let ls := sadj m p • s
      let rs := sadj m q • s
      have hl : ls.lbl ⟨p+1+(d+1)+1,by omega⟩ = .inr a := by
        change (sadj m p • s).lbl _ = _
        rw [lbl_sadj, sadj_apply_of_ne _ (by dsimp; omega) (by dsimp; omega)]
        exact (lbl_eq_of_val s (by dsimp; omega) (b := ⟨p+(d+2)+1,hd⟩)).trans ha
      have hr : rs.lbl ⟨p+(d+1)+1,by omega⟩ = .inr a := by
        change (sadj m q • s).lbl ⟨q,_⟩ = _
        rw [lbl_sadj, sadj_apply_left hq]; exact ha
      have hmid : (sadj m q • ls).lbl ⟨p+1+d+1,by omega⟩ = .inr a := by
        rw [lbl_sadj, show (⟨p+1+d+1,by omega⟩ : Fin m) = ⟨q,by omega⟩ from Fin.ext (by dsimp [q]; omega),
          sadj_apply_left hq]; exact (lbl_eq_of_val ls (by dsimp [q]; omega) (b := ⟨p+1+(d+1)+1,by omega⟩)).trans hl
      have lstep := wrap Q Λ p _ _ s (ih (d+1) (by omega) (p+1) ls (by omega) hl)
      have inner := wrap Q Λ p _ _ s (wrap Q Λ q _ _ ls (ih d (by omega) (p+1) _ (by omega) hmid).symm)
      have rstep := wrap Q Λ q _ _ s (ih (d+1) (by omega) p rs (by omega) hr)
      rw [left_succ Q Λ p d] at rstep
      rw [left_succ Q Λ p (d+1), right_succ Q Λ p (d+1), lstep, right_succ Q Λ (p+1) d]
      rw [show p+1+d+1 = q by dsimp [q]; omega, inner]
      calc ψ p * (ψ q * leftPath (p+1) d * ψ q) * ψ p * e s =
             ψ q * (ψ p * leftPath (p+1) d * ψ p) * ψ q * e s := by
               simp only [mul_assoc]; rw [far.left_comm, far.symm.left_comm (e s)]
           _ = _ := rstep

variable (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (κ' : List (Fin ℓ))
local notation "A" => BraidedStendhalAlgebra k Q Λ ν
local notation "raw" => ofKLR k Q Λ ν
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "B" => RedBlock.crossingSpace (k := k) (violMk k Q Λ ν (redProj k Q Λ ν (redWord t)))
  (violMk k Q Λ ν (redProj k Q Λ ν κ'))
local notation "lower" => blockKernelLowerClass Q Λ t κ'

/-- **Dotted change between the two extreme exits** of `b i₁ … i_d a`, Webster v2,
§6.1, proof of Lemma 6.8 after (6.21). The black labels and their exponents are read
at the left exit, where they occupy the consecutive positions starting at `p`.
The mark can be there alone; the word connecting back from the other exit acts on
`x` in the higher submodule. Neither a common last factor nor division is involved. -/
theorem blockKernelIntervalBigon_slide (x : K) (p d : ℕ) (hd : p+d+1 < m) (s : KLR.Seq μ)
    (ha : s.lbl ⟨p+d+1,hd⟩ = .inr a) (hr : redWord (wordProd m (Rw p d) • s) = redWord t)
    (ex : ℕ → ℕ) (hc : ∀ z, (hz : z < d) → ∃ i,
      (wordProd m (Lw p d) • s).lbl ⟨p+z,by omega⟩ = .inl i ∧ ex z = Λ a i) (y : A) :
    (BalancedTensor.tmul x (lower (raw (blockSweepDots Q Λ p ex d (by omega) * (ψw (Lw p d) * e s)) * y)) :
      BalancedTensor k k T K B) = BalancedTensor.tmul
        (op (blockSeamWord Q Λ t (desc p d ++ desc (p+1) d)) • x) (lower (raw (ψw (Rw p d) * e s) * y)) := by
  let h := wordProd m (Lw p d) • s
  have ha' : h.lbl ⟨p+d,by omega⟩ = .inr a := by
    simp only [h, wordProd_cons, mul_smul, lbl_sadj, sadj_apply_left hd, lbl_smul, ← wordProd_reverse,
      List.reverse_reverse]
    rw [wordProd_apply_of_forall_ne (fun z hz => by have h := List.mem_range'.1 hz; dsimp; constructor <;> omega), ha]
  have cut : (e h * (ψw (Lw p d) * e s) : R) = ψw (Lw p d) * e s := by
    rw [← mul_assoc, e_mul_ψw]; simp only [h, inv_smul_smul, mul_assoc, e_mul_self]
  have sq := blockSweep_square Q Λ p d (by omega) a ex h ha' hc
  have path := extreme_paths Q Λ d p s hd a ha
  rw [blockKernelWord_slide Q Λ t a b κ' x _ _ s hr]
  apply congrArg (fun z : R => (BalancedTensor.tmul x (lower (raw z * y)) : BalancedTensor k k T K B))
  calc blockSweepDots Q Λ p ex d _ * (ψw (Lw p d) * e s) =
         (ψw (desc p d) * ψw (asc p d) * e h) * (ψw (Lw p d) * e s) := by rw [sq, mul_assoc, cut]
       _ = ψw (desc p d) * (leftPath p d * e s) := by simp only [ψw_append, mul_assoc, cut]
       _ = _ := by rw [path]; simp only [ψw_append, mul_assoc]

end Categorification.Stendhal.BraidedStendhalAlgebra
