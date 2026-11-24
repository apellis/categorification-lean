/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelColumn

/-!
# Returning an interleaved column to consecutive reds

Webster, arXiv:1309.3796v2, §6.1, kernel test following (6.21) of Lemma 6.8.
Moving the second exchanged red past the intervening blacks and back costs a
product of black-dot powers, one bigon (4.2) per black. On the actual kernel tensor
the outward map lands in the consecutive column. Thus the dot product annihilates
the column kernel; it cannot in general be cancelled in the violated quotient.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} {k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "π" => AlgHom.comp (violMk k Q Λ ν) (ofKLR k Q Λ ν)
local notation "up" => List.range'

/-- Dot product at positions `p,…,p+d-1` from returning the red along a run of `d` blacks. -/
def blockSweepDots (p : ℕ) (ex : ℕ → ℕ) : (d : ℕ) → p+d < m → R
  | 0, _ => 1
  | d+1, h => blockSweepDots p ex d (by omega) * x ⟨p+d,by omega⟩ ^ ex d

local notation "D" => blockSweepDots Q Λ (ν := ν)

private theorem dots_far (p : ℕ) (ex : ℕ → ℕ) (d : ℕ) (hd : p+d < m) (j : ℕ) (hj : p+d ≤ j) :
    Commute (D p ex d hd) (ψ j) := by
  induction d with
  | zero => exact Commute.one_left _
  | succ d ih =>
    apply Commute.mul_left (ih (by omega) (by omega))
    exact (show Commute (x (⟨p+d,by omega⟩ : Fin m) : R) (ψ j) from
      x_mul_ψ _ _ (by dsimp; omega) (by dsimp; omega)).pow_left _

private theorem dots_unit (p d : ℕ) (hd : p+d < m) : D p (fun _ => 0) d hd = 1 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [blockSweepDots, pow_zero, mul_one, ih]

/-- Red–black bigons along the interval, Webster v2, (4.2): going left through the
black strands and returning evaluates to the indicated monomial at the original loading. -/
theorem blockSweep_square (p d : ℕ) (hd : p+d < m) (a : Fin ℓ) (ex : ℕ → ℕ) (s : KLR.Seq μ)
    (ha : s.lbl ⟨p+d,hd⟩ = .inr a)
    (hc : ∀ z, (hz : z < d) → ∃ i, s.lbl ⟨p+z,by omega⟩ = .inl i ∧ ex z = Λ a i) :
    (ψw (up p d).reverse * ψw (up p d) * e s : R) = D p ex d hd * e s := by
  induction d generalizing s with
  | zero => simp [blockSweepDots]
  | succ d ih =>
    let j := p+d
    let u := sadj m j • s
    have hj : j+1 < m := by dsimp [j]; omega
    have hu : u.lbl ⟨p+d,by omega⟩ = .inr a := by
      change (sadj m j • s).lbl ⟨j,_⟩ = _
      rw [lbl_smul, sadj_inv, sadj_apply_left hj]; exact ha
    have hc' (z : ℕ) (hz : z < d) : ∃ i, u.lbl ⟨p+z,by omega⟩ = .inl i ∧ ex z = Λ a i := by
      change ∃ i, (sadj m j • s).lbl _ = .inl i ∧ _
      rw [lbl_smul, sadj_inv, sadj_apply_of_ne _ (by dsimp [j]; omega) (by dsimp [j]; omega)]
      exact hc z (by omega)
    have prev := ih (by omega) u hu hc'
    obtain ⟨i,hi,he⟩ := hc d (by omega)
    have sq := KLRAlgebra.ψ_sq (Q := stendhalQ Q Λ) j hj s
    have hjRed : s.lbl ⟨j+1,hj⟩ = .inr a := ha
    rw [hi,hjRed] at sq
    simp only [reduceCtorEq, ↓reduceIte, stendhalQ_inl_inr, ncEval_x2, map_pow,
      MvPolynomial.rename_X, pol_X, Matrix.cons_val_zero, ← he] at sq
    have moved : ψ j * e s = (e u * ψ j : R) := ψ_mul_e _ _
    have far := (dots_far (ν := ν) Q Λ p ex d (by omega) j le_rfl).symm.eq
    have words : up p (d+1) = up p d ++ [j] := by simp [List.range'_concat,j]
    rw [words, List.reverse_append, List.reverse_singleton, ψw_append, ψw_append, ψw_cons, ψw_nil, mul_one]
    calc ψ j * ψw (up p d).reverse * (ψw (up p d) * ψ j) * e s =
          ψ j * ((ψw (up p d).reverse * ψw (up p d) * e u) * ψ j) := by simp only [mul_assoc,moved]
         _ = D p ex d (by omega) * (ψ j * ψ j * e s) := by rw [prev]; simp only [mul_assoc,moved]; rw [← mul_assoc, far, mul_assoc]
         _ = _ := by rw [sq]; simp only [blockSweepDots, mul_assoc, j]

variable (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ)
local notation "E" => violMk k Q Λ ν (redProj k Q Λ ν (redWord t))
local notation "C" s:arg => RedBlock.crossingSpace (k := k) E
  (violMk k Q Λ ν (ofKLR k Q Λ ν (e s)))
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "inc" => blockKernelColumnInclusion Q Λ t a b
private local instance {S : Type*} [Ring S] [Algebra k S] {g h : S} (hg : IsIdempotentElem g) :
    IsScalarTower k hg.Corner (RedBlock.crossingSpace (k := k) g h) where
  smul_assoc c r x := Subtype.ext (smul_mul_assoc c r.1 x.1)

private def columnTail (s u : KLR.Seq μ) (v : R) : C s →ₗ[T] C u where
  toFun y := ⟨y.1 * π (v * e u), by rw [← mul_assoc,y.2.1], by
    change y.1 * π (v * e u) * π (e u) = _
    rw [mul_assoc, ← map_mul, mul_assoc, e_mul_self]⟩
  map_add' x y := Subtype.ext (add_mul x.1 y.1 _)
  map_smul' r y := Subtype.ext (mul_assoc r.1 y.1 _)

local notation "tailMap" => columnTail Q Λ t
local notation "changeK" => BalancedTensor.mapRight (k := k) («B» := k) (M := K)
local notation "changeP" => BalancedTensor.mapRight (k := k) («B» := k) (M := P)

private theorem column_square (s v : KLR.Seq μ) (f : C s →ₗ[T] C v) :
    (inc v).comp (changeK f) = (changeP f).comp (inc s) := BalancedTensor.ext fun _ _ => rfl

private theorem change_comp (s v : KLR.Seq μ) (f : C s →ₗ[T] C v) (g : C v →ₗ[T] C s)
    (h : C s →ₗ[T] C s) (eq : g.comp f = h) : (changeK g).comp (changeK f) = changeK h :=
  BalancedTensor.ext fun x y => congrArg (fun z : C s => (BalancedTensor.tmul x z : BalancedTensor k k T K (C s)))
    (LinearMap.congr_fun eq y)

private theorem change_unit (s : KLR.Seq μ) (f : C s →ₗ[T] C s) (eq : f = LinearMap.id) :
    changeK f = LinearMap.id := BalancedTensor.ext fun x y =>
  congrArg (fun z : C s => (BalancedTensor.tmul x z : BalancedTensor k k T K (C s))) (LinearMap.congr_fun eq y)

private theorem ker_le_of_roundtrip {X Y U V : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    (i : X →ₗ[k] Y) (j : U →ₗ[k] V) (f : X →ₗ[k] U) (g : U →ₗ[k] X) (h : Y →ₗ[k] V)
    (op' : X →ₗ[k] X) (hj : Function.Injective j) (hn : j.comp f = h.comp i) (hd : g.comp f = op') :
    LinearMap.ker i ≤ LinearMap.ker op' := by
  intro z hz
  have ih : i z = 0 := hz
  have eq : j (f z) = 0 := (LinearMap.congr_fun hn z).trans (by simp [ih])
  have hf : f z = 0 := hj (eq.trans (map_zero _).symm)
  change op' z = 0
  rw [← hd, LinearMap.comp_apply, hf, map_zero]

/-- The product of black dots acts at the bottom on `K ⊗_T B e(s)`. -/
def blockKernelColumnDots (s : KLR.Seq μ) (p d : ℕ) (h : p+d < m) (ex : ℕ → ℕ) :=
  changeK (tailMap s s (D p ex d h))

/-- **Dot annihilator of an interleaved column kernel** (Webster v2, (4.2) and the
kernel test after (6.21)). The exchanged loading `s` has `d` intervening blacks;
pulling `a` left through them gives the consecutive exchanged loading. The product
uses their individual multiplicities against `a`, with no regularity hypothesis. -/
theorem ker_blockKernelColumnInclusion_le_ker_dots (hQ : KLRSymm Q)
    (L M : List (Fin ℓ)) (ht : redWord t = L ++ a :: b :: M)
    (u : KLR.Seq μ) (hu : redWord u = redWord t) (n d : ℕ) (hd : n+1+d < m)
    (ha : u.lbl ⟨n,by omega⟩ = .inr a) (hb : u.lbl ⟨n+1,by omega⟩ = .inr b)
    (s : KLR.Seq μ) (hs : wordProd m (up (n+1) d) • s = sadj m n • u)
    (hs' : s.lbl ⟨n+1+d,hd⟩ = .inr a) (ex : ℕ → ℕ)
    (hc : ∀ z, (hz : z < d) → ∃ i, s.lbl ⟨n+1+z,by omega⟩ = .inl i ∧ ex z = Λ a i) :
    LinearMap.ker (inc s) ≤ LinearMap.ker (blockKernelColumnDots Q Λ t a b s (n+1) d hd ex) := by
  let v := sadj m n • u
  let w := up (n+1) d
  let f := tailMap s v (ψw w.reverse)
  let g := tailMap v s (ψw w)
  have comp : g.comp f = tailMap s s (D (n+1) ex d hd) := by
    apply LinearMap.ext; intro y; apply Subtype.ext
    change y.1 * π (ψw w.reverse * e v) * π (ψw w * e s) = _
    have cut : (e v * (ψw w * e s) : R) = ψw w * e s := by
      have hv : wordProd m w • s = v := hs
      rw [← hv, ← mul_assoc, e_mul_ψw, inv_smul_smul, mul_assoc, e_mul_self]
    rw [mul_assoc, ← map_mul, mul_assoc (ψw w.reverse), cut, ← mul_assoc (ψw w.reverse),
      blockSweep_square Q Λ (n+1) d hd a ex s hs' hc]; rfl
  have inj := blockKernelColumnInclusion_injective Q Λ t a b v hQ L M ht u hu n (by omega) ha hb rfl
  exact ker_le_of_roundtrip (k := k) (X := BalancedTensor k k T K (C s)) (Y := BalancedTensor k k T P (C s))
    (U := BalancedTensor k k T K (C v)) (V := BalancedTensor k k T P (C v)) (inc s) (inc v)
    (changeK f) (changeK g) (changeP f) (blockKernelColumnDots Q Λ t a b s (n+1) d hd ex) inj
    (column_square Q Λ t a b s v f) (change_comp Q Λ t a b s v f g _ comp)

private theorem injective_of_unit_operator {X Y : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (i : X →ₗ[k] Y) (f : X →ₗ[k] X)
    (h : LinearMap.ker i ≤ LinearMap.ker f) (hf : f = LinearMap.id) : Function.Injective i := by
  rw [← LinearMap.ker_eq_bot]; exact le_bot_iff.mp (h.trans (by rw [hf, LinearMap.ker_id]))

/-- **Interleaved column injectivity for zero red–black pairings**, a restricted
case of Webster v2, Lemma 6.8 after (6.21). All intervening blacks pair to zero
with the red moved left. No other pairing or spectator is restricted. -/
theorem blockKernelColumnInclusion_injective_of_zero_pairings (hQ : KLRSymm Q)
    (L M : List (Fin ℓ)) (ht : redWord t = L ++ a :: b :: M)
    (u : KLR.Seq μ) (hu : redWord u = redWord t) (n d : ℕ) (hd : n+1+d < m)
    (ha : u.lbl ⟨n,by omega⟩ = .inr a) (hb : u.lbl ⟨n+1,by omega⟩ = .inr b)
    (s : KLR.Seq μ) (hs : wordProd m (up (n+1) d) • s = sadj m n • u)
    (hs' : s.lbl ⟨n+1+d,hd⟩ = .inr a)
    (hc : ∀ z, (hz : z < d) → ∃ i, s.lbl ⟨n+1+z,by omega⟩ = .inl i ∧ Λ a i = 0) :
    Function.Injective (inc s) := by
  have H := ker_blockKernelColumnInclusion_le_ker_dots Q Λ t a b hQ L M ht u hu n d hd ha hb s hs hs'
    (fun _ => 0) (fun z hz => (hc z hz).imp fun _ hi => ⟨hi.1,hi.2.symm⟩)
  have one : tailMap s s (D (n+1) (fun _ => 0) d hd) = LinearMap.id := by
    rw [dots_unit]; apply LinearMap.ext; intro y; apply Subtype.ext
    change y.1 * π (1 * e s) = y.1; rw [one_mul]; exact y.2.2
  exact injective_of_unit_operator (k := k) (X := BalancedTensor k k T K (C s)) (Y := BalancedTensor k k T P (C s))
    (inc s) (blockKernelColumnDots Q Λ t a b s (n+1) d hd fun _ => 0) H (change_unit Q Λ t a b s _ one)

end Categorification.Stendhal.BraidedStendhalAlgebra
