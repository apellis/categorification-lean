/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.InterleavedPresentation
import Categorification.WeightedKLR.RedStrands.BlockKernelColumn

/-!
# Balancing the joint in a marked loading column

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8, the injectivity test after (6.21).
Project both coefficients at their exits. A lift of their signed relation to the
higher ideal kills the original tensor by balancing, including a one-sided relation.
This proves the loading-column inclusion when the joint is higher or one return
power is zero, without requiring the whole higher row to be cyclic.
-/
noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA MulOpposite
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {ν : Multiset I}
    (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
local notation "μ" => stendhalWeight ℓ ν
local notation "n" => Multiset.card μ
local notation "R" => KLRAlgebra k (stendhalQ Q Λ) μ
local notation "V" => ViolQuotient k Q Λ ν
local notation "mk" => violMk k Q Λ ν
local notation "π" => AlgHom.comp mk (ofKLR k Q Λ ν)
local notation "p" => fun v : KLR.Seq μ => π (e v)
variable (t s : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ)
local notation "ord" => isIdempotentElem_violMk_redProj k Q Λ ν (redWord t)
local notation "E" => mk (redProj k Q Λ ν (redWord t))
local notation "T" => IsIdempotentElem.Corner ord
local notation "C" => RedBlock.crossingSpace (k := k) E (p s)
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "J" => blockUpperIdeal k Q Λ ν a b (adjacentBlockRoot a b t) (redWord t)
local notation "inc" => blockKernelColumnInclusion Q Λ t a b s
local notation "leg" => fun (w : List ℕ) (v : KLR.Seq μ) => (ψw w * e v : R)
local notation "q" => fun w : List ℕ => wordProd n w • s

private theorem leg_cuts (w : List ℕ) (v : KLR.Seq μ) :
    p (wordProd n w • v) * π (leg w v) = π (leg w v) ∧ π (leg w v) * p v = π (leg w v) := by
  constructor
  · rw [← map_mul π,← mul_assoc,e_mul_ψw,inv_smul_smul,mul_assoc,e_mul_self]
  · rw [← map_mul π,mul_assoc,e_mul_self]

private theorem cut_in_order (v : KLR.Seq μ) (hv : redWord v = redWord t) : E * p v = p v ∧ p v * E = p v :=
  ⟨(map_mul mk _ _).symm.trans (congrArg mk ((redProj_mul_e _ _).trans (ite_eq_left hv))),
   (map_mul mk _ _).symm.trans (congrArg mk ((e_mul_redProj _ _).trans (ite_eq_left hv)))⟩

private def atSeam (v u : KLR.Seq μ) (hv : redWord v = redWord t) (hu : redWord u = redWord t)
    (z : V) (hl : p v * z = z) (hr : z * p u = z) : T :=
  ⟨z,(Subsemigroup.mem_corner_iff ord).2 ⟨by
    calc E*z = E*(p v*z) := congrArg (E*·) hl.symm
         _ = z := by rw [← mul_assoc,(cut_in_order Q Λ t v hv).1,hl],by
    calc z*E = (z*p u)*E := congrArg (·*E) hr.symm
         _ = z := by rw [mul_assoc,(cut_in_order Q Λ t u hu).2,hr]⟩⟩

private theorem cut_upper (v : KLR.Seq μ) (g : K) : p t * (g.1.1.1*p v) * p v = g.1.1.1*p v ∧
    g.1.1.1*p v ∈ J := by
  have h : p t * g.1.1.1 = g.1.1.1 := congrArg Subtype.val g.1.2
  exact ⟨by rw [← mul_assoc,h,mul_assoc,← map_mul π,e_mul_self],(J).mul_mem_right _ _ g.2⟩

private def loadingStack : BalancedTensor k k T P C →ₗ[k] V :=
  BalancedTensor.lift ((LinearMap.compl₂ (LinearMap.mul k V) (C).subtype).comp
    ((IsIdempotentElem.cornerVal («R» := k) ord).comp ((P).subtype.restrictScalars k)))
    (fun x r y => mul_assoc x.1.1 r.1 y.1)

private theorem exits_zero (x y : K) (l r : C)
    (h : inc (BalancedTensor.tmul x l + BalancedTensor.tmul y r) = 0) :
    x.1.1.1*l.1 + y.1.1.1*r.1 = 0 := by
  let f := (loadingStack Q Λ t s).comp inc
  exact (map_add f (BalancedTensor.tmul x l) (BalancedTensor.tmul y r)).symm.trans
    ((congrArg (loadingStack Q Λ t s) h).trans (map_zero _))

private theorem rep_of_cut (v : KLR.Seq μ) (hv : redWord v = redWord t) (z : V)
    (he : p t * z * p v = z) : (blockLoadingRep Q Λ t z).1.1 = z := by
  rw [blockLoadingRep_val]
  calc p t * z * E = p t * (p t * z * p v) * E := congrArg (fun u => p t * u * E) he.symm
       _ = z := by rw [← mul_assoc (p t),← mul_assoc (p t),← map_mul π,e_mul_self,
         mul_assoc _ (p v), (cut_in_order Q Λ t v hv).2,he]

/-- If two cut coefficients are the signed products of a common *marked* joint,
balancing kills their sum. The unprojected upper factors need not have been
supported at those cuts. -/
private theorem balance_joint (l r : C) (pL pR dL dR : T) (x y g : K)
    (hl : pL • l = l) (hr : pR • r = r) (hd : dL • l = dR • r)
    (hx : op pL • x = op dL • g) (hy : op pR • (-y) = op dR • g) :
    (BalancedTensor.tmul x l + BalancedTensor.tmul y r : BalancedTensor k k T K C) = 0 := by
  have mv (c v : T) (u : K) (w : C) (h : c • w = w) (e : op c • u = op v • g) :
      (BalancedTensor.tmul u w : BalancedTensor k k T K C) = BalancedTensor.tmul g (v • w) := by
    calc _ = BalancedTensor.tmul (op c • u) w := by rw [BalancedTensor.op_smul_tmul,h]
         _ = _ := by rw [e,BalancedTensor.op_smul_tmul]
  have neg : (BalancedTensor.tmul (-y) r : BalancedTensor k k T K C) = -BalancedTensor.tmul y r :=
    map_neg ((BalancedTensor.mkBil k k T K C).flip r) y
  exact add_eq_zero_iff_eq_neg.mpr ((mv _ _ x l hl hx).trans ((congrArg (BalancedTensor.tmul g) hd).trans
    ((mv _ _ (-y) r hr hy).symm.trans neg)))

variable (j : ℕ) (hj : j+2 < (stendhalWeight ℓ ν).card)
local notation "L" => [j+1,j]
local notation "U" => [j,j+1]
local notation "D" => [j,j+1,j]

private theorem marked_exits_balance {i : I} (hb : s.lbl ⟨j,by omega⟩ = .inr b)
    (hi : s.lbl ⟨j+1,by omega⟩ = .inl i) (ha : s.lbl ⟨j+2,hj⟩ = .inr a)
    (lo : redWord (q L) = redWord t) (ro : redWord (q U) = redWord t) (ho : redWord (q D) = redWord t)
    (x y : K) (u : V) (hm : u ∈ J) (he : p t*u*p (q D) = u)
    (ul : u*π (leg [j] (q L)) = x.1.1.1*p (q L)) (ur : u*π (leg [j+1] (q U)) = -(y.1.1.1*p (q U))) :
    (BalancedTensor.tmul x (interleavedLeg Q Λ s t L lo) + BalancedTensor.tmul y (interleavedLeg Q Λ s t U ro) :
      BalancedTensor k k T K C) = 0 := by
  have sq (v : KLR.Seq μ) : p v * p v = p v := by rw [← map_mul π,e_mul_self]
  let proj (v : KLR.Seq μ) (hv : redWord v = redWord t) := atSeam Q Λ t v v hv hv (p v) (sq v) (sq v)
  have cut (w : List ℕ) (v : KLR.Seq μ) (hw : wordProd n w • v = q D) :
      p (q D) * π (leg w v) = π (leg w v) := hw ▸ (leg_cuts Q Λ w v).1
  have left : wordProd n [j] • q L = q D := by simp only [wordProd_cons,wordProd_nil,mul_one,mul_smul]
  have right : wordProd n [j+1] • q U = q D := by
    simpa only [wordProd_cons,wordProd_nil,mul_one,mul_smul] using (braid_smul hj s).symm
  let dL := atSeam Q Λ t (q D) (q L) ho lo (π (leg [j] (q L))) (cut _ _ left) (leg_cuts Q Λ _ _).2
  let dR := atSeam Q Λ t (q D) (q U) ho ro (π (leg [j+1] (q U))) (cut _ _ right) (leg_cuts Q Λ _ _).2
  have val := rep_of_cut Q Λ t (q D) ho u he
  let g : K := ⟨blockLoadingRep Q Λ t u,by change (blockLoadingRep Q Λ t u).1.1 ∈ J; rwa [val]⟩
  apply balance_joint Q Λ t s a b _ _ (proj _ lo) (proj _ ro) dL dR x y g
  · exact Subtype.ext (leg_cuts Q Λ L s).1
  · exact Subtype.ext (leg_cuts Q Λ U s).1
  · apply Subtype.ext; change π (leg [j] (q L)) * π (leg L s) = π (leg [j+1] (q U)) * π (leg U s)
    rw [← map_mul π,← map_mul π]; apply congrArg π
    have h := ExitPBW.exit_rows Q Λ s j hj hb hi ha [] 1
    simpa only [ψw_nil,map_one,one_mul] using h.2.1.trans h.2.2.1.symm
  · apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change x.1.1.1 * p (q L) = (blockLoadingRep Q Λ t u).1.1 * π (leg [j] (q L)); rw [val,ul]
  · apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    change (-y.1.1.1) * p (q U) = (blockLoadingRep Q Λ t u).1.1 * π (leg [j+1] (q U))
    rw [val,ur,neg_mul]

/-- For a bottom loading `b i a`, lifting the signed joint of two marked exit
coefficients to the higher ideal suffices for the column inclusion in (6.21).
The lift can differ from the original witness by any element killed by both legs. -/
private theorem marked_column_of_joint_lift {i : I} {Lr Mr : List (Fin ℓ)}
    (hQ : KLRSymm Q) (ht : redWord t = Lr ++ a :: b :: Mr)
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (ho : redWord (q D) = redWord t)
    (liftJoint : ∀ x y : V, p t * x * p (q L) = x → p t * y * p (q U) = y →
      x ∈ J → y ∈ J → x * π (leg L s) + y * π (leg U s) = 0 →
      ∃ u ∈ J, p t * u * p (q D) = u ∧ u * π (leg [j] (q L)) = x ∧
        u * π (leg [j+1] (q U)) = -y) :
    Function.Injective inc := by
  have hL : sadj n j • q D = q L := by simp only [wordProd_cons,wordProd_nil,mul_one,mul_smul,sadj_smul_smul]
  have hR : sadj n (j+1) • q D = q U := by
    simp only [wordProd_cons,wordProd_nil,mul_one,mul_smul,braid_smul hj s,sadj_smul_smul]
  have hblack : (q D).lbl ⟨j+1,by omega⟩ = .inl i := (braid_smul_apply_one hj s).trans hi
  have lo : redWord (q L) = redWord t := hL ▸ (redWord_sadj_smul (q D) (show j+1<n by omega) (by rw [hblack]; simp)).trans ho
  have ro : redWord (q U) = redWord t := hR ▸ (redWord_sadj_smul (q D) hj (by rw [hblack]; simp)).trans ho
  let l := interleavedLeg Q Λ s t L lo; let r := interleavedLeg Q Λ s t U ro
  rw [← LinearMap.ker_eq_bot,LinearMap.ker_eq_bot']; intro z hz
  obtain ⟨x,y,rfl⟩ := exists_interleavedKernelColumn_exits Q Λ s j hj t a b hQ ht hb ha lo ro z
  have eq := exits_zero Q Λ t s a b x y l r hz
  have lc := (leg_cuts Q Λ L s).1; have rc := (leg_cuts Q Λ U s).1
  obtain ⟨hx,mx⟩ := cut_upper Q Λ t a b (q L) x; obtain ⟨hy,my⟩ := cut_upper Q Λ t a b (q U) y
  have rel : (x.1.1.1*p (q L))*π (leg L s) + (y.1.1.1*p (q U))*π (leg U s) = 0 := by
    rwa [mul_assoc,lc,mul_assoc,rc]
  obtain ⟨u,hm,he,ul,ur⟩ := liftJoint _ _ hx hy mx my rel
  exact marked_exits_balance Q Λ t s a b j hj hb hi ha lo ro ho x y u hm he ul ur

/-- The marked column inclusion for a higher joint or a zero return exponent.
Webster v2, §6.1, proof of Lemma 6.8 after (6.21), restricted to `b i a`.
The disjunction is a limitation of this intermediate result. Arbitrary exterior
strands and one-sided exit relations are allowed. -/
theorem interleaved_markedColumn_injective {i : I} {Lr Mr : List (Fin ℓ)}
    (hQ : KLRSymm Q) (ht : redWord t = Lr ++ a :: b :: Mr)
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (ho : redWord (q D) = redWord t)
    (hmark : adjacentBlockRoot a b t < adjacentBlockRoot a b (q D) ∨ min (Λ a i) (Λ b i) = 0) :
    Function.Injective inc := by
  apply marked_column_of_joint_lift Q Λ t s a b j hj hQ ht hb hi ha ho
  intro x y hx hy mx my rel
  rcases hmark with hh | hzero
  · exact interleaved_marked_joint_of_higher Q Λ s j hj hQ t ht hb hi ha ho hh x y hx hy rel
  · obtain ⟨u,hu,hl,hr,hm⟩ :=
      interleaved_joint_dot_mem Q Λ s j hj hQ t ht hb hi ha x y hx hy mx my rel
    rw [hzero,pow_zero,map_one,mul_one] at hm
    exact ⟨u,hm,hu,hl,hr⟩

/-- Injectivity of the right joint leg on the partially standardized corner suffices
for the interleaved column of (6.21). The hypothesis says that a supported
coefficient whose right exit is in the higher ideal already belongs to that ideal. -/
theorem interleaved_markedColumn_injective_of_right_leg {i : I} {Lr Mr : List (Fin ℓ)}
    (hQ : KLRSymm Q) (ht : redWord t = Lr ++ a :: b :: Mr)
    (hb : s.lbl ⟨j,by omega⟩ = .inr b) (hi : s.lbl ⟨j+1,by omega⟩ = .inl i)
    (ha : s.lbl ⟨j+2,hj⟩ = .inr a) (ho : redWord (q D) = redWord t)
    (rightLeg : ∀ u : V, p t * u * p (q D) = u →
      u * π (leg [j+1] (q U)) ∈ J → u ∈ J) :
    Function.Injective inc := by
  apply marked_column_of_joint_lift Q Λ t s a b j hj hQ ht hb hi ha ho
  intro x y hx hy _ my rel
  obtain ⟨u,hu,hl,hr⟩ :=
    (interleaved_quotient_relation_iff Q Λ s j hj hQ t ht hb hi ha x y hx hy).mp rel
  exact ⟨u,rightLeg u hu (by rw [hr]; exact (J).neg_mem my),hu,hl,hr⟩

end Categorification.Stendhal.BraidedStendhalAlgebra
