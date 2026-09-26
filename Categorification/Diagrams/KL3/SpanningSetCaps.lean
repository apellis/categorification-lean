/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SpanningSetLocal

/-!
# Elimination of caps modulo lower terms

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3, proof
of Proposition 3.11 ("arbitrary homotopies of colored dotted diagrams modulo lower order terms,
i.e., terms with fewer crossings, fewer circles, etc.", following A. Lauda, arXiv:0803.3652v3,
§8) and §3.2.4 (the ideal of diagrams factoring through shorter sequences).

Fix a weight `μ` and a source signed sequence `w₀`. A **move** (`Mv`) is a dot, a crossing of two
adjacent strands (`xLay`: upward, downward or sideways), or a cup, placed between strands. A
**move diagram** is a composite of moves starting at `E_{w₀} 1_μ`: a diagram without caps (the
sideways crossings being counted as single moves). We show that every normal-form diagram
`E_{w₀} 1_μ ⟶ E_v 1_μ` with at most `c` crossings is a linear combination of move diagrams with at
most `c` crossings followed by bubble monomials on the far right, modulo 2-morphisms factoring
through sequences shorter than `w₀` (`thruShort`).

## The argument

By induction on the number of crossings, and then on the number of layers: a diagram is a
diagram with one layer less followed by a dot, a crossing, a cup or a cap. Only caps need work.
A cap on top of a move diagram is pushed down: more generally, for a cap joining two strands `A`
and `B` over which a block `S` of strands passes (`B` moves left across `S` and then meets `A`;
`capBlk`), we push the block down through the top move of the move diagram:

* moves away from the block commute with it;
* a strand entering the block from the left or right joins `S` (pitchfork moves);
* a crossing inside `S` passes the block by Reidemeister 3;
* a crossing of `A` or `B` with the adjacent strand of `S`, or a cup creating a strand of `S`
  and `A` or `B`, or both legs inside `S`, give a double crossing or a curl, hence lower terms;
* a cup creating `A` (or `B`) with a strand outside the block cancels the cap (zigzag),
  leaving a move diagram;
* a cup creating `A` and `B` (and `S = []`) closes a bubble, which slides to the far right;
* at the bottom (`A` and `B` strands of `w₀`) the diagram factors through a shorter sequence.

All the lower terms have fewer crossings and are handled by the induction on crossings.

## Main results

* `Mv`, `MvChain`, `mvLay`: moves and move diagrams; `MvSp`, `thruShort`, `CapTarget`.
* `lmLc`, `lmRc`, `capBlk`: a strand moving across a block of strands, and the cap block.

The local relations of the cap block are in `Categorification.Diagrams.KL3.SpanningSetBlock`,
and the elimination of caps (`capElim`: every diagram with at most `c` crossings lies in
`CapTarget c`, simply-laced Cartan data) in `Categorification.Diagrams.KL3.SpanningSetElim`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Moves -/

/-- A move: a dot, a crossing of two adjacent strands, or a cup, between the strands `u` and
`v`. -/
inductive Mv (I : Type u)
  | dot (u : List (Letter I)) (l : Letter I) (v : List (Letter I))
  | cross (u : List (Letter I)) (l₁ l₂ : Letter I) (v : List (Letter I))
  | cup (u : List (Letter I)) (l : Letter I) (v : List (Letter I))

namespace Mv

/-- The layers of a move. -/
def lay : Mv I → List (LayerData I)
  | dot u l v => [(u, .dot l, v)]
  | cross u l₁ l₂ v => (xLay l₁ l₂).map (whL u v)
  | cup u l v => [(u, .cup l, v)]

/-- The bottom boundary of a move. -/
def src : Mv I → List (Letter I)
  | dot u l v => u ++ [l] ++ v
  | cross u l₁ l₂ v => u ++ [l₁, l₂] ++ v
  | cup u _ v => u ++ v

/-- The top boundary of a move. -/
def tgt : Mv I → List (Letter I)
  | dot u l v => u ++ [l] ++ v
  | cross u l₁ l₂ v => u ++ [l₂, l₁] ++ v
  | cup u l v => u ++ [l, l.dual] ++ v

theorem sChain_lay (m : Mv I) : SChain m.src m.lay m.tgt := by
  cases m with
  | dot u l v => exact ⟨rfl, by simp [tgt]⟩
  | cross u l₁ l₂ v => simpa [src, tgt, lay] using (sChain_xLay l₁ l₂).whisk u v
  | cup u l v => exact ⟨by simp [src], by simp [tgt]⟩

theorem ccnt_lay (m : Mv I) : ccnt m.lay = match m with | cross .. => 1 | _ => 0 := by
  cases m <;> simp [lay, ccnt_map_whL]

end Mv

/-- The layers of a list of moves. -/
def mvLay (ms : List (Mv I)) : List (LayerData I) := (ms.map Mv.lay).flatten

@[simp] theorem mvLay_nil : mvLay ([] : List (Mv I)) = [] := rfl

theorem mvLay_append (ms ns : List (Mv I)) : mvLay (ms ++ ns) = mvLay ms ++ mvLay ns := by
  simp [mvLay]

theorem mvLay_singleton (m : Mv I) : mvLay [m] = m.lay := by simp [mvLay]

/-- A chain of moves from `s` to `t`. -/
def MvChain : List (Letter I) → List (Mv I) → List (Letter I) → Prop
  | s, [], t => s = t
  | s, m :: ms, t => s = m.src ∧ MvChain m.tgt ms t

theorem MvChain.sChain : ∀ {s t : List (Letter I)} {ms : List (Mv I)}, MvChain s ms t →
    SChain s (mvLay ms) t
  | _, _, [], h => h
  | _, _, m :: ms, ⟨rfl, h⟩ => by
    simpa [mvLay] using m.sChain_lay.append h.sChain

theorem MvChain.snoc {s : List (Letter I)} {ms : List (Mv I)} {m : Mv I}
    (h : MvChain s ms m.src) : MvChain s (ms ++ [m]) m.tgt := by
  induction ms generalizing s with
  | nil => exact ⟨h, rfl⟩
  | cons m' ms ih => exact ⟨h.1, ih h.2⟩

theorem MvChain.of_snoc {s t : List (Letter I)} {ms : List (Mv I)} {m : Mv I}
    (h : MvChain s (ms ++ [m]) t) : MvChain s ms m.src ∧ m.tgt = t := by
  induction ms generalizing s with
  | nil => exact ⟨h.1, h.2⟩
  | cons m' ms ih => obtain ⟨h₁, h₂⟩ := ih h.2; exact ⟨⟨h.1, h₁⟩, h₂⟩

/-! ## Move diagrams and the ideal of diagrams factoring through shorter sequences -/

variable (RD k) in
/-- Move diagrams from `E_{w₀} 1_μ` to `E_v 1_μ` with at most `c` crossings, followed by an element of
the image of `Π_μ` on the far right. -/
def MvSp (μ : X) (w₀ v : List (Letter I)) (c : ℕ) :
    Submodule k ((pres RD k).obj (ob RD μ w₀) ⟶ (pres RD k).obj (ob RD μ v)) :=
  Submodule.span k {f | ∃ (ms : List (Mv I)) (β : End ((pres RD k).obj (ob RD μ []))),
    MvChain w₀ ms v ∧ ccnt (mvLay ms) ≤ c ∧ IsBub RD k μ β ∧
      f = dg RD k μ w₀ v (mvLay ms) ≫ bubAt RD k μ v β}

variable (RD k) in
/-- 2-morphisms `E_{w₀} 1_μ ⟶ E_v 1_μ` factoring through a sequence shorter than `w₀`. -/
def thruShort (μ : X) (w₀ v : List (Letter I)) :
    Submodule k ((pres RD k).obj (ob RD μ w₀) ⟶ (pres RD k).obj (ob RD μ v)) :=
  Submodule.span k {f | ∃ (u : List (Letter I)) (g : (pres RD k).obj (ob RD μ w₀) ⟶
    (pres RD k).obj (ob RD μ u)) (h : (pres RD k).obj (ob RD μ u) ⟶ (pres RD k).obj (ob RD μ v)),
      u.length < w₀.length ∧ f = g ≫ h}

variable (RD k) in
/-- The target of the elimination of caps. -/
def CapTarget (μ : X) (w₀ v : List (Letter I)) (c : ℕ) :
    Submodule k ((pres RD k).obj (ob RD μ w₀) ⟶ (pres RD k).obj (ob RD μ v)) :=
  MvSp RD k μ w₀ v c ⊔ thruShort RD k μ w₀ v

section Closure

variable {μ : X} {w₀ : List (Letter I)}

theorem mvSp_mono {v : List (Letter I)} {c c' : ℕ} (h : c ≤ c') :
    MvSp RD k μ w₀ v c ≤ MvSp RD k μ w₀ v c' :=
  Submodule.span_mono fun _ ⟨ms, β, h₁, h₂, h₃, e⟩ => ⟨ms, β, h₁, h₂.trans h, h₃, e⟩

theorem capTarget_mono {v : List (Letter I)} {c c' : ℕ} (h : c ≤ c') :
    CapTarget RD k μ w₀ v c ≤ CapTarget RD k μ w₀ v c' :=
  sup_le_sup_right (mvSp_mono h) _

theorem thruShort_comp {v v' : List (Letter I)} {f} (hf : f ∈ thruShort RD k μ w₀ v)
    (h : (pres RD k).obj (ob RD μ v) ⟶ (pres RD k).obj (ob RD μ v')) :
    f ≫ h ∈ thruShort RD k μ w₀ v' := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, g, h', hu, rfl⟩ := hf
    exact Submodule.subset_span ⟨u, g, h' ≫ h, hu, by rw [Category.assoc]⟩
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem mvSp_comp_mv {v : List (Letter I)} {c : ℕ} {f} (hf : f ∈ MvSp RD k μ w₀ v c) (m : Mv I)
    (hm : m.src = v) :
    f ≫ dg RD k μ v m.tgt m.lay ∈ MvSp RD k μ w₀ m.tgt (c + ccnt m.lay) := by
  subst hm
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ms, β, hc, hcc, hβ, rfl⟩ := hf
    refine Submodule.subset_span ⟨ms ++ [m], β, hc.snoc, ?_, hβ, ?_⟩
    · rw [mvLay_append, mvLay_singleton, ccnt_append]; omega
    · rw [Category.assoc, bubAt_comm, ← Category.assoc, dg_comp hc.sChain m.sChain_lay,
        mvLay_append, mvLay_singleton]
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem capTarget_comp_mv {v : List (Letter I)} {c : ℕ} {f} (hf : f ∈ CapTarget RD k μ w₀ v c)
    (m : Mv I) (hm : m.src = v) :
    f ≫ dg RD k μ v m.tgt m.lay ∈ CapTarget RD k μ w₀ m.tgt (c + ccnt m.lay) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
  rw [Preadditive.add_comp]
  exact Submodule.add_mem_sup (mvSp_comp_mv ha m hm) (thruShort_comp hb _)

theorem mvSp_comp_bubAt {v : List (Letter I)} {c : ℕ} {f} (hf : f ∈ MvSp RD k μ w₀ v c)
    {β : End ((pres RD k).obj (ob RD μ []))} (hβ : IsBub RD k μ β) :
    f ≫ bubAt RD k μ v β ∈ MvSp RD k μ w₀ v c := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ms, β', hc, hcc, hβ', rfl⟩ := hf
    refine Submodule.subset_span ⟨ms, β' ≫ β, hc, hcc, hβ'.comp hβ, ?_⟩
    rw [Category.assoc, bubAt_comp]
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

theorem capTarget_comp_bubAt {v : List (Letter I)} {c : ℕ} {f}
    (hf : f ∈ CapTarget RD k μ w₀ v c) {β : End ((pres RD k).obj (ob RD μ []))}
    (hβ : IsBub RD k μ β) : f ≫ bubAt RD k μ v β ∈ CapTarget RD k μ w₀ v c := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
  rw [Preadditive.add_comp]
  exact Submodule.add_mem_sup (mvSp_comp_bubAt ha hβ) (thruShort_comp hb _)

theorem dg_mvLay_mem_mvSp {v : List (Letter I)} {c : ℕ} {ms : List (Mv I)}
    (hc : MvChain w₀ ms v) (hcc : ccnt (mvLay ms) ≤ c) :
    dg RD k μ w₀ v (mvLay ms) ∈ MvSp RD k μ w₀ v c :=
  Submodule.subset_span ⟨ms, 𝟙 _, hc, hcc, IsBub.id, by rw [bubAt_id, Category.comp_id]⟩

theorem dg_mem_thruShort {v u : List (Letter I)} (L M : List (LayerData I))
    (hu : u.length < w₀.length) :
    dg RD k μ w₀ u L ≫ dg RD k μ u v M ∈ thruShort RD k μ w₀ v :=
  Submodule.subset_span ⟨u, _, _, hu, rfl⟩

end Closure

/-! ## A strand moving across a block of strands -/

/-- The strand `b` moving left across the strands `S`: `S ++ [b] ⟶ [b] ++ S`. -/
def lmLc : List (Letter I) → Letter I → List (LayerData I)
  | [], _ => []
  | s :: S, b => (lmLc S b).map (whL [s] []) ++ (xLay s b).map (whL [] S)

/-- The strand `a` moving right across the strands `S`: `[a] ++ S ⟶ S ++ [a]`. -/
def lmRc (a : Letter I) : List (Letter I) → List (LayerData I)
  | [] => []
  | s :: S => (xLay a s).map (whL [] S) ++ (lmRc a S).map (whL [s] [])

theorem sChain_lmLc : ∀ (S : List (Letter I)) (b : Letter I), SChain (S ++ [b]) (lmLc S b) (b :: S)
  | [], _ => rfl
  | s :: S, b => by
    unfold lmLc
    refine (by simpa using (sChain_lmLc S b).whisk [s] [] : SChain ((s :: S) ++ [b])
      ((lmLc S b).map (whL [s] [])) ([s, b] ++ S)).append ?_
    simpa using (sChain_xLay s b).whisk [] S

theorem sChain_lmRc (a : Letter I) : ∀ S : List (Letter I), SChain (a :: S) (lmRc a S) (S ++ [a])
  | [] => rfl
  | s :: S => by
    unfold lmRc
    refine (by simpa using (sChain_xLay a s).whisk [] S : SChain (a :: s :: S)
      ((xLay a s).map (whL [] S)) (s :: a :: S)).append ?_
    simpa using (sChain_lmRc a S).whisk [s] []

theorem ccnt_lmLc : ∀ (S : List (Letter I)) (b : Letter I), ccnt (lmLc S b) = S.length
  | [], _ => rfl
  | s :: S, b => by
    simp only [lmLc, ccnt_append, ccnt_map_whL, ccnt_lmLc S b, ccnt_xLay, List.length_cons]

theorem ccnt_lmRc (a : Letter I) : ∀ S : List (Letter I), ccnt (lmRc a S) = S.length
  | [] => rfl
  | s :: S => by
    simp only [lmRc, ccnt_append, ccnt_map_whL, ccnt_lmRc a S, ccnt_xLay, List.length_cons]
    omega

theorem lmLc_append (b : Letter I) : ∀ S₁ S₂ : List (Letter I),
    lmLc (S₁ ++ S₂) b = (lmLc S₂ b).map (whL S₁ []) ++ (lmLc S₁ b).map (whL [] S₂)
  | [], S₂ => by simp [lmLc]
  | s :: S₁, S₂ => by
    simp only [List.cons_append, lmLc, lmLc_append b S₁ S₂, List.map_append, List.map_map,
      List.append_assoc]
    congr 1
    · congr 1; funext x; simp [whL, Function.comp_def]
    · congr 1
      · congr 1; funext x; simp [whL, Function.comp_def]
      · congr 1; funext x; simp [whL, Function.comp_def]

theorem lmLc_snoc (S : List (Letter I)) (e b : Letter I) :
    lmLc (S ++ [e]) b = (xLay e b).map (whL S []) ++ (lmLc S b).map (whL [] [e]) := by
  rw [lmLc_append]; simp [lmLc]

/-! ## The cap with a block of strands passing over it -/

/-- The cap `l* l ⟶ 1` joining the strands `A = l*` and `B = l`, with `d` dots on `A`, over which
the strands `S` pass: `B` moves left across `S`, then `d` dots on `A`, then the cap. From
`[l*] ++ S ++ [l]` to `S`. -/
def capBlk (S : List (Letter I)) (l : Letter I) (d : ℕ) : List (LayerData I) :=
  (lmLc S l).map (whL [l.dual] []) ++ List.replicate d ([], .dot l.dual, l :: S) ++
    [([], .cap l, S)]

theorem sChain_capBlk (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    SChain ([l.dual] ++ S ++ [l]) (capBlk S l d) S := by
  unfold capBlk
  have h1 : SChain ([l.dual] ++ S ++ [l]) ((lmLc S l).map (whL [l.dual] [])) (l.dual :: l :: S) := by
    simpa using (sChain_lmLc S l).whisk [l.dual] []
  have h2 : SChain (l.dual :: l :: S) (List.replicate d ([], .dot l.dual, l :: S))
      (l.dual :: l :: S) :=
    SChain.replicate_of (x := ([], .dot l.dual, l :: S)) (s := l.dual :: l :: S) ⟨rfl, rfl⟩ d
  have h3 : SChain (l.dual :: l :: S) [([], .cap l, S)] S := ⟨rfl, rfl⟩
  exact (h1.append h2).append h3

theorem ccnt_capBlk (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    ccnt (capBlk S l d) = S.length := by
  simp [capBlk, ccnt_append, ccnt_map_whL, ccnt_lmLc, ccnt_replicate_dot]

/-! ## Tools: interchange in context, rewriting modulo lower terms -/

/-- **Interchange law for blocks in context**: a block `A` acting on the strands `s` and a block `B`
acting on the strands `t` to their right can be exchanged. -/
theorem dg_ichg {μ : X} {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (P Q : List (Letter I)) {s s' t t' : List (Letter I)} {A B : List (LayerData I)}
    (hA : SChain s A s') (hB : SChain t B t') :
    dg RD k μ s₀ t₀ (pre ++ A.map (whL P (t ++ Q)) ++ B.map (whL (P ++ s') Q) ++ post) =
      dg RD k μ s₀ t₀ (pre ++ B.map (whL (P ++ s) Q) ++ A.map (whL P (t' ++ Q)) ++ post) := by
  have E := dg_interchange (RD := RD) (k := k) (μ := μ) (S := s₀) (T := t₀) pre post
    (by simpa using hA.whisk P [] : SChain (P ++ s) (A.map (whL P [])) (P ++ s'))
    (by simpa using hB.whisk [] Q : SChain (t ++ Q) (B.map (whL [] Q)) (t' ++ Q))
  wnf at E
  wnf
  exact E


theorem sChain_map_whL_iff {s t : List (Letter I)} {A : List (LayerData I)} (hA : SChain s A t)
    (hne : A ≠ []) (u v s' t' : List (Letter I)) :
    SChain s' (A.map (whL u v)) t' ↔ s' = u ++ s ++ v ∧ t' = u ++ t ++ v := by
  constructor
  · intro h
    have h₀ := hA.whisk u v
    obtain ⟨x, A', rfl⟩ := List.exists_cons_of_ne_nil hne
    have e : s' = u ++ s ++ v := h.1.trans h₀.1.symm
    subst e
    exact ⟨rfl, SChain.eq_target h h₀⟩
  · rintro ⟨rfl, rfl⟩; exact hA.whisk u v

/-- **A local equation in any context**, without typing hypotheses on the context. -/
theorem dg_step_free {μ : X} {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)}
    (E : dg RD k (wt RD μ v) s t A = dg RD k (wt RD μ v) s t B) (hA : SChain s A t)
    (hB : SChain s B t) (hAne : A ≠ []) (hBne : B ≠ []) {L L' : List (LayerData I)}
    (hL : L = pre ++ A.map (whL u v) ++ post) (hL' : L' = pre ++ B.map (whL u v) ++ post) :
    dg RD k μ s₀ t₀ L = dg RD k μ s₀ t₀ L' := by
  subst hL hL'
  refine dg_congr_ctx (fun s' t' h => ?_) (fun s' t' h => ?_) (fun s' t' h => ?_) s₀ t₀ pre post
  · obtain ⟨rfl, rfl⟩ := (sChain_map_whL_iff hA hAne u v s' t').1 h
    exact hB.whisk u v
  · obtain ⟨rfl, rfl⟩ := (sChain_map_whL_iff hB hBne u v s' t').1 h
    exact hA.whisk u v
  · obtain ⟨rfl, rfl⟩ := (sChain_map_whL_iff hA hAne u v s' t').1 h
    rw [← plcL_dg, ← plcL_dg, E]

/-- **A local relation modulo lower terms in any context**, without typing hypotheses on the
context. -/
theorem dg_mod_free {μ : X} {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A B : List (LayerData I)} {c c' : ℕ}
    (E : dg RD k (wt RD μ v) s t A - dg RD k (wt RD μ v) s t B ∈ LeL RD k (wt RD μ v) s t c)
    (hA : SChain s A t) (hB : SChain s B t) (hAne : A ≠ []) (hBne : B ≠ [])
    {L L' : List (LayerData I)}
    (hL : L = pre ++ A.map (whL u v) ++ post) (hL' : L' = pre ++ B.map (whL u v) ++ post)
    (hc : ccnt pre + c + ccnt post ≤ c') :
    dg RD k μ s₀ t₀ L - dg RD k μ s₀ t₀ L' ∈ LeL RD k μ s₀ t₀ c' := by
  subst hL hL'
  by_cases h : SChain s₀ (pre ++ A.map (whL u v) ++ post) t₀
  · obtain ⟨m', h₁, h₂⟩ := SChain.split h
    obtain ⟨m, h₃, h₄⟩ := SChain.split h₁
    obtain ⟨rfl, rfl⟩ := (sChain_map_whL_iff hA hAne u v m m').1 h₄
    exact leL_mono hc (dg_mod_ctx μ pre post u v E h₃ h₂)
  · have h' : ¬ SChain s₀ (pre ++ B.map (whL u v) ++ post) t₀ := by
      intro h'
      obtain ⟨m', h₁, h₂⟩ := SChain.split h'
      obtain ⟨m, h₃, h₄⟩ := SChain.split h₁
      obtain ⟨rfl, rfl⟩ := (sChain_map_whL_iff hB hBne u v m m').1 h₄
      exact h ((h₃.append (hA.whisk u v)).append h₂)
    rw [dg_of_not h, dg_of_not h', sub_self]; exact Submodule.zero_mem _

/-- A local diagram in the lower span, in any context. -/
theorem dg_mem_free {μ : X} {s₀ t₀ : List (Letter I)} (pre post : List (LayerData I))
    (u v : List (Letter I)) {s t : List (Letter I)} {A : List (LayerData I)} {c c' : ℕ}
    (E : dg RD k (wt RD μ v) s t A ∈ LeL RD k (wt RD μ v) s t c)
    (hA : SChain s A t) (hAne : A ≠ []) {L : List (LayerData I)}
    (hL : L = pre ++ A.map (whL u v) ++ post) (hc : ccnt pre + c + ccnt post ≤ c') :
    dg RD k μ s₀ t₀ L ∈ LeL RD k μ s₀ t₀ c' := by
  subst hL
  by_cases h : SChain s₀ (pre ++ A.map (whL u v) ++ post) t₀
  · obtain ⟨m', h₁, h₂⟩ := SChain.split h
    obtain ⟨m, h₃, h₄⟩ := SChain.split h₁
    obtain ⟨rfl, rfl⟩ := (sChain_map_whL_iff hA hAne u v m m').1 h₄
    exact leL_mono hc (dg_mem_ctx μ pre post u v E h₃ h₂)
  · rw [dg_of_not h]; exact Submodule.zero_mem _

/-- **A local relation modulo lower terms, in context** (with explicit decompositions). -/
theorem dg_mod_step {μ : X} {s₀ t₀ : List (Letter I)} {L L' : List (LayerData I)}
    (pre post : List (LayerData I)) (u v : List (Letter I)) {s t : List (Letter I)}
    {A B : List (LayerData I)} {c c' : ℕ}
    (E : dg RD k (wt RD μ v) s t A - dg RD k (wt RD μ v) s t B ∈ LeL RD k (wt RD μ v) s t c)
    (hpre : SChain s₀ pre (u ++ s ++ v)) (hpost : SChain (u ++ t ++ v) post t₀)
    (hL : L = pre ++ A.map (whL u v) ++ post) (hL' : L' = pre ++ B.map (whL u v) ++ post)
    (hc : ccnt pre + c + ccnt post ≤ c') :
    dg RD k μ s₀ t₀ L - dg RD k μ s₀ t₀ L' ∈ LeL RD k μ s₀ t₀ c' := by
  subst hL hL'
  exact leL_mono hc (dg_mod_ctx μ pre post u v E hpre hpost)

/-- A dot on the right leg of a cap equals a dot on its left leg. -/
theorem dotCap (ν : X) (l : Letter I) :
    dg RD k ν [l.dual, l] [] [([l.dual], .dot l, []), ([], .cap l, [])] =
      dg RD k ν [l.dual, l] [] [([], .dot l.dual, [l]), ([], .cap l, [])] := by
  obtain ⟨_ | _, i⟩ := l
  · exact dg_dot_cap_dn RD k ν i
  · exact (dg_dot_cap_up RD k ν i).symm

/-- The zigzag with dots on the cup's right leg. -/
theorem zigDotsL (ν : X) (l : Letter I) (d : ℕ) :
    dg RD k ν [l] [l] ([([], .cup l, [l])] ++ List.replicate d ([l], .dot l.dual, [l]) ++
        [([l], .cap l, [])]) =
      dg RD k ν [l] [l] (List.replicate d ([], .dot l, [])) := by
  have hc : dg RD k (wt RD ν [l]) [] [l, l.dual]
      ([([], .cup l, [])] ++ List.replicate d ([l], .dot l.dual, [])) =
      dg RD k (wt RD ν [l]) [] [l, l.dual] ([([], .cup l, [])] ++ List.replicate d ([], .dot l, [l.dual])) := by
    obtain ⟨_ | _, i⟩ := l
    · exact dg_dots_cupDn RD k i _ d
    · exact dg_dots_cupUp RD k i _ d
  dstep [] [([l], .cap l, [])] [] [l] hc
  dstep [([], .cup l, [l])] [] [] [] (dg_swap_rep' RD k ν [] [] [] (.cap l) (.dot l) rfl d)
  dstep [] (List.replicate d ([], .dot l, [])) [] [] (dg_zigL' RD k ν l)
  simp



/-! ## The cap block: dots -/

theorem capBlk_dotA (ν : X) (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    dg RD k ν ([l.dual] ++ S ++ [l]) S ([([], .dot l.dual, S ++ [l])] ++ capBlk S l d) =
      dg RD k ν ([l.dual] ++ S ++ [l]) S (capBlk S l (d + 1)) := by
  have := dg_ichg (RD := RD) (k := k) (μ := ν) (s₀ := [l.dual] ++ S ++ [l]) (t₀ := S) []
    (List.replicate d ([], .dot l.dual, l :: S) ++ [([], .cap l, S)]) [] []
    (A := [([], .dot l.dual, [])]) (B := lmLc S l) (s := [l.dual]) (s' := [l.dual]) (t := S ++ [l])
    (t' := l :: S) ⟨rfl, rfl⟩ (sChain_lmLc S l)
  unfold capBlk
  wnf at this ⊢
  rw [List.replicate_succ]
  exact this


section Dec

variable [DecidableEq I]

theorem ds0rep (ν : X) (l₁ l₂ : Letter I) (d : ℕ) :
    dg RD k ν [l₁, l₂] [l₂, l₁] (xLay l₁ l₂ ++ List.replicate d ([], .dot l₂, [l₁])) -
      dg RD k ν [l₁, l₂] [l₂, l₁] (List.replicate d ([l₁], .dot l₂, []) ++ xLay l₁ l₂) ∈
        LeL RD k ν [l₁, l₂] [l₂, l₁] 0 := by
  induction d with
  | zero => simp only [List.replicate_zero, List.append_nil, List.nil_append]; exact leL_sub_self _
  | succ d ih =>
    refine leL_sub_trans (b := dg RD k ν [l₁, l₂] [l₂, l₁]
      ([([l₁], .dot l₂, [])] ++ (xLay l₁ l₂ ++ List.replicate d ([], .dot l₂, [l₁])))) ?_ ?_
    · exact dg_mod_step [] (List.replicate d ([], .dot l₂, [l₁])) [] [] (ds0 ν l₁ l₂)
        rfl (by simpa using SChain.replicate d [] l₂ [l₁]) (by simp [List.replicate_succ])
        (by simp) (by simp [ccnt_replicate_dot])
    · refine dg_mod_step [([l₁], .dot l₂, [])] [] [] [] ih ⟨rfl, rfl⟩ rfl (by simp) ?_ (by simp)
      simp [List.replicate_succ]

theorem ds1rep (ν : X) (l₁ l₂ : Letter I) (d : ℕ) :
    dg RD k ν [l₁, l₂] [l₂, l₁] (xLay l₁ l₂ ++ List.replicate d ([l₂], .dot l₁, [])) -
      dg RD k ν [l₁, l₂] [l₂, l₁] (List.replicate d ([], .dot l₁, [l₂]) ++ xLay l₁ l₂) ∈
        LeL RD k ν [l₁, l₂] [l₂, l₁] 0 := by
  induction d with
  | zero => simp only [List.replicate_zero, List.append_nil, List.nil_append]; exact leL_sub_self _
  | succ d ih =>
    refine leL_sub_trans (b := dg RD k ν [l₁, l₂] [l₂, l₁]
      ([([], .dot l₁, [l₂])] ++ (xLay l₁ l₂ ++ List.replicate d ([l₂], .dot l₁, [])))) ?_ ?_
    · exact dg_mod_step [] (List.replicate d ([l₂], .dot l₁, [])) [] [] (ds1 ν l₁ l₂)
        rfl (by simpa using SChain.replicate d [l₂] l₁ []) (by simp [List.replicate_succ])
        (by simp) (by simp [ccnt_replicate_dot])
    · refine dg_mod_step [([], .dot l₁, [l₂])] [] [] [] ih ⟨rfl, rfl⟩ rfl (by simp) ?_ (by simp)
      simp [List.replicate_succ]

theorem dotThruLm (ν : X) (b : Letter I) : ∀ S : List (Letter I),
    dg RD k ν (S ++ [b]) (b :: S) ([(S, .dot b, [])] ++ lmLc S b) -
      dg RD k ν (S ++ [b]) (b :: S) (lmLc S b ++ [([], .dot b, S)]) ∈
        LeL RD k ν (S ++ [b]) (b :: S) (S.length - 1)
  | [] => by simp [lmLc]
  | [s] => by
    have h := leL_sub_comm (ds0 (RD := RD) (k := k) ν s b)
    simpa [lmLc] using h
  | s :: s' :: S => by
    have ih := dotThruLm ν b (s' :: S)
    refine leL_sub_trans (b := dg RD k ν (s :: s' :: S ++ [b]) (b :: s :: s' :: S)
      ((lmLc (s' :: S) b).map (whL [s] []) ++ [([s], .dot b, s' :: S)] ++
        (xLay s b).map (whL [] (s' :: S)))) ?_ ?_
    · refine dg_mod_step [] ((xLay s b).map (whL [] (s' :: S))) [s] [] ih (by simp)
        (by simpa using (sChain_xLay s b).whisk [] (s' :: S)) ?_ ?_ ?_
      · rw [lmLc]; try wnf
      · try wnf
      · simp [ccnt_map_whL]; try omega
    · refine dg_mod_step ((lmLc (s' :: S) b).map (whL [s] [])) [] [] (s' :: S)
        (leL_sub_comm (ds0 (RD := RD) (k := k) _ s b)) ?_ (by simp) ?_ ?_ ?_
      · simpa using (sChain_lmLc (s' :: S) b).whisk [s] []
      · wnf
      · rw [lmLc]; try wnf
      · simp [ccnt_map_whL, ccnt_lmLc]

theorem capBlk_dotB (ν : X) (S : List (Letter I)) (l : Letter I) (d : ℕ) :
    dg RD k ν ([l.dual] ++ S ++ [l]) S ([([l.dual] ++ S, .dot l, [])] ++ capBlk S l d) -
      dg RD k ν ([l.dual] ++ S ++ [l]) S (capBlk S l (d + 1)) ∈
        LeL RD k ν ([l.dual] ++ S ++ [l]) S (S.length - 1) := by
  -- the dot passes the block
  refine leL_sub_trans (b := dg RD k ν ([l.dual] ++ S ++ [l]) S
      ((lmLc S l).map (whL [l.dual] []) ++ [([l.dual], .dot l, S)] ++
        List.replicate d ([], .dot l.dual, l :: S) ++ [([], .cap l, S)])) ?_ ?_
  · refine dg_mod_step [] (List.replicate d ([], .dot l.dual, l :: S) ++ [([], .cap l, S)])
      [l.dual] [] (dotThruLm ν l S) (by simp) ?_ ?_ ?_ ?_
    · have h1 : SChain (l.dual :: l :: S) (List.replicate d ([], .dot l.dual, l :: S))
          (l.dual :: l :: S) :=
        SChain.replicate_of (x := ([], .dot l.dual, l :: S)) (s := l.dual :: l :: S) ⟨rfl, rfl⟩ d
      simpa using h1.append (show SChain (l.dual :: l :: S) [([], .cap l, S)] S from ⟨rfl, rfl⟩)
    · unfold capBlk; wnf
    · wnf
    · simp [ccnt_append, ccnt_replicate_dot]
  · refine leL_sub_of_eq ?_
    -- dots on `A` and the dot on `B` commute, then the dot moves around the cap
    have e₁ := dg_swap_dots RD k (wt RD ν S) [] [] [] l.dual l 1 d
    simp only [List.nil_append, List.append_nil, List.replicate_one] at e₁
    have hpre : SChain ([l.dual] ++ S ++ [l]) ((lmLc S l).map (whL [l.dual] [])) (l.dual :: l :: S) := by
      simpa using (sChain_lmLc S l).whisk [l.dual] []
    refine (dg_step RD k ν ((lmLc S l).map (whL [l.dual] [])) [([], .cap l, S)] [] S e₁
      (by simpa using hpre) ⟨rfl, rfl⟩ (by wnf) rfl).trans ?_
    refine (dg_step RD k ν ((lmLc S l).map (whL [l.dual] []) ++
      List.replicate d ([], .dot l.dual, l :: S)) [] [] S (dotCap (wt RD ν S) l)
      (by simpa using hpre.append (SChain.replicate_of (x := ([], .dot l.dual, l :: S))
        (s := l.dual :: l :: S) ⟨rfl, rfl⟩ d)) rfl (by wnf) rfl).trans ?_
    unfold capBlk
    wnf
    rw [List.replicate_succ']
    wnf

end Dec

end Categorification.KL3.Diagram
