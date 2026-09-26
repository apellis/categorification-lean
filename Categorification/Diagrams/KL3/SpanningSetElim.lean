/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.SpanningSetBlock

/-!
# Elimination of caps

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3, proof
of Proposition 3.11 (reduction of diagrams modulo lower terms, following A. Lauda,
arXiv:0803.3652v3, §8).

We push a cap block (`capBlk`) down through a move diagram, one move at a time, using the local
relations of `Categorification.Diagrams.KL3.SpanningSetBlock`, and deduce that every normal-form
diagram with at most `c` crossings lies in `CapTarget c`: it is a linear combination of move
diagrams (dots, crossings, cups; no caps) with at most `c` crossings followed by bubble monomials,
modulo 2-morphisms factoring through sequences shorter than the source (simply-laced Cartan data).

## Main results

* `capPush`: a cap block on top of a move diagram lies in `CapTarget`.
* `capElim`: every normal-form diagram with at most `c` crossings lies in `CapTarget c`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Moves in context -/

namespace Mv

/-- The local layers of a move. -/
def loc : Mv I → List (LayerData I)
  | dot _ l _ => [([], .dot l, [])]
  | cross _ l₁ l₂ _ => xLay l₁ l₂
  | cup _ l _ => [([], .cup l, [])]

/-- The local bottom boundary of a move. -/
def lsrc : Mv I → List (Letter I)
  | dot _ l _ => [l]
  | cross _ l₁ l₂ _ => [l₁, l₂]
  | cup _ _ _ => []

/-- The local top boundary of a move. -/
def ltgt : Mv I → List (Letter I)
  | dot _ l _ => [l]
  | cross _ l₁ l₂ _ => [l₂, l₁]
  | cup _ l _ => [l, l.dual]

/-- The strands to the left of a move. -/
def pre : Mv I → List (Letter I)
  | dot u _ _ => u
  | cross u _ _ _ => u
  | cup u _ _ => u

/-- The strands to the right of a move. -/
def post : Mv I → List (Letter I)
  | dot _ _ v => v
  | cross _ _ _ v => v
  | cup _ _ v => v

/-- The same move between other strands. -/
def reCtx : Mv I → List (Letter I) → List (Letter I) → Mv I
  | dot _ l _, u, v => dot u l v
  | cross _ l₁ l₂ _, u, v => cross u l₁ l₂ v
  | cup _ l _, u, v => cup u l v

theorem lay_eq (m : Mv I) : m.lay = m.loc.map (whL m.pre m.post) := by
  cases m <;> simp [lay, loc, pre, post]

theorem src_eq (m : Mv I) : m.src = m.pre ++ m.lsrc ++ m.post := by
  cases m <;> simp [src, lsrc, pre, post]

theorem tgt_eq (m : Mv I) : m.tgt = m.pre ++ m.ltgt ++ m.post := by
  cases m <;> simp [tgt, ltgt, pre, post]

theorem sChain_loc (m : Mv I) : SChain m.lsrc m.loc m.ltgt := by
  cases m with
  | dot u l v => exact ⟨rfl, rfl⟩
  | cross u l₁ l₂ v => exact sChain_xLay l₁ l₂
  | cup u l v => exact ⟨rfl, rfl⟩

theorem loc_ne_nil (m : Mv I) : m.loc ≠ [] := by
  cases m <;> simp [loc, xLay_ne_nil]

@[simp] theorem reCtx_pre (m : Mv I) (u v : List (Letter I)) : (m.reCtx u v).pre = u := by
  cases m <;> rfl
@[simp] theorem reCtx_post (m : Mv I) (u v : List (Letter I)) : (m.reCtx u v).post = v := by
  cases m <;> rfl
@[simp] theorem reCtx_loc (m : Mv I) (u v : List (Letter I)) : (m.reCtx u v).loc = m.loc := by
  cases m <;> rfl
@[simp] theorem reCtx_lsrc (m : Mv I) (u v : List (Letter I)) : (m.reCtx u v).lsrc = m.lsrc := by
  cases m <;> rfl
@[simp] theorem reCtx_ltgt (m : Mv I) (u v : List (Letter I)) : (m.reCtx u v).ltgt = m.ltgt := by
  cases m <;> rfl

theorem ccnt_lay_eq_loc (m : Mv I) : ccnt m.lay = ccnt m.loc := by
  rw [lay_eq, ccnt_map_whL]

end Mv

/-- Whiskering a list of moves. -/
def mvWh (P Q : List (Letter I)) (ms : List (Mv I)) : List (Mv I) :=
  ms.map fun m => m.reCtx (P ++ m.pre) (m.post ++ Q)

theorem mvLay_mvWh (P Q : List (Letter I)) (ms : List (Mv I)) :
    mvLay (mvWh P Q ms) = (mvLay ms).map (whL P Q) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [mvWh, List.map_cons, mvLay, List.flatten_cons, List.map_append] at ih ⊢
    rw [ih, Mv.lay_eq, Mv.lay_eq, Mv.reCtx_loc, Mv.reCtx_pre, Mv.reCtx_post, map_whL_whL]

theorem MvChain.wh (P Q : List (Letter I)) : ∀ {s t : List (Letter I)} {ms : List (Mv I)},
    MvChain s ms t → MvChain (P ++ s ++ Q) (mvWh P Q ms) (P ++ t ++ Q)
  | _, _, [], h => by subst h; rfl
  | _, _, m :: ms, ⟨rfl, h⟩ => by
    refine ⟨?_, ?_⟩
    · rw [Mv.src_eq, Mv.src_eq]; simp
    · have := MvChain.wh P Q h
      rw [Mv.tgt_eq] at this ⊢
      simpa using this

theorem MvChain.append : ∀ {s m t : List (Letter I)} {ms ns : List (Mv I)},
    MvChain s ms m → MvChain m ns t → MvChain s (ms ++ ns) t
  | _, _, _, [], _, h₁, h₂ => by subst h₁; exact h₂
  | _, _, _, _ :: _, _, ⟨h, h₁⟩, h₂ => ⟨h, MvChain.append h₁ h₂⟩

theorem ccnt_mvLay_mvWh (P Q : List (Letter I)) (ms : List (Mv I)) :
    ccnt (mvLay (mvWh P Q ms)) = ccnt (mvLay ms) := by
  rw [mvLay_mvWh, ccnt_map_whL]

/-- The moves of a strand moving left across `S`. -/
def lmMv : List (Letter I) → Letter I → List (Mv I)
  | [], _ => []
  | s :: S, b => mvWh [s] [] (lmMv S b) ++ [Mv.cross [] s b S]

theorem mvLay_lmMv : ∀ (S : List (Letter I)) (b : Letter I), mvLay (lmMv S b) = lmLc S b
  | [], _ => rfl
  | s :: S, b => by
    rw [lmMv, mvLay_append, mvLay_mvWh, mvLay_lmMv S b, mvLay_singleton, lmLc]
    rfl

theorem mvChain_lmMv : ∀ (S : List (Letter I)) (b : Letter I), MvChain (S ++ [b]) (lmMv S b) (b :: S)
  | [], _ => rfl
  | s :: S, b => by
    rw [lmMv]
    refine MvChain.append (m := [s] ++ (b :: S) ++ []) ?_ ?_
    · simpa using (mvChain_lmMv S b).wh [s] []
    · exact ⟨by simp [Mv.src], by simp [Mv.tgt, MvChain]⟩

/-- The moves of a strand moving right across `S`. -/
def rmMv (a : Letter I) : List (Letter I) → List (Mv I)
  | [] => []
  | s :: S => [Mv.cross [] a s S] ++ mvWh [s] [] (rmMv a S)

theorem mvLay_rmMv (a : Letter I) : ∀ S : List (Letter I), mvLay (rmMv a S) = lmRc a S
  | [] => rfl
  | s :: S => by
    rw [rmMv, mvLay_append, mvLay_mvWh, mvLay_rmMv a S, mvLay_singleton, lmRc]
    rfl

theorem mvChain_rmMv (a : Letter I) : ∀ S : List (Letter I), MvChain (a :: S) (rmMv a S) (S ++ [a])
  | [] => rfl
  | s :: S => by
    rw [rmMv]
    refine MvChain.append (m := [s] ++ (a :: S) ++ []) ?_ ?_
    · exact ⟨by simp [Mv.src], by simp [Mv.tgt, MvChain]⟩
    · simpa using (mvChain_rmMv a S).wh [s] []

/-- `d` dots as moves. -/
def dotMv (d : ℕ) (u : List (Letter I)) (l : Letter I) (v : List (Letter I)) : List (Mv I) :=
  List.replicate d (Mv.dot u l v)

theorem mvLay_dotMv (d : ℕ) (u : List (Letter I)) (l : Letter I) (v : List (Letter I)) :
    mvLay (dotMv d u l v) = List.replicate d (u, .dot l, v) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [dotMv, List.replicate_succ, mvLay, List.map_cons, List.flatten_cons] at ih ⊢
    rw [ih]; rfl

theorem mvChain_dotMv (d : ℕ) (u : List (Letter I)) (l : Letter I) (v : List (Letter I)) :
    MvChain (u ++ [l] ++ v) (dotMv d u l v) (u ++ [l] ++ v) := by
  induction d with
  | zero => rfl
  | succ d ih => exact ⟨rfl, ih⟩

/-- Dot layers are moves. -/
theorem exists_mv_of_dots : ∀ (D : List (LayerData I)) {s t : List (Letter I)},
    AllSh Shape.isDot D → SChain s D t → ∃ ns : List (Mv I), mvLay ns = D ∧ MvChain s ns t ∧
      ccnt (mvLay ns) = 0
  | [], s, t, _, h => ⟨[], rfl, h, rfl⟩
  | (a, g, b) :: D, s, t, hD, h => by
    obtain ⟨ns, h₁, h₂, h₃⟩ := exists_mv_of_dots D (fun x hx => hD x (by simp [hx])) h.2
    cases g with
    | dot l =>
      refine ⟨Mv.dot a l b :: ns, by simp [mvLay, h₁.symm, Mv.lay], ⟨?_, h₂⟩, ?_⟩
      · simpa [Mv.src] using h.1
      · simpa [mvLay, ccnt_append, Mv.lay] using h₃
    | _ => exact absurd (hD _ List.mem_cons_self) (by simp [Shape.isDot])

/-! ## Positions of a move relative to the block -/

theorem split1 {α : Type*} {x y : α} : ∀ {u v L₁ L₂ : List α}, u ++ [x] ++ v = L₁ ++ [y] ++ L₂ →
    (∃ R, L₁ = u ++ [x] ++ R ∧ v = R ++ [y] ++ L₂) ∨ (u = L₁ ∧ x = y ∧ v = L₂) ∨
      (∃ R, u = L₁ ++ [y] ++ R ∧ L₂ = R ++ [x] ++ v)
  | [], v, [], L₂, h => by simp at h; exact Or.inr (Or.inl ⟨rfl, h.1, h.2⟩)
  | [], v, b :: L₁, L₂, h => by
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨L₁, by simp, by simp⟩
  | a :: u, v, [], L₂, h => by
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr (Or.inr ⟨u, by simp, by simp⟩)
  | a :: u, v, b :: L₁, L₂, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rcases split1 (by simpa using h) with ⟨R, h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨R, h₁, h₂⟩
    · exact Or.inl ⟨R, by simp [h₁], h₂⟩
    · exact Or.inr (Or.inl ⟨by simp [h₁], h₂, h₃⟩)
    · exact Or.inr (Or.inr ⟨R, by simp [h₁], h₂⟩)

theorem posDot {α : Type*} {u v P S Q : List α} {x A B : α}
    (h : u ++ [x] ++ v = P ++ [A] ++ S ++ [B] ++ Q) :
    (∃ R, P = u ++ [x] ++ R ∧ v = R ++ [A] ++ S ++ [B] ++ Q) ∨
      (u = P ∧ x = A ∧ v = S ++ [B] ++ Q) ∨
      (∃ S₁ S₂, S = S₁ ++ [x] ++ S₂ ∧ u = P ++ [A] ++ S₁ ∧ v = S₂ ++ [B] ++ Q) ∨
      (u = P ++ [A] ++ S ∧ x = B ∧ v = Q) ∨
      (∃ R, Q = R ++ [x] ++ v ∧ u = P ++ [A] ++ S ++ [B] ++ R) := by
  rcases split1 (L₁ := P) (L₂ := S ++ [B] ++ Q) (by simpa using h) with
    ⟨R, h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨R, h₁, h₂⟩
  · exact Or.inl ⟨R, h₁, by simpa using h₂⟩
  · exact Or.inr (Or.inl ⟨h₁, h₂, h₃⟩)
  · rcases split1 (u := R) (v := v) (L₁ := S) (L₂ := Q) (by simpa using h₂.symm) with
      ⟨R', h₃, h₄⟩ | ⟨h₃, h₄, h₅⟩ | ⟨R', h₃, h₄⟩
    · exact Or.inr (Or.inr (Or.inl ⟨R, R', h₃, by simpa using h₁, by simpa using h₄⟩))
    · subst h₃; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by simpa using h₁, h₄, h₅⟩)))
    · subst h₃
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨R', h₄, by simpa using h₁⟩)))

theorem posPair {α : Type*} {u v P S Q : List α} {y z A B : α}
    (h : u ++ [y, z] ++ v = P ++ [A] ++ S ++ [B] ++ Q) :
    (∃ R, P = u ++ [y, z] ++ R ∧ v = R ++ [A] ++ S ++ [B] ++ Q) ∨
      (P = u ++ [y] ∧ z = A ∧ v = S ++ [B] ++ Q) ∨
      (u = P ∧ y = A ∧ ∃ S', S = z :: S' ∧ v = S' ++ [B] ++ Q) ∨
      (u = P ∧ y = A ∧ S = [] ∧ z = B ∧ v = Q) ∨
      (∃ S₁ S₂, S = S₁ ++ [y, z] ++ S₂ ∧ u = P ++ [A] ++ S₁ ∧ v = S₂ ++ [B] ++ Q) ∨
      (∃ S', S = S' ++ [y] ∧ z = B ∧ u = P ++ [A] ++ S' ∧ v = Q) ∨
      (u = P ++ [A] ++ S ∧ y = B ∧ Q = z :: v) ∨
      (∃ R, Q = R ++ [y, z] ++ v ∧ u = P ++ [A] ++ S ++ [B] ++ R) := by
  rcases posDot (u := u) (x := y) (v := z :: v) (by simpa using h) with
    ⟨R, h₁, h₂⟩ | ⟨h₁, h₂, h₃⟩ | ⟨S₁, S₂, h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨R, h₁, h₂⟩
  · rcases R with _ | ⟨r, R⟩
    · simp at h₂
      exact Or.inr (Or.inl ⟨by simpa using h₁, h₂.1, by simpa using h₂.2⟩)
    · simp at h₂
      exact Or.inl ⟨R, by simp [h₁, h₂.1], by simpa using h₂.2⟩
  · rcases S with _ | ⟨s, S⟩
    · simp at h₃
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁, h₂, rfl, h₃.1, h₃.2⟩)))
    · simp at h₃
      exact Or.inr (Or.inr (Or.inl ⟨h₁, h₂, S, by simp [h₃.1], by simpa using h₃.2⟩))
  · rcases S₂ with _ | ⟨s, S₂⟩
    · simp at h₃
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨S₁, by simpa using h₁, h₃.1, h₂,
        h₃.2⟩)))))
    · simp at h₃
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨S₁, S₂, by simp [h₁, h₃.1], h₂,
        by simpa using h₃.2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h₁, h₂, h₃.symm⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨R, by simp [h₁], h₂⟩))))))

/-! ## A zigzag -/

/-- A cup creating `B` and a strand to the right of the block, with no strands in the block,
cancels the cap exactly (zigzag). -/
theorem capBlk_cupBright_nil (ν : X) (l : Letter I) (d : ℕ) :
    dg RD k ν [l.dual] [l.dual] ([([l.dual], .cup l, [])] ++ (capBlk [] l d).map (whL [] [l.dual])) =
      dg RD k ν [l.dual] [l.dual] (List.replicate d ([], .dot l.dual, [])) := by
  simp only [capBlk_eq, lmLc, List.map_nil, List.nil_append, List.map_append, List.map_replicate]
  refine (dg_step_free [] [whL [] [l.dual] ([], .cap l, [])] [] []
      (ichgLoc (RD := RD) (k := k) _ (A := List.replicate d ([], .dot l.dual, []))
        (s := [l.dual]) (s' := [l.dual]) (B := [([], .cup l, [])]) (t := []) (t' := [l, l.dual])
        (by simpa using SChain.replicate d [] l.dual []) ⟨rfl, rfl⟩).symm
      (sChain_ichgR (by simpa using SChain.replicate d [] l.dual []) ⟨rfl, rfl⟩)
      (sChain_ichgL (by simpa using SChain.replicate d [] l.dual []) ⟨rfl, rfl⟩)
      (by simp) (by simp) (by wnf) rfl).trans ?_
  exact dg_step RD k ν (List.replicate d ([], .dot l.dual, [])) [] [] []
    (dg_zigR' RD k (wt RD ν []) l) (by simpa using SChain.replicate d [] l.dual [])
    rfl (by wnf) (by wnf)

/-! ## Pushing the cap block down -/

section Push

variable {μ : X} {w₀ : List (Letter I)}

theorem capTarget_comp_mvs {c : ℕ} : ∀ {ns : List (Mv I)} {v v' : List (Letter I)}
    {f : (pres RD k).obj (ob RD μ w₀) ⟶ (pres RD k).obj (ob RD μ v)},
    f ∈ CapTarget RD k μ w₀ v c → MvChain v ns v' →
      f ≫ dg RD k μ v v' (mvLay ns) ∈ CapTarget RD k μ w₀ v' (c + ccnt (mvLay ns))
  | [], v, v', f, hf, h => by
    subst h; rw [mvLay_nil, dg_nil, Category.comp_id]; simpa using hf
  | m :: ns, v, v', f, hf, ⟨hv, h⟩ => by
    subst hv
    have h1 := capTarget_comp_mv hf m rfl
    have h2 := capTarget_comp_mvs (ns := ns) h1 h
    have e : mvLay (m :: ns) = m.lay ++ mvLay ns := rfl
    rw [e, ← dg_comp m.sChain_lay h.sChain, ← Category.assoc, ccnt_append, ← add_assoc]
    exact h2

variable (RD k μ w₀) in
/-- The induction hypothesis on the number of crossings. -/
def LowHyp (c : ℕ) : Prop :=
  ∀ c' < c, ∀ (v : List (Letter I)) (L : List (LayerData I)), ccnt L ≤ c' →
    dg RD k μ w₀ v L ∈ CapTarget RD k μ w₀ v c'

theorem capT_of_leL {v : List (Letter I)} {c c' t : ℕ} (hF : LowHyp RD k μ w₀ c) (hc : c' < c)
    (ht : c' ≤ t) {f} (hf : f ∈ LeL RD k μ w₀ v c') : f ∈ CapTarget RD k μ w₀ v t := by
  refine capTarget_mono ht ?_
  refine (Submodule.span_le.mpr ?_) hf
  rintro _ ⟨L, hL, rfl⟩
  exact hF c' hc v L hL

theorem capT_of_sub {v : List (Letter I)} {c c' t : ℕ} (hF : LowHyp RD k μ w₀ c) (hc : c' < c)
    (ht : c' ≤ t) {a b} (h : a - b ∈ LeL RD k μ w₀ v c') (hb : b ∈ CapTarget RD k μ w₀ v t) :
    a ∈ CapTarget RD k μ w₀ v t := by
  have := Submodule.add_mem _ (capT_of_leL hF hc ht h) hb
  simpa using this

variable (RD k μ w₀) in
/-- The statement of the cap push for a move diagram `ms`. -/
def PushHyp (c : ℕ) (ms : List (Mv I)) : Prop :=
  ∀ (P S Q : List (Letter I)) (l : Letter I) (d : ℕ),
    MvChain w₀ ms (P ++ [l.dual] ++ S ++ [l] ++ Q) → ccnt (mvLay ms) + S.length ≤ c →
    dg RD k μ w₀ (P ++ S ++ Q) (mvLay ms ++ (capBlk S l d).map (whL P Q)) ∈
      CapTarget RD k μ w₀ (P ++ S ++ Q) (ccnt (mvLay ms) + S.length)

theorem pushHyp_nil (c : ℕ) : PushHyp RD k μ w₀ c [] := by
  intro P S Q l d h _
  have h' : w₀ = P ++ [l.dual] ++ S ++ [l] ++ Q := h
  subst h'
  refine Submodule.mem_sup_right ?_
  have := dg_mem_thruShort (RD := RD) (k := k) (μ := μ) (w₀ := P ++ [l.dual] ++ S ++ [l] ++ Q)
    (v := P ++ S ++ Q) (u := P ++ S ++ Q) ((capBlk S l d).map (whL P Q)) [] (by simp; omega)
  rw [dg_nil, Category.comp_id] at this
  simpa using this

variable (RD k μ w₀) in
/-- The step of the cap push: the goal for `ms ++ [m]`. -/
def PushGoal (c : ℕ) (ms : List (Mv I)) (m : Mv I) : Prop :=
  ∀ (P S Q : List (Letter I)) (l : Letter I) (d : ℕ),
    m.tgt = P ++ [l.dual] ++ S ++ [l] ++ Q → ccnt (mvLay ms) + ccnt m.lay + S.length ≤ c →
    dg RD k μ w₀ (P ++ S ++ Q) (mvLay ms ++ m.lay ++ (capBlk S l d).map (whL P Q)) ∈
      CapTarget RD k μ w₀ (P ++ S ++ Q) (ccnt (mvLay ms) + ccnt m.lay + S.length)

/-- A move to the left of the block commutes with it. -/
theorem push_disjL {c : ℕ} {ms : List (Mv I)} (hIH : PushHyp RD k μ w₀ c ms) {m : Mv I}
    (hms : MvChain w₀ ms m.src) {P S Q : List (Letter I)} {l : Letter I} (d : ℕ)
    (R : List (Letter I)) (hP : P = m.pre ++ m.ltgt ++ R)
    (hv : m.post = R ++ [l.dual] ++ S ++ [l] ++ Q) (hc : ccnt (mvLay ms) + ccnt m.lay + S.length ≤ c) :
    dg RD k μ w₀ (P ++ S ++ Q) (mvLay ms ++ m.lay ++ (capBlk S l d).map (whL P Q)) ∈
      CapTarget RD k μ w₀ (P ++ S ++ Q) (ccnt (mvLay ms) + ccnt m.lay + S.length) := by
  subst hP
  set m' := m.reCtx m.pre (R ++ S ++ Q)
  have hB := (sChain_capBlk S l d).whisk R []
  have e : dg RD k μ w₀ (m.pre ++ m.ltgt ++ R ++ S ++ Q) (mvLay ms ++ m.lay ++ (capBlk S l d).map (whL (m.pre ++ m.ltgt ++ R) Q)) =
      dg RD k μ w₀ (m.pre ++ m.ltgt ++ R ++ S ++ Q) (mvLay ms ++ (capBlk S l d).map (whL (m.pre ++ m.lsrc ++ R) Q) ++
        m'.lay) := by
    have := dg_ichg (RD := RD) (k := k) (μ := μ) (s₀ := w₀) (t₀ := m.pre ++ m.ltgt ++ R ++ S ++ Q) (mvLay ms) []
      m.pre Q m.sChain_loc hB
    rw [Mv.lay_eq, Mv.lay_eq, hv]
    simp only [m', Mv.reCtx_loc, Mv.reCtx_pre, Mv.reCtx_post]
    wnf at this ⊢
    exact this
  have hsrc : m.src = (m.pre ++ m.lsrc ++ R) ++ [l.dual] ++ S ++ [l] ++ Q := by
    rw [Mv.src_eq, hv]; simp
  have h1 := hIH (m.pre ++ m.lsrc ++ R) S Q l d (hsrc ▸ hms) (by omega)
  have hm' : m'.src = m.pre ++ m.lsrc ++ R ++ S ++ Q := by
    simp only [m', Mv.src_eq, Mv.reCtx_pre, Mv.reCtx_post, Mv.reCtx_lsrc]; simp
  have hm't : m'.tgt = m.pre ++ m.ltgt ++ R ++ S ++ Q := by
    simp only [m', Mv.tgt_eq, Mv.reCtx_pre, Mv.reCtx_post, Mv.reCtx_ltgt]; simp
  have h2 := capTarget_comp_mv h1 m' hm'
  rw [hm't] at h2
  have hB' := (sChain_capBlk S l d).whisk (m.pre ++ m.lsrc ++ R) Q
  have hc1 : SChain w₀ (mvLay ms ++ (capBlk S l d).map (whL (m.pre ++ m.lsrc ++ R) Q))
      (m.pre ++ m.lsrc ++ R ++ S ++ Q) :=
    hms.sChain.append (by simpa [hsrc] using hB')
  have hc2 : SChain (m.pre ++ m.lsrc ++ R ++ S ++ Q) m'.lay (m.pre ++ m.ltgt ++ R ++ S ++ Q) := by
    simpa [hm', hm't] using m'.sChain_lay
  rw [e, ← dg_comp hc1 hc2]
  have hcc : ccnt m'.lay = ccnt m.lay := by
    simp only [m', Mv.ccnt_lay_eq_loc, Mv.reCtx_loc]
  rw [hcc] at h2
  refine capTarget_mono (le_of_eq ?_) h2
  omega

/-- A move to the right of the block commutes with it. -/
theorem push_disjR {c : ℕ} {ms : List (Mv I)} (hIH : PushHyp RD k μ w₀ c ms) {m : Mv I}
    (hms : MvChain w₀ ms m.src) {P S Q : List (Letter I)} {l : Letter I} (d : ℕ)
    (R : List (Letter I)) (hQ : Q = R ++ m.ltgt ++ m.post)
    (hu : m.pre = P ++ [l.dual] ++ S ++ [l] ++ R) (hc : ccnt (mvLay ms) + ccnt m.lay + S.length ≤ c) :
    dg RD k μ w₀ (P ++ S ++ Q) (mvLay ms ++ m.lay ++ (capBlk S l d).map (whL P Q)) ∈
      CapTarget RD k μ w₀ (P ++ S ++ Q) (ccnt (mvLay ms) + ccnt m.lay + S.length) := by
  subst hQ
  set m' := m.reCtx (P ++ S ++ R) m.post
  have hA := (sChain_capBlk S l d).whisk [] R
  have e : dg RD k μ w₀ (P ++ S ++ (R ++ m.ltgt ++ m.post))
      (mvLay ms ++ m.lay ++ (capBlk S l d).map (whL P (R ++ m.ltgt ++ m.post))) =
      dg RD k μ w₀ (P ++ S ++ (R ++ m.ltgt ++ m.post))
        (mvLay ms ++ (capBlk S l d).map (whL P (R ++ m.lsrc ++ m.post)) ++ m'.lay) := by
    have := dg_ichg (RD := RD) (k := k) (μ := μ) (s₀ := w₀) (t₀ := P ++ S ++ (R ++ m.ltgt ++ m.post))
      (mvLay ms) [] P m.post hA m.sChain_loc
    rw [Mv.lay_eq, Mv.lay_eq, hu]
    simp only [m', Mv.reCtx_loc, Mv.reCtx_pre, Mv.reCtx_post]
    wnf at this ⊢
    exact this.symm
  have hsrc : m.src = P ++ [l.dual] ++ S ++ [l] ++ (R ++ m.lsrc ++ m.post) := by
    rw [Mv.src_eq, hu]; simp
  have h1 := hIH P S (R ++ m.lsrc ++ m.post) l d (hsrc ▸ hms) (by omega)
  have hm' : m'.src = P ++ S ++ (R ++ m.lsrc ++ m.post) := by
    simp only [m', Mv.src_eq, Mv.reCtx_pre, Mv.reCtx_post, Mv.reCtx_lsrc]; simp
  have hm't : m'.tgt = P ++ S ++ (R ++ m.ltgt ++ m.post) := by
    simp only [m', Mv.tgt_eq, Mv.reCtx_pre, Mv.reCtx_post, Mv.reCtx_ltgt]; simp
  have h2 := capTarget_comp_mv h1 m' hm'
  rw [hm't] at h2
  have hB' := (sChain_capBlk S l d).whisk P (R ++ m.lsrc ++ m.post)
  have hc1 : SChain w₀ (mvLay ms ++ (capBlk S l d).map (whL P (R ++ m.lsrc ++ m.post)))
      (P ++ S ++ (R ++ m.lsrc ++ m.post)) :=
    hms.sChain.append (by simpa [hsrc] using hB')
  have hc2 : SChain (P ++ S ++ (R ++ m.lsrc ++ m.post)) m'.lay (P ++ S ++ (R ++ m.ltgt ++ m.post)) := by
    simpa [hm', hm't] using m'.sChain_lay
  rw [e, ← dg_comp hc1 hc2]
  have hcc : ccnt m'.lay = ccnt m.lay := by
    simp only [m', Mv.ccnt_lay_eq_loc, Mv.reCtx_loc]
  rw [hcc] at h2
  refine capTarget_mono (le_of_eq ?_) h2
  omega

/-- Concluding from an equation with a block of the induction hypothesis followed by moves. -/
theorem push_of_eq {c t : ℕ} {ms : List (Mv I)} (hIH : PushHyp RD k μ w₀ c ms)
    {T P S Q : List (Letter I)} {l : Letter I} {d : ℕ} {Z : List (LayerData I)}
    (hms : MvChain w₀ ms (P ++ [l.dual] ++ S ++ [l] ++ Q)) (ns : List (Mv I))
    (hns : MvChain (P ++ S ++ Q) ns T)
    (E : dg RD k μ w₀ T (mvLay ms ++ Z) =
      dg RD k μ w₀ T (mvLay ms ++ (capBlk S l d).map (whL P Q) ++ mvLay ns))
    (hc : ccnt (mvLay ms) + S.length ≤ c) (ht : ccnt (mvLay ms) + S.length + ccnt (mvLay ns) ≤ t) :
    dg RD k μ w₀ T (mvLay ms ++ Z) ∈ CapTarget RD k μ w₀ T t := by
  rw [E, ← dg_comp (hms.sChain.append (by simpa using (sChain_capBlk S l d).whisk P Q)) hns.sChain]
  exact capTarget_mono ht (capTarget_comp_mvs (hIH P S Q l d hms hc) hns)

/-- Concluding from a relation modulo lower terms with a block of the induction hypothesis
followed by moves. -/
theorem push_of_sub {c c' t : ℕ} (hF : LowHyp RD k μ w₀ c) {ms : List (Mv I)}
    (hIH : PushHyp RD k μ w₀ c ms)
    {T P S Q : List (Letter I)} {l : Letter I} {d : ℕ} {Z : List (LayerData I)}
    (hms : MvChain w₀ ms (P ++ [l.dual] ++ S ++ [l] ++ Q)) (ns : List (Mv I))
    (hns : MvChain (P ++ S ++ Q) ns T)
    (E : dg RD k μ w₀ T (mvLay ms ++ Z) -
      dg RD k μ w₀ T (mvLay ms ++ (capBlk S l d).map (whL P Q) ++ mvLay ns) ∈ LeL RD k μ w₀ T c')
    (hc' : c' < c) (hc't : c' ≤ t)
    (hc : ccnt (mvLay ms) + S.length ≤ c) (ht : ccnt (mvLay ms) + S.length + ccnt (mvLay ns) ≤ t) :
    dg RD k μ w₀ T (mvLay ms ++ Z) ∈ CapTarget RD k μ w₀ T t :=
  capT_of_sub hF hc' hc't E (by
    have := push_of_eq hIH hms ns hns (Z := (capBlk S l d).map (whL P Q) ++ mvLay ns) (by
      rw [List.append_assoc]) hc ht
    rwa [← List.append_assoc] at this)

/-- Concluding from an equation with a move diagram. -/
theorem push_of_mv {t : ℕ} {ms : List (Mv I)} {T : List (Letter I)} {Z : List (LayerData I)}
    (ns : List (Mv I)) (hch : MvChain w₀ (ms ++ ns) T)
    (E : dg RD k μ w₀ T (mvLay ms ++ Z) = dg RD k μ w₀ T (mvLay (ms ++ ns)))
    (ht : ccnt (mvLay (ms ++ ns)) ≤ t) :
    dg RD k μ w₀ T (mvLay ms ++ Z) ∈ CapTarget RD k μ w₀ T t := by
  rw [E]
  exact Submodule.mem_sup_left (dg_mvLay_mem_mvSp hch ht)

variable [DecidableEq I]

/-- **The cap push through a dot.** -/
theorem push_dot {c : ℕ} (hF : LowHyp RD k μ w₀ c) {ms : List (Mv I)}
    (hIH : PushHyp RD k μ w₀ c ms) (u : List (Letter I)) (x : Letter I) (v : List (Letter I))
    (hms : MvChain w₀ ms (Mv.dot u x v).src) : PushGoal RD k μ w₀ c ms (Mv.dot u x v) := by
  intro P S Q l d htgt hc
  have hcm : ccnt (Mv.dot u x v).lay = 0 := rfl
  rw [hcm] at hc ⊢
  rcases posDot (u := u) (x := x) (v := v) htgt with
    ⟨R, hP, hv⟩ | ⟨hu, hx, hv⟩ | ⟨S₁, S₂, hS, hu, hv⟩ | ⟨hu, hx, hv⟩ | ⟨R, hQ, hu⟩
  · exact push_disjL hIH hms d R hP hv (by simpa using hc)
  · -- a dot on `A`
    subst u x v
    rw [List.append_assoc (mvLay ms)]
    refine push_of_eq hIH (P := P) (S := S) (Q := Q) (l := l) (d := d + 1) ?hms00 [] rfl ?E00 ?hc00 ?ht00
    case hms00 => simpa [Mv.src] using hms
    case hc00 => omega
    case ht00 => simp
    refine dg_step_free (mvLay ms) [] P Q (capBlk_dotA (RD := RD) (k := k) _ S l d) ?_ ?_
      (by simp) (by simp [capBlk]) ?_ ?_
    · exact (show SChain _ [([], .dot l.dual, S ++ [l])] _ from ⟨rfl, rfl⟩).append (sChain_capBlk S l d)
    · exact sChain_capBlk S l (d + 1)
    · simp only [Mv.lay]; wnf
    · simp
  · -- a dot on a strand of the block
    subst S u v
    rw [List.append_assoc (mvLay ms)]
    refine push_of_sub hF hIH (P := P) (S := S₁ ++ [x] ++ S₂) (Q := Q) (l := l) (d := d)
      (c' := ccnt (mvLay ms) + (S₁ ++ [x] ++ S₂).length - 1) ?hms10
      [Mv.dot (P ++ S₁) x (S₂ ++ Q)] ?hns10 ?E10 ?h110 ?h210 ?h310 ?h410
    case hms10 => simpa [Mv.src] using hms
    case hns10 => exact ⟨by simp [Mv.src], by simp [Mv.tgt, MvChain]⟩
    case h110 => simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢; omega
    case h210 => simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢; omega
    case h310 => simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢; omega
    case h410 => rfl
    refine dg_mod_free (mvLay ms) [] P Q (capBlk_dotS (RD := RD) (k := k) _ S₁ S₂ x l d) ?_ ?_
      (by simp) (by simp [capBlk]) ?_ ?_ (by simp; omega)
    · exact (show SChain _ [([l.dual] ++ S₁, .dot x, S₂ ++ [l])] _ from ⟨by simp, by simp⟩).append
        (sChain_capBlk _ l d)
    · exact (sChain_capBlk _ l d).append (show SChain _ [(S₁, .dot x, S₂)] _ from ⟨by simp, by simp⟩)
    · simp only [Mv.lay]; wnf
    · simp only [mvLay_singleton, Mv.lay]; wnf
  · -- a dot on `B`
    subst u x v
    rw [List.append_assoc (mvLay ms)]
    rcases S with _ | ⟨s, S⟩
    · refine push_of_eq hIH (P := P) (S := []) (Q := Q) (l := l) (d := d + 1) ?hms21 [] rfl ?E21 ?hc21 ?ht21
      case hms21 => simpa [Mv.src] using hms
      case hc21 => simpa using hc
      case ht21 => simp
      refine dg_step_free (mvLay ms) [] P Q (capBlk_dotB_nil (RD := RD) (k := k) _ l d) ?_ ?_
        (by simp) (by simp [capBlk]) ?_ ?_
      · exact (show SChain _ [([l.dual], .dot l, [])] _ from ⟨rfl, rfl⟩).append (sChain_capBlk [] l d)
      · exact sChain_capBlk [] l (d + 1)
      · simp only [Mv.lay]; wnf
      · simp
    · refine push_of_sub hF hIH (P := P) (S := s :: S) (Q := Q) (l := l) (d := d + 1)
        (c' := ccnt (mvLay ms) + (s :: S).length - 1) ?hms22 [] rfl ?E22 ?h122 ?h222 ?h322 ?h422
      case hms22 => simpa [Mv.src] using hms
      case h122 => simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢; omega
      case h222 => simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢; omega
      case h322 => simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢; omega
      case h422 => simp
      refine dg_mod_free (mvLay ms) [] P Q (capBlk_dotB (RD := RD) (k := k) _ (s :: S) l d) ?_ ?_
        (by simp) (by simp [capBlk]) ?_ ?_ (by simp)
      · exact (show SChain _ [([l.dual] ++ s :: S, .dot l, [])] _ from ⟨by simp, by simp⟩).append
          (sChain_capBlk _ l d)
      · exact sChain_capBlk _ l (d + 1)
      · simp only [Mv.lay]; wnf
      · simp
  · exact push_disjR hIH hms d R hQ hu (by simpa using hc)

/-- **The cap push through a crossing.** -/
theorem push_cross {c : ℕ} (hF : LowHyp RD k μ w₀ c) {ms : List (Mv I)}
    (hIH : PushHyp RD k μ w₀ c ms) (u : List (Letter I)) (l₁ l₂ : Letter I) (v : List (Letter I))
    (hms : MvChain w₀ ms (Mv.cross u l₁ l₂ v).src) :
    PushGoal RD k μ w₀ c ms (Mv.cross u l₁ l₂ v) := by
  intro P S Q l d htgt hc
  have hcm : ccnt (Mv.cross u l₁ l₂ v).lay = 1 := by simp [Mv.lay, ccnt_map_whL]
  rcases posPair (u := u) (y := l₂) (z := l₁) (v := v) htgt with
    ⟨R, hP, hv⟩ | ⟨hP, h1, hv⟩ | ⟨hu, h2, S', hS, hv⟩ | ⟨hu, h2, hS, h1, hv⟩ |
      ⟨S₁, S₂, hS, hu, hv⟩ | ⟨S', hS, h1, hu, hv⟩ | ⟨hu, h2, hQ⟩ | ⟨R, hQ, hu⟩
  · exact push_disjL hIH hms d R hP hv hc
  · -- the strand to the left of `A` enters the block
    subst P l₁ v
    rw [hcm] at hc ⊢
    rw [List.append_assoc (mvLay ms)]
    refine push_of_sub hF hIH (P := u) (S := l₂ :: S) (Q := Q) (l := l) (d := d)
      (c' := ccnt (mvLay ms) + S.length) ?hmsA [] (by simp [MvChain]) ?EA ?h1A ?h2A ?h3A ?h4A
    case hmsA => simpa [Mv.src] using hms
    case h1A => omega
    case h2A => omega
    case h3A => simp only [List.length_cons] at hc ⊢; omega
    case h4A => simp; omega
    refine dg_mod_free (mvLay ms) [] u Q (capBlk_enterL (RD := RD) (k := k) _ S l₂ l d) ?_ ?_
      (by simp [xLay_ne_nil]) (by simp [capBlk]) ?_ ?_ (by simp)
    · have h1 := (sChain_xLay l.dual l₂).whisk [] (S ++ [l])
      have h2 := (sChain_capBlk S l d).whisk [l₂] []
      simpa using h1.append (by simpa using h2)
    · exact sChain_capBlk _ l d
    · simp only [Mv.lay]; wnf
    · simp
  · -- a crossing of the first strand of the block with `A`
    subst u l₂ S v
    rw [hcm] at hc ⊢
    rw [List.append_assoc (mvLay ms)]
    refine capT_of_leL hF (c' := ccnt (mvLay ms) + (S'.length + 1)) (by simp at hc; omega)
      (by simp) ?_
    refine dg_mem_free (mvLay ms) [] P Q (capBlk_sA (RD := RD) (k := k) _ l₁ S' l d) ?_
      (by simp [xLay_ne_nil]) ?_ (by simp)
    · have h1 := (sChain_xLay l₁ l.dual).whisk [] (S' ++ [l])
      simpa using h1.append (by simpa using sChain_capBlk (l₁ :: S') l d)
    · simp only [Mv.lay]; wnf
  · -- a crossing of `B` and `A`
    subst u l₂ S l₁ v
    rw [hcm] at hc ⊢
    rw [List.append_assoc (mvLay ms)]
    refine capT_of_leL hF (c' := ccnt (mvLay ms) + 0) (by simp at hc; omega) (by simp) ?_
    refine dg_mem_free (mvLay ms) [] P Q (capBlk_AB (RD := RD) (k := k) _ l d) ?_
      (by simp [xLay_ne_nil]) ?_ (by simp)
    · exact (sChain_xLay l l.dual).append (by simpa using sChain_capBlk [] l d)
    · simp only [Mv.lay]; wnf
  · -- a crossing inside the block (Reidemeister 3)
    subst S u v
    rw [hcm] at hc ⊢
    rw [List.append_assoc (mvLay ms)]
    refine push_of_sub hF hIH (P := P) (S := S₁ ++ [l₁, l₂] ++ S₂) (Q := Q) (l := l) (d := d)
      (c' := ccnt (mvLay ms) + (S₁ ++ [l₂, l₁] ++ S₂).length) ?hmsC
      [Mv.cross (P ++ S₁) l₁ l₂ (S₂ ++ Q)] ?hnsC ?EC ?h1C ?h2C ?h3C ?h4C
    case hmsC => simpa [Mv.src] using hms
    case hnsC => exact ⟨by simp [Mv.src], by simp [Mv.tgt, MvChain]⟩
    case h1C => simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢; omega
    case h2C => simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢; omega
    case h3C => simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢; omega
    case h4C =>
      simp only [mvLay_singleton, Mv.lay, ccnt_map_whL, ccnt_xLay, List.length_append,
        List.length_cons, List.length_nil]; omega
    refine dg_mod_free (mvLay ms) [] P Q (capBlk_crossS (RD := RD) (k := k) _ S₁ S₂ l₁ l₂ l d)
      ?_ ?_ (by simp [xLay_ne_nil]) (by simp [capBlk]) ?_ ?_ (by simp)
    · have h1 := (sChain_xLay l₁ l₂).whisk ([l.dual] ++ S₁) (S₂ ++ [l])
      simpa using h1.append (by simpa using sChain_capBlk (S₁ ++ [l₂, l₁] ++ S₂) l d)
    · have h2 := (sChain_xLay l₁ l₂).whisk S₁ S₂
      simpa using (sChain_capBlk (S₁ ++ [l₁, l₂] ++ S₂) l d).append (by simpa using h2)
    · simp only [Mv.lay]; wnf
    · simp only [mvLay_singleton, Mv.lay]; wnf
  · -- a crossing of the last strand of the block with `B`
    subst S l₁ u v
    rw [hcm] at hc ⊢
    rw [List.append_assoc (mvLay ms)]
    refine capT_of_leL hF (c' := ccnt (mvLay ms) + (S'.length + 1)) (by simp at hc; omega)
      (by simp) ?_
    refine dg_mem_free (mvLay ms) [] P Q (capBlk_sB (RD := RD) (k := k) _ S' l₂ l d) ?_
      (by simp [xLay_ne_nil]) ?_ (by simp)
    · have h1 := (sChain_xLay l l₂).whisk ([l.dual] ++ S') []
      simpa using h1.append (by simpa using sChain_capBlk (S' ++ [l₂]) l d)
    · simp only [Mv.lay]; wnf
  · -- the strand to the right of `B` enters the block
    subst u l₂ Q
    rw [hcm] at hc ⊢
    rw [List.append_assoc (mvLay ms)]
    refine push_of_eq hIH (P := P) (S := S ++ [l₁]) (Q := v) (l := l) (d := d) ?hmsE [] (by simp [MvChain]) ?EE
      ?hcE ?htE
    case hmsE => simpa [Mv.src] using hms
    case hcE => simp only [List.length_append, List.length_cons, List.length_nil] at hc ⊢; omega
    case htE => simp; omega
    rw [mvLay_nil, List.append_nil, ← capBlk_enterR]
    simp only [Mv.lay]
    wnf
  · exact push_disjR hIH hms d R hQ hu hc

omit [DecidableEq I] in
theorem dual_inj {l l' : Letter I} (h : l'.dual = l.dual) : l' = l := by
  simpa using congrArg Letter.dual h

omit [DecidableEq I] in
/-- Dots on the strands to the right of a region, followed by bubbles, after a move diagram. -/
theorem dotBubSpan_le_capTarget {ms : List (Mv I)} {P Q : List (Letter I)}
    (hms : MvChain w₀ ms (P ++ Q)) :
    dotBubSpan RD k μ w₀ (P ++ Q) (mvLay ms) [] P Q ≤
      CapTarget RD k μ w₀ (P ++ Q) (ccnt (mvLay ms)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨D, δ, hD, hc, hδ, rfl⟩
  obtain ⟨ns, h1, h2, h3⟩ := exists_mv_of_dots D hD hc
  refine Submodule.mem_sup_left (Submodule.subset_span ⟨ms ++ mvWh P [] ns, δ, ?_, ?_, hδ, ?_⟩)
  · exact MvChain.append hms (by simpa using h2.wh P [])
  · rw [mvLay_append, ccnt_append, ccnt_mvLay_mvWh, h3]; simp
  · rw [mvLay_append, mvLay_mvWh, h1, List.append_nil]

variable (hSL : SimplyLaced C)
include hSL

/-- **The cap push through a cup.** -/
theorem push_cup {c : ℕ} (hF : LowHyp RD k μ w₀ c) {ms : List (Mv I)}
    (hIH : PushHyp RD k μ w₀ c ms) (u : List (Letter I)) (l' : Letter I) (v : List (Letter I))
    (hms : MvChain w₀ ms (Mv.cup u l' v).src) :
    PushGoal RD k μ w₀ c ms (Mv.cup u l' v) := by
  intro P S Q l d htgt hc
  have hcm : ccnt (Mv.cup u l' v).lay = 0 := rfl
  rcases posPair (u := u) (y := l') (z := l'.dual) (v := v) htgt with
    ⟨R, hP, hv⟩ | ⟨hP, h1, hv⟩ | ⟨hu, h2, S', hS, hv⟩ | ⟨hu, h2, hS, h1, hv⟩ |
      ⟨S₁, S₂, hS, hu, hv⟩ | ⟨S', hS, h1, hu, hv⟩ | ⟨hu, h2, hQ⟩ | ⟨R, hQ, hu⟩
  · exact push_disjL hIH hms d R hP hv hc
  · -- a cup creating a strand to the left and `A`: zigzag
    obtain rfl := dual_inj h1
    subst P v
    rw [hcm] at hc ⊢
    rw [List.append_assoc (mvLay ms)]
    have hns : MvChain (u ++ (S ++ [l']) ++ Q) (mvWh u Q (lmMv S l' ++ dotMv d [] l' S))
        (u ++ (l' :: S) ++ Q) := by
      refine MvChain.wh u Q (MvChain.append (mvChain_lmMv S l') ?_)
      simpa using mvChain_dotMv d [] l' S
    refine push_of_mv (mvWh u Q (lmMv S l' ++ dotMv d [] l' S))
      (MvChain.append (by simpa [Mv.src] using hms) (by simpa using hns)) ?_ ?_
    · rw [mvLay_append, mvLay_mvWh, mvLay_append, mvLay_lmMv, mvLay_dotMv]
      refine dg_step RD k μ (mvLay ms) [] u Q (capBlk_cupAleft (RD := RD) (k := k) _ S l' d)
        (by simpa [Mv.src] using hms.sChain) (by simp) ?_ (by simp)
      simp only [Mv.lay]; wnf
    · rw [mvLay_append, ccnt_append, ccnt_mvLay_mvWh, mvLay_append, ccnt_append, mvLay_lmMv,
        mvLay_dotMv, ccnt_lmLc, ccnt_replicate_dot]
      simp
  · -- a cup creating `A` and the first strand of the block: a curl
    subst u l' S v
    rw [hcm] at hc ⊢
    try simp only [Letter.dual_dual] at hc hms ⊢
    rw [List.append_assoc (mvLay ms)]
    refine capT_of_leL hF (c' := ccnt (mvLay ms) + S'.length) (by simp at hc; omega)
      (by simp) ?_
    refine dg_mem_free (mvLay ms) [] P Q (capBlk_cupAs (RD := RD) (k := k) _ S' l d) ?_
      (by simp) ?_ (by simp)
    · exact (show SChain (S' ++ [l]) [([], .cup l.dual, S' ++ [l])] (l.dual :: l :: (S' ++ [l]))
        from ⟨rfl, by simp⟩).append (by simpa using sChain_capBlk (l :: S') l d)
    · simp only [Mv.lay]; wnf
  · -- a cup creating `A` and `B`: a bubble
    subst u l' S v
    rw [hcm] at hc ⊢
    rw [show P ++ [] ++ Q = P ++ Q by simp, List.length_nil, add_zero, add_zero]
    have hpre : SChain w₀ (mvLay ms) (P ++ Q) := by simpa [Mv.src] using hms.sChain
    have hpre' : SChain w₀ (mvLay ms) (P ++ [] ++ Q) := by simpa using hpre
    have e := ctxL_dg RD k μ (s₀ := w₀) (t₀ := P ++ Q) (pre := mvLay ms) (u := P) (v := Q)
      (post := []) (s := []) (t := []) hpre' (by simp) ([([], .cup l.dual, [])] ++ capBlk [] l d)
    have h := slideOutAny (RD := RD) (k := k) hSL μ Q P (S := w₀) (T := P ++ Q) (mvLay ms) []
      hpre rfl _ (isBub_capBlk_nil (RD := RD) (k := k) (wt RD μ Q) l d)
    rw [e] at h
    have h' := dotBubSpan_le_capTarget (RD := RD) (k := k) (by simpa [Mv.src] using hms) h
    convert h' using 2
    simp only [Mv.lay]; wnf
  · -- a cup creating two strands of the block
    subst S u v
    rw [hcm] at hc ⊢
    rw [List.append_assoc (mvLay ms)]
    refine capT_of_leL hF (c' := ccnt (mvLay ms) + ((S₁ ++ S₂).length + 1))
      (by simp at hc ⊢; omega) (by simp; omega) ?_
    refine dg_mem_free (mvLay ms) [] P Q (capBlk_cupSS (RD := RD) (k := k) _ S₁ S₂ l' l d) ?_
      (by simp) ?_ (by simp)
    · exact (show SChain _ [([l.dual] ++ S₁, .cup l', S₂ ++ [l])] _ from ⟨by simp, by simp⟩).append
        (sChain_capBlk _ l d)
    · simp only [Mv.lay]; wnf
  · -- a cup creating the last strand of the block and `B`: a curl
    obtain rfl : l' = l.dual := dual_inj (by simpa using h1)
    subst S u v
    rw [hcm] at hc ⊢
    rw [List.append_assoc (mvLay ms)]
    refine capT_of_leL hF (c' := ccnt (mvLay ms) + S'.length) (by simp at hc; omega)
      (by simp) ?_
    refine dg_mem_free (mvLay ms) [] P Q (capBlk_cupsB (RD := RD) (k := k) _ S' l d) ?_
      (by simp) ?_ (by simp)
    · have h := (show SChain ([l.dual] ++ S') [([l.dual] ++ S', .cup l.dual, [])]
        ([l.dual] ++ S' ++ [l.dual, l]) from ⟨by simp, by simp⟩).append
        (by simpa using sChain_capBlk (S' ++ [l.dual]) l d)
      simpa using h
    · simp only [Mv.lay]; wnf
  · -- a cup creating `B` and a strand to the right: zigzag
    subst u l' Q
    rw [hcm] at hc ⊢
    rw [List.append_assoc (mvLay ms)]
    by_cases hS : S = []
    · subst hS
      refine push_of_mv (mvWh P v (dotMv d [] l.dual [])) (MvChain.append
        (by simpa [Mv.src] using hms) (by simpa using (mvChain_dotMv d [] l.dual []).wh P v)) ?_ ?_
      · rw [mvLay_append, mvLay_mvWh, mvLay_dotMv]
        refine dg_step RD k μ (mvLay ms) [] P v (capBlk_cupBright_nil (RD := RD) (k := k) _ l d)
          (by simpa [Mv.src] using hms.sChain) (by simp) ?_ (by simp)
        simp only [Mv.lay]; wnf
      · rw [mvLay_append, ccnt_append, ccnt_mvLay_mvWh, mvLay_dotMv, ccnt_replicate_dot]; simp
    · have hns : MvChain (P ++ ([l.dual] ++ S) ++ v) (mvWh P v (dotMv d [] l.dual S ++ rmMv l.dual S))
          (P ++ (S ++ [l.dual]) ++ v) := by
        refine MvChain.wh P v (MvChain.append (by simpa using mvChain_dotMv d [] l.dual S) ?_)
        exact mvChain_rmMv l.dual S
      refine capT_of_sub hF (c' := ccnt (mvLay ms) + (S.length - 1)) ?_ (by omega)
        (b := dg RD k μ w₀ _ (mvLay (ms ++ mvWh P v (dotMv d [] l.dual S ++ rmMv l.dual S)))) ?_ ?_
      · have := List.length_pos_of_ne_nil hS; omega
      · rw [mvLay_append, mvLay_mvWh, mvLay_append, mvLay_rmMv, mvLay_dotMv]
        refine dg_mod_free (mvLay ms) [] P v (capBlk_cupBright (RD := RD) (k := k) _ S l d) ?_ ?_
          (by simp) ?_ ?_ ?_ (by simp)
        · have h := (show SChain ([l.dual] ++ S) [([l.dual] ++ S, .cup l, [])]
            ([l.dual] ++ S ++ [l, l.dual]) from ⟨by simp, by simp⟩).append
            (by simpa using (sChain_capBlk S l d).whisk [] [l.dual])
          simpa using h
        · have h := (SChain.replicate d [] l.dual S).append (sChain_lmRc l.dual S)
          simpa using h
        · obtain ⟨s, S', rfl⟩ := List.exists_cons_of_ne_nil hS
          simp [lmRc, xLay_ne_nil]
        · simp only [Mv.lay]; wnf
        · simp
      · refine Submodule.mem_sup_left (dg_mvLay_mem_mvSp ?_ ?_)
        · exact MvChain.append (by simpa [Mv.src] using hms) (by simpa using hns)
        · rw [mvLay_append, ccnt_append, ccnt_mvLay_mvWh, mvLay_append, ccnt_append, mvLay_rmMv,
            mvLay_dotMv, ccnt_lmRc, ccnt_replicate_dot]; simp
  · exact push_disjR hIH hms d R hQ hu hc

/-- **The cap push**: a cap block on top of a move diagram lies in `CapTarget`. -/
theorem capPush {c : ℕ} (hF : LowHyp RD k μ w₀ c) : ∀ ms : List (Mv I), PushHyp RD k μ w₀ c ms := by
  intro ms
  induction ms using List.reverseRecOn with
  | nil => exact pushHyp_nil c
  | append_singleton ms m ih =>
    intro P S Q l d hch hc
    obtain ⟨hms, htgt⟩ := MvChain.of_snoc hch
    rw [mvLay_append, mvLay_singleton] at hc ⊢
    rw [ccnt_append] at hc ⊢
    cases m with
    | dot u x v => exact push_dot hF ih u x v hms P S Q l d htgt hc
    | cross u l₁ l₂ v => exact push_cross hF ih u l₁ l₂ v hms P S Q l d htgt hc
    | cup u l' v => exact push_cup hSL hF ih u l' v hms P S Q l d htgt hc

/-- Composing with a cap preserves `CapTarget`. -/
theorem capTarget_comp_cap {c c₁ : ℕ} (hF : LowHyp RD k μ w₀ c) (hc₁ : c₁ ≤ c)
    {P Q : List (Letter I)} {l : Letter I} {f}
    (hf : f ∈ CapTarget RD k μ w₀ (P ++ [l.dual, l] ++ Q) c₁) :
    f ≫ dg RD k μ (P ++ [l.dual, l] ++ Q) (P ++ Q) [(P, .cap l, Q)] ∈
      CapTarget RD k μ w₀ (P ++ Q) c₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
  rw [Preadditive.add_comp]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (thruShort_comp hb _))
  clear hf hb
  induction ha using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨ms, β, hch, hcc, hβ, rfl⟩ := hg
    rw [Category.assoc, bubAt_comm, ← Category.assoc,
      dg_comp hch.sChain (show SChain (P ++ [l.dual, l] ++ Q) [(P, .cap l, Q)] (P ++ Q) from
        ⟨by simp, by simp⟩)]
    have h := capPush hSL hF ms P [] Q l 0 (by simpa using hch) (by simp; omega)
    have e : (capBlk [] l 0).map (whL P Q) = [(P, .cap l, Q)] := by simp [capBlk, lmLc]
    rw [e, show P ++ [] ++ Q = P ++ Q by simp, List.length_nil, add_zero] at h
    exact capTarget_mono hcc (capTarget_comp_bubAt h hβ)
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hx

variable (μ w₀) in
/-- **Elimination of caps** (simply-laced): every normal-form diagram `E_{w₀} 1_μ ⟶ E_v 1_μ` with
at most `c` crossings is a linear combination of move diagrams with at most `c` crossings followed
by bubble monomials, modulo 2-morphisms factoring through sequences shorter than `w₀`. -/
theorem capElim : ∀ (c : ℕ) (v : List (Letter I)) (L : List (LayerData I)), ccnt L ≤ c →
    dg RD k μ w₀ v L ∈ CapTarget RD k μ w₀ v c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  have hF : LowHyp RD k μ w₀ c := fun c' hc' v L hL => ihc c' hc' v L hL
  suffices H : ∀ (L : List (LayerData I)) (v : List (Letter I)), ccnt L ≤ c →
      dg RD k μ w₀ v L ∈ CapTarget RD k μ w₀ v (ccnt L) from
    fun v L hL => capTarget_mono hL (H L v hL)
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro v _
    by_cases h : w₀ = v
    · subst h
      exact Submodule.mem_sup_left (dg_mvLay_mem_mvSp (ms := []) rfl le_rfl)
    · rw [dg_of_not (show ¬ SChain w₀ [] v from h)]; exact Submodule.zero_mem _
  | append_singleton L x ih =>
    intro v hL
    rw [ccnt_append] at hL ⊢
    by_cases h : SChain w₀ (L ++ [x]) v
    · obtain ⟨v', h1, h2⟩ := SChain.split h
      rw [← dg_comp h1 h2]
      have hL' := ih v' (by omega)
      obtain ⟨a, g, b⟩ := x
      obtain ⟨hv', hv⟩ := h2
      have hv'' : a ++ g.cod ++ b = v := hv
      subst hv' hv''
      cases g with
      | dot l => exact capTarget_comp_mv hL' (Mv.dot a l b) rfl
      | cross ε i j =>
        have e : (Mv.cross a (ε, i) (ε, j) b).lay = [(a, .cross ε i j, b)] := by
          cases ε <;> simp [Mv.lay]
        have := capTarget_comp_mv hL' (Mv.cross a (ε, i) (ε, j) b) rfl
        rw [e] at this
        exact this
      | cup l => exact capTarget_comp_mv hL' (Mv.cup a l b) (by simp [Mv.src])
      | cap l =>
        have := capTarget_comp_cap hSL hF (c₁ := ccnt L) (by omega) (P := a) (Q := b) (l := l) hL'
        rw [show a ++ (Shape.cap l).cod ++ b = a ++ b by simp, ccnt_single_cap, add_zero]
        exact this
    · rw [dg_of_not h]; exact Submodule.zero_mem _

end Push

end Categorification.KL3.Diagram
