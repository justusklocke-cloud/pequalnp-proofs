import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Set vertex 9 false in the circuit made of the first gate and the 17 others. killTwo says that
-- every gate reading vertex 9 goes away (and every gate reading an AND or NOT gate that reads
-- it), and no gate is added. So three gates reading vertex 9 leave at most 15 gates, with the
-- same output wire sense. What remains is fewReaders: at most two gates name wire 9.
theorem PEqualNP.Outside.R_meta_4330_157
    (killTwo : ∀ (n : ℕ) (C : Circuit) (v : Fin n), FanInTwo C →
      (∀ x : Fin n → Bool, circuitFun n C (Function.update x v false) = true) ∨
      ∃ E : Circuit, FanInTwo E ∧
        E.size + List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (k : ℕ) => k == ↑v || (Nat.ble n k && (C.gates[k - n]?).any (fun (h : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (h.op.eval [Bool.false]).toNat) h.inputs).contains ↑v && !h.op.eval [Bool.true, Bool.false])))) C.gates ≤ C.size ∧
        ∀ x : Fin n → Bool, circuitFun n E x = circuitFun n C (Function.update x v false))
    (fewReaders : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size = (17 : ℕ) ∧ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.inputs.contains 9) x3.gates ≤ 2 →         have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => (x3.wires ({ gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x4 Bool.false;         (∀ (x10 : Fin (10 : ℕ) → Bool), (if x5 = Bool.true then !x9 x10 else x9 x10) = x1 x10) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit) (x12 : ℕ) (x13 : Bool),             PEqualNP.MetaComplexity.FanInTwo x11 ∧               x11.size ≤ (15 : ℕ) ∧                 have x14 : (Fin (10 : ℕ) → Bool) → Bool := fun (x14 : Fin (10 : ℕ) → Bool) => (x11.wires (List.ofFn x14)).getD x12 Bool.false;                 ∀ (x15 : Fin (10 : ℕ) → Bool), x15 (9 : Fin (10 : ℕ)) = Bool.false → (if x13 = Bool.true then !x14 x15 else x14 x15) = x1 x15) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size = (17 : ℕ) →         have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => (x3.wires ({ gates := [x2], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x4 Bool.false;         (∀ (x10 : Fin (10 : ℕ) → Bool), (if x5 = Bool.true then !x9 x10 else x9 x10) = x1 x10) →           ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit) (x12 : ℕ) (x13 : Bool),             PEqualNP.MetaComplexity.FanInTwo x11 ∧               x11.size ≤ (15 : ℕ) ∧                 have x14 : (Fin (10 : ℕ) → Bool) → Bool := fun (x14 : Fin (10 : ℕ) → Bool) => (x11.wires (List.ofFn x14)).getD x12 Bool.false;                 ∀ (x15 : Fin (10 : ℕ) → Bool), x15 (9 : Fin (10 : ℕ)) = Bool.false → (if x13 = Bool.true then !x14 x15 else x14 x15) = x1 x15 := by
  dsimp only
  intro g C o neg hg hfan hsize hcomp
  have hgate : ∀ (g : Gate), g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      ∀ Fv : ℕ → Bool,
      g.op.eval ((if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).map Fv)
        = g.op.eval (g.inputs.map Fv) := by
    intro g hg Fv
    obtain ⟨op, inputs⟩ := g
    rcases hg with h | h | h
    · have e : op = GateOp.and := h
      subst e
      rfl
    · have e : op = GateOp.or := h
      subst e
      rfl
    · have e : op = GateOp.not := h
      subst e
      cases inputs <;> rfl
  have hw : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
      ∀ w : List Bool,
      (gs.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = gs.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
    intro gs
    induction gs with
    | nil => intro _ w; rfl
    | cons g gs ih =>
      intro hg w
      have e : w ++ [g.op.eval ((if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).map
          fun i => w.getD i false)] = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] :=
        congrArg (fun v => w ++ [v]) (hgate g (hg g List.mem_cons_self) (fun i => w.getD i false))
      exact (congrArg (fun u => (gs.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) u) e).trans
        (ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _)
  have hall : ∀ g' ∈ g :: C.gates,
      g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | h
    · exact hg g' List.mem_cons_self
    · exact hfan g' h
  have hlen2 : ∀ g' : Gate, g'.inputs.length ≤ 2 →
      (if g'.op.eval [false] = true then g'.inputs.take 1 else g'.inputs).length ≤ 2 := by
    intro g' h
    split_ifs
    · simp only [List.length_take]
      omega
    · exact h
  by_cases hr : List.countP (fun (g : Gate) =>
      (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 9) C.gates ≤ 2
  · have hcount : List.countP (fun (g : Gate) => g.inputs.contains 9)
        (⟨C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate)), C.output⟩ : Circuit).gates
        = List.countP (fun (g : Gate) =>
          (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 9) C.gates := by
      show List.countP _ (C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))) = _
      rw [List.countP_map]
      rfl
    exact fewReaders ((fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate)) g) ⟨C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate)), C.output⟩ o neg
      (by
        intro g' hg'
        rcases List.mem_singleton.1 hg' with rfl
        exact ⟨(hall g List.mem_cons_self).1, hlen2 g (hall g List.mem_cons_self).2⟩)
      (by
        intro g' hg'
        obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg'
        exact ⟨(hfan g0 hg0).1, hlen2 g0 (hfan g0 hg0).2⟩)
      ⟨by
        show (C.gates.map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).length = 17
        rw [List.length_map]
        exact hsize, by rw [hcount]; exact hr⟩
      (by
        intro x
        have e : ((g :: C.gates).map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)
            = (g :: C.gates).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x) :=
          hw (g :: C.gates) (fun g' hg' => (hall g' hg').1) _
        have h1 := hcomp x
        show (if neg = true then !(((g :: C.gates).map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD o false
          else (((g :: C.gates).map (fun g : Gate => (⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩ : Gate))).foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).getD o false) = _
        rw [e]
        exact h1)
  · have hT : FanInTwo (⟨g :: C.gates, o⟩ : Circuit) := hall
    have hval : ∀ x : Fin 10 → Bool, circuitFun 10 (⟨g :: C.gates, o⟩ : Circuit) x
        = (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD o false := fun x => rfl
    have hsz : (⟨g :: C.gates, o⟩ : Circuit).size = 18 := by
      show (g :: C.gates).length = 18
      rw [List.length_cons]
      have : C.gates.length = 17 := hsize
      omega
    rcases killTwo 10 ⟨g :: C.gates, o⟩ 9 hT with hTr | ⟨E, hE, hEs, hEf⟩
    · refine ⟨⟨[⟨GateOp.and, []⟩], 10⟩, 10, neg, ?_, ?_, ?_⟩
      · intro g' hg'
        rcases List.mem_singleton.1 hg' with rfl
        exact ⟨Or.inl rfl, by simp⟩
      · show (1 : ℕ) ≤ 15
        omega
      · intro x hx
        have hup : Function.update x 9 false = x := by
          funext i
          by_cases h : i = 9
          · rw [h, Function.update_self, hx]
          · rw [Function.update_of_ne h]
        have h1 := hTr x
        rw [hup, hval] at h1
        have h2 := hcomp x
        rw [h1] at h2
        have h3 : ((⟨[⟨GateOp.and, []⟩], 10⟩ : Circuit).wires (List.ofFn x)).getD 10 false = true := by
          show (List.ofFn x ++ [true]).getD 10 false = true
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp
        rw [h3]
        exact h2
    · have key : ∀ (q : Gate → Bool) (m : ℕ),
          (∀ g' ∈ g :: C.gates,
            (if g'.op.eval [false] = true then g'.inputs.take 1 else g'.inputs).contains 9 = true →
              q g' = true) →
          E.size + List.countP q (g :: C.gates) ≤ m → E.size + 3 ≤ m := by
        intro q m hq hle
        have hm := List.countP_mono_left (l := g :: C.gates)
          (p := fun (g : Gate) =>
            (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 9)
          (q := q) hq
        have hcons : List.countP (fun (g : Gate) =>
              (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 9) C.gates
            ≤ List.countP (fun (g : Gate) =>
              (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).contains 9) (g :: C.gates) :=
          (List.sublist_cons_self g C.gates).countP_le
        omega
      have h18 : E.size + 3 ≤ (⟨g :: C.gates, o⟩ : Circuit).size := by
        refine key _ _ (fun g' hg' hc => ?_) hEs
        have hop := (hall g' hg').1
        have hl := (hall g' hg').2
        have hin : (9 : ℕ) ∈ List.take (2 - (g'.op.eval [false]).toNat) g'.inputs := by
          obtain ⟨op, inputs⟩ := g'
          rcases hop with h | h | h
          · have e : op = GateOp.and := h
            subst e
            have hc' : inputs.contains 9 = true := hc
            have : (9 : ℕ) ∈ inputs := by simpa using hc'
            show (9 : ℕ) ∈ List.take 2 inputs
            rw [List.take_of_length_le hl]
            exact this
          · have e : op = GateOp.or := h
            subst e
            have hc' : inputs.contains 9 = true := hc
            have : (9 : ℕ) ∈ inputs := by simpa using hc'
            show (9 : ℕ) ∈ List.take 2 inputs
            rw [List.take_of_length_le hl]
            exact this
          · have e : op = GateOp.not := h
            subst e
            have hc' : (inputs.take 1).contains 9 = true := hc
            have : (9 : ℕ) ∈ inputs.take 1 := by simpa using hc'
            exact this
        exact List.any_eq_true.2 ⟨9, hin, by simp⟩
      refine ⟨E, E.output, neg, hE, by omega, ?_⟩
      intro x hx
      have hup : Function.update x 9 false = x := by
        funext i
        by_cases h : i = 9
        · rw [h, Function.update_self, hx]
        · rw [Function.update_of_ne h]
      have h1 := hEf x
      rw [hup, hval] at h1
      have h2 := hcomp x
      show (if neg = true then !(E.wires (List.ofFn x)).getD E.output false
        else (E.wires (List.ofFn x)).getD E.output false) = _
      have h4 : (E.wires (List.ofFn x)).getD E.output false = circuitFun 10 E x := rfl
      rw [h4, h1]
      exact h2
