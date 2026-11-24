import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- With vertex 0 false, or with vertex 2 false, the function is the nine-edge function of the
-- other eight vertices, after renaming, and it needs 12 gates: small is the statement of the
-- checked L_meta_1664. fixZero: with vertex 0 false, wire 9 is true and wire 10 is one NOT gate;
-- every gate that reads wire 0 or wire 9 goes away. fixTwo is the same for vertex 2 and wire 10.
-- So three such gates among 13 leave at most 11. What remains is fewReaders: at most two gates
-- read wire 0 or wire 9, and at most two read wire 2 or wire 10.
theorem PEqualNP.Outside.R_meta_4665_613
    (small : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 5 && x 7)) 11)
    (fixZero : ∀ (C : Circuit), FanInTwo C →
      (∃ c : Bool, ∀ x : Fin 9 → Bool, x 0 = false →
        C.eval (List.ofFn x ++ [true, !x 2]) = c) ∨
      ∃ E : Circuit, FanInTwo E ∧ E.size + List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (i : ℕ) => i == 0 || i == 9)) C.gates ≤ C.size + 1 ∧
        ∀ x : Fin 9 → Bool, x 0 = false →
          E.eval (List.ofFn (fun j : Fin 8 => x (([1, 2, 3, 8, 6, 7, 4, 5] : List (Fin 9)).getD j.val 0))) = C.eval (List.ofFn x ++ [true, !x 2]))
    (fixTwo : ∀ (C : Circuit), FanInTwo C →
      (∃ c : Bool, ∀ x : Fin 9 → Bool, x 2 = false →
        C.eval (List.ofFn x ++ [!x 0, true]) = c) ∨
      ∃ E : Circuit, FanInTwo E ∧ E.size + List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (i : ℕ) => i == 2 || i == 10)) C.gates ≤ C.size + 1 ∧
        ∀ x : Fin 9 → Bool, x 2 = false →
          E.eval (List.ofFn (fun j : Fin 8 => x (([1, 0, 5, 8, 6, 4, 7, 3] : List (Fin 9)).getD j.val 0))) = C.eval (List.ofFn x ++ [!x 0, true]))
    (fewReaders : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (13 : ℕ) → (∀ x5 ∈ [(9 : ℕ), (10 : ℕ)], ∃ x7 ∈ x2.gates, x5 ∈ x7.inputs) → (∃ x6 ∈ x2.gates, x6.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ x7 ∈ x2.gates, x7.op = PEqualNP.CircuitLowerBounds.GateOp.not → x7.inputs.length ≤ (1 : ℕ) ∧ ∀ x10 ∈ x7.inputs, x10 ∉ [(0 : ℕ), (2 : ℕ), (9 : ℕ), (10 : ℕ)]) → (List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (i : ℕ) => i == 0 || i == 9)) x2.gates ≤ 2 ∧ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (i : ℕ) => i == 2 || i == 10)) x2.gates ≤ 2) → ∃ (x8 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ)), !x8 (2 : Fin (9 : ℕ))]) ≠ x1 x8) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (13 : ℕ) → (∀ x5 ∈ [(9 : ℕ), (10 : ℕ)], ∃ x7 ∈ x2.gates, x5 ∈ x7.inputs) → (∃ x6 ∈ x2.gates, x6.op = PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ x7 ∈ x2.gates, x7.op = PEqualNP.CircuitLowerBounds.GateOp.not → x7.inputs.length ≤ (1 : ℕ) ∧ ∀ x10 ∈ x7.inputs, x10 ∉ [(0 : ℕ), (2 : ℕ), (9 : ℕ), (10 : ℕ)]) → ∃ (x8 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ)), !x8 (2 : Fin (9 : ℕ))]) ≠ x1 x8 := by
  dsimp only
  intro C hfan hsize hread hnot hform
  by_contra hne
  have hall : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [!x 0, !x 2]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    by_contra hx
    exact hne ⟨x, hx⟩
  by_cases hr0 : List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (i : ℕ) => i == 0 || i == 9)) C.gates ≤ 2
  swap
  · have hC : ∀ x : Fin 9 → Bool, x 0 = false →
        C.eval (List.ofFn x ++ [true, !x 2]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      intro x hx
      have e : List.ofFn x ++ [!x 0, !x 2] = List.ofFn x ++ [true, !x 2] := by
        rw [hx]
        rfl
      rw [← e]
      exact hall x
    rcases fixZero C hfan with ⟨c, hc⟩ | ⟨E, hE, hEs, hEf⟩
    · have h0 : c = false := by
        rw [← hc (fun _ => false) rfl, hC (fun _ => false) rfl]
        rfl
      have h1 : c = true := by
        rw [← hc (fun i => decide (i ≠ 0)) rfl, hC (fun i => decide (i ≠ 0)) rfl]
        rfl
      exact absurd (h0.symm.trans h1) (by decide)
    · apply small
      refine ⟨E, hE, by omega, fun y => ?_⟩
      have hx : (fun i : Fin 9 => if i = 0 then false else y (([0, 0, 1, 2, 6, 7, 4, 5, 3] : List (Fin 8)).getD i.val 0)) 0 = false := rfl
      have hin : (fun j : Fin 8 => (fun i : Fin 9 => if i = 0 then false else y (([0, 0, 1, 2, 6, 7, 4, 5, 3] : List (Fin 8)).getD i.val 0)) (([1, 2, 3, 8, 6, 7, 4, 5] : List (Fin 9)).getD j.val 0)) = y := by
        funext j
        fin_cases j <;> rfl
      have h1 := hEf (fun i : Fin 9 => if i = 0 then false else y (([0, 0, 1, 2, 6, 7, 4, 5, 3] : List (Fin 8)).getD i.val 0)) hx
      rw [hin] at h1
      rw [h1, hC _ hx]
      have taut : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
          (false && b0 || b0 && b1 || b1 && b2 || b2 && b6 || b6 && false || false && b7 || b0 && b4 || b1 && b5 || b2 && b3 || b7 && b5 || b4 && b3 || b3 && b7)
          = ((b0 && b1) || (b1 && b2) || (b2 && b3) || (b3 && b4) || (b4 && b0) || (b1 && b5) || (b2 && b6) || (b3 && b7) || (b5 && b7)) := by decide
      exact taut (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
  by_cases hr2 : List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => (List.take (2 - (g.op.eval [Bool.false]).toNat) g.inputs).any (fun (i : ℕ) => i == 2 || i == 10)) C.gates ≤ 2
  swap
  · have hC : ∀ x : Fin 9 → Bool, x 2 = false →
        C.eval (List.ofFn x ++ [!x 0, true]) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      intro x hx
      have e : List.ofFn x ++ [!x 0, !x 2] = List.ofFn x ++ [!x 0, true] := by
        rw [hx]
        rfl
      rw [← e]
      exact hall x
    rcases fixTwo C hfan with ⟨c, hc⟩ | ⟨E, hE, hEs, hEf⟩
    · have h0 : c = false := by
        rw [← hc (fun _ => false) rfl, hC (fun _ => false) rfl]
        rfl
      have h1 : c = true := by
        rw [← hc (fun i => decide (i ≠ 2)) rfl, hC (fun i => decide (i ≠ 2)) rfl]
        rfl
      exact absurd (h0.symm.trans h1) (by decide)
    · apply small
      refine ⟨E, hE, by omega, fun y => ?_⟩
      have hx : (fun i : Fin 9 => if i = 2 then false else y (([1, 0, 0, 7, 5, 2, 4, 6, 3] : List (Fin 8)).getD i.val 0)) 2 = false := rfl
      have hin : (fun j : Fin 8 => (fun i : Fin 9 => if i = 2 then false else y (([1, 0, 0, 7, 5, 2, 4, 6, 3] : List (Fin 8)).getD i.val 0)) (([1, 0, 5, 8, 6, 4, 7, 3] : List (Fin 9)).getD j.val 0)) = y := by
        funext j
        fin_cases j <;> rfl
      have h1 := hEf (fun i : Fin 9 => if i = 2 then false else y (([1, 0, 0, 7, 5, 2, 4, 6, 3] : List (Fin 8)).getD i.val 0)) hx
      rw [hin] at h1
      rw [h1, hC _ hx]
      have taut : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
          (b1 && b0 || b0 && false || false && b7 || b7 && b5 || b5 && b1 || b1 && b2 || b0 && b4 || false && b6 || b7 && b3 || b2 && b6 || b4 && b3 || b3 && b2)
          = ((b0 && b1) || (b1 && b2) || (b2 && b3) || (b3 && b4) || (b4 && b0) || (b1 && b5) || (b2 && b6) || (b3 && b7) || (b5 && b7)) := by decide
      exact taut (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6) (y 7)
  exact hne (fewReaders C hfan hsize hread hnot hform ⟨hr0, hr2⟩)
