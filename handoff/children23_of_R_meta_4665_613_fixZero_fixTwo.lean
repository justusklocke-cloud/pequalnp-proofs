import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9994
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat : Type := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


theorem elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (elim n gs acc).2.length + gs.countP (fun g => decide (k ∈ g.inputs))
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, decide_true, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [hkg, decide_false, Bool.false_eq_true, ite_false]
      omega


theorem getD_ofFn' {α : Type} (m : ℕ) (f : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn f).getD j.val d = f j := by
  simp [List.getD_eq_getElem?_getD]

theorem normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> rfl

theorem normGate_inputs' (g : Gate) (h : Ok g) :
    (normGate g).inputs = g.inputs.take (2 - (g.op.eval [false]).toNat) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    have hl : inputs.length ≤ 2 := hlen
    simp [normGate, GateOp.eval, List.take_of_length_le hl]
  · have : op = GateOp.or := h
    subst this
    have hl : inputs.length ≤ 2 := hlen
    simp [normGate, GateOp.eval, List.take_of_length_le hl]
  · have : op = GateOp.not := h
    subst this
    simp [normGate, GateOp.eval]

theorem elim_countP (n : ℕ) (P : ℕ → Bool) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) →
    (∀ k, P k = true → k < acc.1.length ∧ ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (elim n gs acc).2.length + gs.countP (fun g => g.inputs.any P) ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hP
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by
        intro k hk
        obtain ⟨hlt, c, hc⟩ := hP k hk
        refine ⟨by simp [elimStep]; omega, c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : g.inputs.any P = true
    · obtain ⟨k, hkin, hPk⟩ := List.any_eq_true.1 hkg
      obtain ⟨_, c, hc⟩ := hP k hPk
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkin, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      have hd : g.inputs.any P = false := by simpa using hkg
      simp only [hd, Bool.false_eq_true, ite_false]
      omega


def st_fixZero : List Stat := [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 6, Sum.inr 7, Sum.inr 4, Sum.inr 5, Sum.inr 3, Sum.inl true, Sum.inr 8]

theorem fixZero (C : Circuit) (hf : FanInTwo C) :
    (∃ c : Bool, ∀ x : Fin 9 → Bool, x 0 = false → C.eval (List.ofFn x ++ [true, !x 2]) = c) ∨
    ∃ E : Circuit, FanInTwo E ∧ E.size + List.countP (fun (g : Gate) => (List.take (2 - (g.op.eval [false]).toNat) g.inputs).any
        (fun (i : ℕ) => i == 0 || i == 9)) C.gates ≤ C.size + 1 ∧
      ∀ x : Fin 9 → Bool, x 0 = false → E.eval (List.ofFn (fun j : Fin 8 => x (([1, 2, 3, 8, 6, 7, 4, 5] : List (Fin 9)).getD j.val 0))) = C.eval (List.ofFn x ++ [true, !x 2]) := by
  let G0 : Gate := ⟨GateOp.not, [1]⟩
  let acc0 : List Stat × List Gate := (st_fixZero, [G0])
  let gs := C.gates.map normGate
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g' (hf g' hg')
  have hlen := elim_countP 8 (fun i => i == 0 || i == 9) gs acc0 hnok (by
    intro k hk
    have hk' : k = 0 ∨ k = 9 := by simpa using hk
    rcases hk' with rfl | rfl
    · exact ⟨by simp [acc0, st_fixZero], _, rfl⟩
    · exact ⟨by simp [acc0, st_fixZero], _, rfl⟩)
  have hinv : ∀ x : Fin 9 → Bool, x 0 = false → Inv 8 (List.ofFn (fun j : Fin 8 => x (([1, 2, 3, 8, 6, 7, 4, 5] : List (Fin 9)).getD j.val 0))) (List.ofFn x ++ [true, !x 2]) acc0 := by
    intro x hx
    refine ⟨by simp [acc0, st_fixZero], ?_⟩
    intro i
    have hg0 : wiresFrom [G0] (List.ofFn (fun j : Fin 8 => x (([1, 2, 3, 8, 6, 7, 4, 5] : List (Fin 9)).getD j.val 0))) = (List.ofFn (fun j : Fin 8 => x (([1, 2, 3, 8, 6, 7, 4, 5] : List (Fin 9)).getD j.val 0))) ++ [!x 2] := by
      show _ ++ [GateOp.not.eval ([1].map fun i => _)] = _
      simp [GateOp.eval]
    show (st_fixZero.getD i (Sum.inl false)).Valid (8 + 1) ∧
      (st_fixZero.getD i (Sum.inl false)).val (wiresFrom [G0] _) = _
    rw [hg0]
    by_cases hi : i < 11
    · interval_cases i <;> simp [st_fixZero, Stat.Valid, Stat.val, hx]
    · have e1 : st_fixZero.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simp [st_fixZero]; omega)
      have e2 : (List.ofFn x ++ [true, !x 2]).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [e1, e2]; exact ⟨trivial, rfl⟩
  have hfin := fun x hx => inv_elim 8 _ (by simp) gs _ acc0
    (fun g hg => (hnok g hg).1) (hinv x hx)
  have hval : ∀ x : Fin 9 → Bool, x 0 = false →
      ((elim 8 gs acc0).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim 8 gs acc0).2 (List.ofFn (fun j : Fin 8 => x (([1, 2, 3, 8, 6, 7, 4, 5] : List (Fin 9)).getD j.val 0)))) = C.eval (List.ofFn x ++ [true, !x 2]) := by
    intro x hx
    rw [((hfin x hx).2 C.output).2, wiresFrom_norm]
    rfl
  have hok2 := elim_ok 8 gs acc0 (by
    intro g hg
    have : g = G0 := by simpa [acc0] using hg
    subst this
    exact ⟨Or.inr (Or.inr rfl), by simp [G0]⟩)
  have hcount : gs.countP (fun g => g.inputs.any (fun i => i == 0 || i == 9)) = List.countP (fun (g : Gate) => (List.take (2 - (g.op.eval [false]).toNat) g.inputs).any
        (fun (i : ℕ) => i == 0 || i == 9)) C.gates := by
    show (C.gates.map normGate).countP _ = _
    rw [List.countP_map]
    apply List.countP_congr
    intro g hg
    simp only [Function.comp, normGate_inputs' g (hf g hg)]
  have hsize : (elim 8 gs acc0).2.length + List.countP (fun (g : Gate) => (List.take (2 - (g.op.eval [false]).toNat) g.inputs).any
        (fun (i : ℕ) => i == 0 || i == 9)) C.gates ≤ C.size + 1 := by
    have e1 : gs.length = C.size := by simp [gs, Circuit.size]
    have e2 : acc0.2.length = 1 := rfl
    rw [← hcount]
    omega
  rcases hst : (elim 8 gs acc0).1.getD C.output (Sum.inl false) with c | j
  · left
    refine ⟨c, fun x hx => ?_⟩
    have h1 := hval x hx
    rw [hst] at h1
    exact h1.symm
  · right
    refine ⟨⟨(elim 8 gs acc0).2, j⟩, fun g hg => hok2 g hg, hsize, ?_⟩
    intro x hx
    have h1 := hval x hx
    rw [hst] at h1
    exact h1

def st_fixTwo : List Stat := [Sum.inr 1, Sum.inr 0, Sum.inl false, Sum.inr 7, Sum.inr 5, Sum.inr 2, Sum.inr 4, Sum.inr 6, Sum.inr 3, Sum.inr 8, Sum.inl true]

theorem fixTwo (C : Circuit) (hf : FanInTwo C) :
    (∃ c : Bool, ∀ x : Fin 9 → Bool, x 2 = false → C.eval (List.ofFn x ++ [!x 0, true]) = c) ∨
    ∃ E : Circuit, FanInTwo E ∧ E.size + List.countP (fun (g : Gate) => (List.take (2 - (g.op.eval [false]).toNat) g.inputs).any
        (fun (i : ℕ) => i == 2 || i == 10)) C.gates ≤ C.size + 1 ∧
      ∀ x : Fin 9 → Bool, x 2 = false → E.eval (List.ofFn (fun j : Fin 8 => x (([1, 0, 5, 8, 6, 4, 7, 3] : List (Fin 9)).getD j.val 0))) = C.eval (List.ofFn x ++ [!x 0, true]) := by
  let G0 : Gate := ⟨GateOp.not, [1]⟩
  let acc0 : List Stat × List Gate := (st_fixTwo, [G0])
  let gs := C.gates.map normGate
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g' (hf g' hg')
  have hlen := elim_countP 8 (fun i => i == 2 || i == 10) gs acc0 hnok (by
    intro k hk
    have hk' : k = 2 ∨ k = 10 := by simpa using hk
    rcases hk' with rfl | rfl
    · exact ⟨by simp [acc0, st_fixTwo], _, rfl⟩
    · exact ⟨by simp [acc0, st_fixTwo], _, rfl⟩)
  have hinv : ∀ x : Fin 9 → Bool, x 2 = false → Inv 8 (List.ofFn (fun j : Fin 8 => x (([1, 0, 5, 8, 6, 4, 7, 3] : List (Fin 9)).getD j.val 0))) (List.ofFn x ++ [!x 0, true]) acc0 := by
    intro x hx
    refine ⟨by simp [acc0, st_fixTwo], ?_⟩
    intro i
    have hg0 : wiresFrom [G0] (List.ofFn (fun j : Fin 8 => x (([1, 0, 5, 8, 6, 4, 7, 3] : List (Fin 9)).getD j.val 0))) = (List.ofFn (fun j : Fin 8 => x (([1, 0, 5, 8, 6, 4, 7, 3] : List (Fin 9)).getD j.val 0))) ++ [!x 0] := by
      show _ ++ [GateOp.not.eval ([1].map fun i => _)] = _
      simp [GateOp.eval]
    show (st_fixTwo.getD i (Sum.inl false)).Valid (8 + 1) ∧
      (st_fixTwo.getD i (Sum.inl false)).val (wiresFrom [G0] _) = _
    rw [hg0]
    by_cases hi : i < 11
    · interval_cases i <;> simp [st_fixTwo, Stat.Valid, Stat.val, hx]
    · have e1 : st_fixTwo.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simp [st_fixTwo]; omega)
      have e2 : (List.ofFn x ++ [!x 0, true]).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [e1, e2]; exact ⟨trivial, rfl⟩
  have hfin := fun x hx => inv_elim 8 _ (by simp) gs _ acc0
    (fun g hg => (hnok g hg).1) (hinv x hx)
  have hval : ∀ x : Fin 9 → Bool, x 2 = false →
      ((elim 8 gs acc0).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim 8 gs acc0).2 (List.ofFn (fun j : Fin 8 => x (([1, 0, 5, 8, 6, 4, 7, 3] : List (Fin 9)).getD j.val 0)))) = C.eval (List.ofFn x ++ [!x 0, true]) := by
    intro x hx
    rw [((hfin x hx).2 C.output).2, wiresFrom_norm]
    rfl
  have hok2 := elim_ok 8 gs acc0 (by
    intro g hg
    have : g = G0 := by simpa [acc0] using hg
    subst this
    exact ⟨Or.inr (Or.inr rfl), by simp [G0]⟩)
  have hcount : gs.countP (fun g => g.inputs.any (fun i => i == 2 || i == 10)) = List.countP (fun (g : Gate) => (List.take (2 - (g.op.eval [false]).toNat) g.inputs).any
        (fun (i : ℕ) => i == 2 || i == 10)) C.gates := by
    show (C.gates.map normGate).countP _ = _
    rw [List.countP_map]
    apply List.countP_congr
    intro g hg
    simp only [Function.comp, normGate_inputs' g (hf g hg)]
  have hsize : (elim 8 gs acc0).2.length + List.countP (fun (g : Gate) => (List.take (2 - (g.op.eval [false]).toNat) g.inputs).any
        (fun (i : ℕ) => i == 2 || i == 10)) C.gates ≤ C.size + 1 := by
    have e1 : gs.length = C.size := by simp [gs, Circuit.size]
    have e2 : acc0.2.length = 1 := rfl
    rw [← hcount]
    omega
  rcases hst : (elim 8 gs acc0).1.getD C.output (Sum.inl false) with c | j
  · left
    refine ⟨c, fun x hx => ?_⟩
    have h1 := hval x hx
    rw [hst] at h1
    exact h1.symm
  · right
    refine ⟨⟨(elim 8 gs acc0).2, j⟩, fun g hg => hok2 g hg, hsize, ?_⟩
    intro x hx
    have h1 := hval x hx
    rw [hst] at h1
    exact h1

end PEqualNP.Outside.L_meta_9994
