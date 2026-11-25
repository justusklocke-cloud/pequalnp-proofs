import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9996
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

theorem simplify_const (g : Gate) (hn : NOk g) (m : ℕ) (ins : List Stat)
    (hlen : ins.length = g.inputs.length) (hmem : Sum.inl false ∈ ins)
    (hop : (!g.op.eval [true, false]) = true) :
    ∃ c, (simplify g.op m ins).2 = Sum.inl c := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨⟨hops, hl⟩, hnot⟩ := hn
  have hl2 : ins.length ≤ 2 := by rw [hlen]; exact hl
  rcases hops with h | h | h
  · have : op = GateOp.and := h
    subst this
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp at hmem
    · cases a <;> simp_all [simplify, simpAnd]
    · cases a <;> cases b <;> simp_all [simplify, simpAnd]
    · simp at hl2
  · have : op = GateOp.or := h
    subst this
    simp [GateOp.eval] at hop
  · have : op = GateOp.not := h
    subst this
    have h1 : ins.length ≤ 1 := by rw [hlen]; exact hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hmem
    · cases a <;> simp_all [simplify, simpNot]
    · simp at h1

theorem elim_countDyn (n v : ℕ) (hv : v < n) (full : List Gate) :
    ∀ (gs pre : List Gate) (acc : List Stat × List Gate),
    full = pre ++ gs →
    (∀ g ∈ gs, NOk g) →
    acc.1.length = n + pre.length →
    acc.1.getD v (Sum.inl false) = Sum.inl false →
    (∀ k, (Nat.ble n k && (full[k - n]?).any
        (fun h => h.inputs.contains v && !h.op.eval [true, false])) = true →
      ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (elim n gs acc).2.length + gs.countP (fun g => g.inputs.any (fun k => k == v ||
        (Nat.ble n k && (full[k - n]?).any
          (fun h => h.inputs.contains v && !h.op.eval [true, false]))))
      ≤ acc.2.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro pre acc _ _ _ _ _; simp [elim]
  | cons g gs ih =>
    intro pre acc hfull hok hlen hv0 hW
    have hnok := hok g List.mem_cons_self
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hstep1 : (elimStep n acc g).1 = acc.1 ++ [(simplify g.op (n + acc.2.length) ins).2] := rfl
    have h1 := ih (pre ++ [g]) (elimStep n acc g) (by rw [hfull]; simp)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by rw [hstep1]; simp [hlen]; omega)
      (by rw [hstep1, getD_snoc_ne _ _ _ _ (by omega)]; exact hv0)
      (by
        intro k hk
        rw [hstep1]
        by_cases hkl : k = acc.1.length
        · subst hkl
          rw [getD_snoc_eq]
          have hk' := hk
          rw [Bool.and_eq_true] at hk'
          obtain ⟨_, hany⟩ := hk'
          have hidx : acc.1.length - n = pre.length := by omega
          have hg : full[acc.1.length - n]? = some g := by
            rw [hidx, hfull]
            simp
          rw [hg] at hany
          have hany' : (g.inputs.contains v && !g.op.eval [true, false]) = true := by
            simpa using hany
          rw [Bool.and_eq_true] at hany'
          obtain ⟨hc, hopb⟩ := hany'
          have hvin : v ∈ g.inputs := by simpa using hc
          exact simplify_const g hnok _ ins (by simp [hins])
            (List.mem_map.2 ⟨v, hvin, hv0⟩) hopb
        · rw [getD_snoc_ne _ _ _ _ hkl]
          exact hW k hk)
    rw [h3, List.length_cons, List.countP_cons]
    by_cases hkg : g.inputs.any (fun k => k == v ||
        (Nat.ble n k && (full[k - n]?).any
          (fun h => h.inputs.contains v && !h.op.eval [true, false]))) = true
    · obtain ⟨k, hkin, hPk⟩ := List.any_eq_true.1 hkg
      have hconst : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c := by
        rw [Bool.or_eq_true] at hPk
        rcases hPk with hkv | hkw
        · have : k = v := by simpa using hkv
          subst this
          exact ⟨false, hv0⟩
        · exact hW k hkw
      obtain ⟨c, hc⟩ := hconst
      have hnone : (simplify g.op (n + acc.2.length) ins).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa [hins] using hnok.1.2
        · intro h; simpa [hins] using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkin, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length) ins).1.toList).length = _
        rw [hnone]; simp
      simp only [hkg, ite_true]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length) ins).1.toList).length ≤ _
        have := toList_length_le (simplify g.op (n + acc.2.length) ins).1
        simp only [List.length_append]
        omega
      have hd : g.inputs.any (fun k => k == v ||
        (Nat.ble n k && (full[k - n]?).any
          (fun h => h.inputs.contains v && !h.op.eval [true, false]))) = false := by
        simpa using hkg
      simp only [hd, Bool.false_eq_true, ite_false]
      omega

theorem killTwo (n : ℕ) (C : Circuit) (v : Fin n) (hf : FanInTwo C) :
    (∀ x : Fin n → Bool, circuitFun n C (Function.update x v false) = true) ∨
    ∃ E : Circuit, FanInTwo E ∧
      E.size + List.countP (fun (g : Gate) => (List.take (2 - (g.op.eval [false]).toNat) g.inputs).any
        (fun (k : ℕ) => k == v.val || (Nat.ble n k && (C.gates[k - n]?).any (fun (h : Gate) =>
          (List.take (2 - (h.op.eval [false]).toNat) h.inputs).contains v.val &&
            !h.op.eval [true, false])))) C.gates ≤ C.size ∧
      ∀ x : Fin n → Bool, circuitFun n E x = circuitFun n C (Function.update x v false) := by
  let acc0 : List Stat × List Gate :=
    (List.ofFn (fun i : Fin n => if i = v then (Sum.inl false : Stat) else Sum.inr i.val), [])
  let gs := C.gates.map normGate
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g' (hf g' hg')
  have hv0 : acc0.1.getD v.val (Sum.inl false) = Sum.inl false := by
    show (List.ofFn _).getD v.val _ = _
    rw [getD_ofFn']; simp
  have hlen := elim_countDyn n v.val v.isLt gs gs [] acc0 rfl hnok (by simp [acc0]) hv0
    (by
      intro k hk
      rw [Bool.and_eq_true] at hk
      have hnk : n ≤ k := Nat.le_of_ble_eq_true hk.1
      exact ⟨false, List.getD_eq_default _ _ (by simp [acc0]; omega)⟩)
  have hinv : ∀ x : Fin n → Bool, Inv n (List.ofFn x)
      (List.ofFn (Function.update x v false)) acc0 := by
    intro x
    refine ⟨by simp [acc0], ?_⟩
    intro i
    by_cases hi : i < n
    · have e1 : acc0.1.getD i (Sum.inl false)
          = if (⟨i, hi⟩ : Fin n) = v then Sum.inl false else Sum.inr i :=
        getD_ofFn' n (fun i : Fin n => if i = v then (Sum.inl false : Stat)
          else Sum.inr i.val) (Sum.inl false) ⟨i, hi⟩
      have e2 : (List.ofFn (Function.update x v false)).getD i false
          = Function.update x v false ⟨i, hi⟩ := getD_ofFn' n _ _ ⟨i, hi⟩
      rw [e1, e2]
      by_cases hvv : (⟨i, hi⟩ : Fin n) = v
      · rw [if_pos hvv, hvv, Function.update_self]
        exact ⟨trivial, rfl⟩
      · rw [if_neg hvv, Function.update_of_ne hvv]
        refine ⟨?_, ?_⟩
        · show i < n + 0
          omega
        · show (wiresFrom [] (List.ofFn x)).getD i false = _
          exact getD_ofFn' n x false ⟨i, hi⟩
    · have e1 : acc0.1.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simp [acc0]; omega)
      have e2 : (List.ofFn (Function.update x v false)).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [e1, e2]; exact ⟨trivial, rfl⟩
  have hfin := fun x => inv_elim n (List.ofFn x) (by simp) gs _ acc0
    (fun g hg => (hnok g hg).1) (hinv x)
  have hval : ∀ x : Fin n → Bool, ((elim n gs acc0).1.getD C.output (Sum.inl false)).val
      (wiresFrom (elim n gs acc0).2 (List.ofFn x))
        = circuitFun n C (Function.update x v false) := by
    intro x
    rw [((hfin x).2 C.output).2, wiresFrom_norm]
    rfl
  have hok2 := elim_ok n gs acc0 (by simp [acc0])
  have hcount : gs.countP (fun g => g.inputs.any (fun k => k == v.val ||
        (Nat.ble n k && (gs[k - n]?).any
          (fun h => h.inputs.contains v.val && !h.op.eval [true, false]))))
      = List.countP (fun (g : Gate) => (List.take (2 - (g.op.eval [false]).toNat) g.inputs).any
        (fun (k : ℕ) => k == v.val || (Nat.ble n k && (C.gates[k - n]?).any (fun (h : Gate) =>
          (List.take (2 - (h.op.eval [false]).toNat) h.inputs).contains v.val &&
            !h.op.eval [true, false])))) C.gates := by
    show (C.gates.map normGate).countP _ = _
    rw [List.countP_map]
    apply List.countP_congr
    intro g hg
    simp only [Function.comp, normGate_inputs' g (hf g hg)]
    have inner : ∀ k : ℕ, (gs[k - n]?).any
          (fun h => h.inputs.contains v.val && !h.op.eval [true, false])
        = (C.gates[k - n]?).any (fun (h : Gate) =>
          (List.take (2 - (h.op.eval [false]).toNat) h.inputs).contains v.val &&
            !h.op.eval [true, false]) := by
      intro k
      show ((C.gates.map normGate)[k - n]?).any _ = _
      rw [List.getElem?_map]
      rcases hget : C.gates[k - n]? with _ | h
      · rfl
      · have hmem : h ∈ C.gates := List.mem_of_getElem? hget
        simp only [Option.map_some, Option.any_some, normGate_inputs' h (hf h hmem), normGate_op]
    simp only [inner]
  have hsize : (elim n gs acc0).2.length
      + List.countP (fun (g : Gate) => (List.take (2 - (g.op.eval [false]).toNat) g.inputs).any
        (fun (k : ℕ) => k == v.val || (Nat.ble n k && (C.gates[k - n]?).any (fun (h : Gate) =>
          (List.take (2 - (h.op.eval [false]).toNat) h.inputs).contains v.val &&
            !h.op.eval [true, false])))) C.gates ≤ C.size := by
    have e1 : gs.length = C.size := by simp [gs, Circuit.size]
    have e2 : acc0.2.length = 0 := rfl
    rw [← hcount]
    omega
  rcases hst : (elim n gs acc0).1.getD C.output (Sum.inl false) with c | j
  · cases c with
    | true =>
      left
      intro x
      have h1 := hval x
      rw [hst] at h1
      exact h1.symm
    | false =>
      right
      refine ⟨⟨[], n⟩, by intro g hg; simp at hg, ?_, ?_⟩
      · have hle := List.countP_le_length (p := fun (g : Gate) => (List.take (2 - (g.op.eval [false]).toNat) g.inputs).any
          (fun (k : ℕ) => k == v.val || (Nat.ble n k && (C.gates[k - n]?).any (fun (h : Gate) =>
            (List.take (2 - (h.op.eval [false]).toNat) h.inputs).contains v.val &&
              !h.op.eval [true, false])))) (l := C.gates)
        show 0 + _ ≤ C.gates.length
        omega
      · intro x
        have h1 := hval x
        rw [hst] at h1
        rw [← h1]
        show ((List.ofFn x).getD n false) = false
        exact List.getD_eq_default _ _ (by simp)
  · right
    refine ⟨⟨(elim n gs acc0).2, j⟩, fun g hg => hok2 g hg, hsize, ?_⟩
    intro x
    have h1 := hval x
    rw [hst] at h1
    exact h1

end PEqualNP.Outside.L_meta_9996
