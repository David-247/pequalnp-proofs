import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5488

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 2) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma run_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    run gs w = run (gs.drop j) (run (gs.take j) w) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l w) (List.take_append_drop j gs).symm

def val (C : Circuit) (x : Fin 6 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma val_input (C : Circuit) (x : Fin 6 → Bool) (i : Fin 6) :
    val C x i = x i := by
  change (run C.gates (List.ofFn x)).getD i false = x i
  have hi : (i : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]

lemma val_ge (C : Circuit) (x : Fin 6 → Bool) (w : ℕ) (hw : 6 + C.size ≤ w) :
    val C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma val_gate (C : Circuit) (x : Fin 6 → Bool) (w : ℕ) (h6 : 6 ≤ w) (hw : w < 6 + C.size) :
    let g := C.gates[w - 6]'(by unfold Circuit.size at hw; omega)
    val C x w = g.op.eval (g.inputs.map fun r => if r < w then val C x r else false) := by
  let j := w - 6
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then val C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then val C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

def effIn (C : Circuit) (w : ℕ) : Finset ℕ :=
  if h : 6 ≤ w ∧ w - 6 < C.gates.length then
    let g := C.gates[w - 6]'h.2
    match g.op with
    | GateOp.not =>
      match g.inputs with
      | i :: _ => if i < w then {i} else ∅
      | [] => ∅
    | _ => (g.inputs.filter (· < w)).toFinset
  else ∅

lemma effIn_lt (C : Circuit) (w r : ℕ) (hr : r ∈ effIn C w) : r < w := by
  unfold effIn at hr
  split_ifs at hr with h
  · dsimp only at hr
    cases hop : (C.gates[w - 6]'h.2).op <;> simp only [hop] at hr
    · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hr
      exact hr.2
    · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hr
      exact hr.2
    · cases hin : (C.gates[w - 6]'h.2).inputs with
      | nil => simp [hin] at hr
      | cons i tl =>
        simp only [hin] at hr
        split_ifs at hr with hi
        · simp only [Finset.mem_singleton] at hr
          omega
        · simp at hr
    · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hr
      exact hr.2
    · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hr
      exact hr.2
  · simp at hr

lemma effIn_ge_six (C : Circuit) (w r : ℕ) (hr : r ∈ effIn C w) :
    6 ≤ w ∧ w < 6 + C.size := by
  unfold effIn at hr
  split_ifs at hr with h
  · unfold Circuit.size; omega
  · simp at hr

lemma effIn_card_le_two (C : Circuit) (hC : FanInTwo C) (w : ℕ) :
    (effIn C w).card ≤ 2 := by
  unfold effIn
  split_ifs with h
  · dsimp only
    have hg := hC (C.gates[w - 6]'h.2) (List.getElem_mem h.2)
    have hlen : (C.gates[w - 6]'h.2).inputs.length ≤ 2 := hg.2
    cases hop : (C.gates[w - 6]'h.2).op
    · calc ((C.gates[w - 6]'h.2).inputs.filter (· < w)).toFinset.card
          ≤ ((C.gates[w - 6]'h.2).inputs.filter (· < w)).length := List.toFinset_card_le _
        _ ≤ (C.gates[w - 6]'h.2).inputs.length := List.length_filter_le _ _
        _ ≤ 2 := hlen
    · calc ((C.gates[w - 6]'h.2).inputs.filter (· < w)).toFinset.card
          ≤ ((C.gates[w - 6]'h.2).inputs.filter (· < w)).length := List.toFinset_card_le _
        _ ≤ (C.gates[w - 6]'h.2).inputs.length := List.length_filter_le _ _
        _ ≤ 2 := hlen
    · cases hin : (C.gates[w - 6]'h.2).inputs with
      | nil => simp
      | cons i tl =>
        dsimp only
        split_ifs <;> simp
    · calc ((C.gates[w - 6]'h.2).inputs.filter (· < w)).toFinset.card
          ≤ ((C.gates[w - 6]'h.2).inputs.filter (· < w)).length := List.toFinset_card_le _
        _ ≤ (C.gates[w - 6]'h.2).inputs.length := List.length_filter_le _ _
        _ ≤ 2 := hlen
    · calc ((C.gates[w - 6]'h.2).inputs.filter (· < w)).toFinset.card
          ≤ ((C.gates[w - 6]'h.2).inputs.filter (· < w)).length := List.toFinset_card_le _
        _ ≤ (C.gates[w - 6]'h.2).inputs.length := List.length_filter_le _ _
        _ ≤ 2 := hlen
  · simp

lemma val_congr_effIn (C : Circuit) (x y : Fin 6 → Bool) (w : ℕ)
    (h6 : 6 ≤ w) (hw : w < 6 + C.size)
    (heq : ∀ r ∈ effIn C w, val C x r = val C y r) :
    val C x w = val C y w := by
  have hx := val_gate C x w h6 hw
  have hy := val_gate C y w h6 hw
  rw [hx, hy]
  have hcond : 6 ≤ w ∧ w - 6 < C.gates.length := ⟨h6, by unfold Circuit.size at hw; omega⟩
  cases hop : (C.gates[w - 6]'hcond.2).op
  · congr 1
    apply List.map_congr_left
    intro r hr
    by_cases hlt : r < w
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      apply heq
      unfold effIn
      rw [dite_eq_left hcond]
      simp [hop, hr, hlt]
    · rw [ite_eq_right hlt, ite_eq_right hlt]
  · congr 1
    apply List.map_congr_left
    intro r hr
    by_cases hlt : r < w
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      apply heq
      unfold effIn
      rw [dite_eq_left hcond]
      simp [hop, hr, hlt]
    · rw [ite_eq_right hlt, ite_eq_right hlt]
  · cases hin : (C.gates[w - 6]'hcond.2).inputs with
    | nil => simp [GateOp.eval]
    | cons i tl =>
      simp only [List.map_cons, GateOp.eval, List.headD_cons]
      by_cases hi : i < w
      · rw [ite_eq_left hi, ite_eq_left hi]
        congr 1
        apply heq
        unfold effIn
        rw [dite_eq_left hcond]
        simp [hop, hin, hi]
      · rw [ite_eq_right hi, ite_eq_right hi]
  · congr 1
    apply List.map_congr_left
    intro r hr
    by_cases hlt : r < w
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      apply heq
      unfold effIn
      rw [dite_eq_left hcond]
      simp [hop, hr, hlt]
    · rw [ite_eq_right hlt, ite_eq_right hlt]
  · congr 1
    apply List.map_congr_left
    intro r hr
    by_cases hlt : r < w
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      apply heq
      unfold effIn
      rw [dite_eq_left hcond]
      simp [hop, hr, hlt]
    · rw [ite_eq_right hlt, ite_eq_right hlt]

lemma effIn_card_two (C : Circuit) (hC : FanInTwo C) (w : ℕ)
    (hcard : (effIn C w).card = 2) :
    ∃ a b : ℕ, a ≠ b ∧ a < w ∧ b < w ∧ effIn C w = {a, b} ∧
      ((∀ x, val C x w = (val C x a && val C x b)) ∨
       (∀ x, val C x w = (val C x a || val C x b))) := by
  have hcond : 6 ≤ w ∧ w - 6 < C.gates.length := by
    by_contra h
    unfold effIn at hcard
    rw [dite_eq_right h] at hcard
    simp at hcard
  have hw : w < 6 + C.size := by unfold Circuit.size; omega
  have hg := hC (C.gates[w - 6]'hcond.2) (List.getElem_mem hcond.2)
  have hlen : (C.gates[w - 6]'hcond.2).inputs.length ≤ 2 := hg.2
  have hop_mem := hg.1
  rcases hop_mem with hop | hop | hop
  · have heff : effIn C w = ((C.gates[w - 6]'hcond.2).inputs.filter (· < w)).toFinset := by
      unfold effIn; rw [dite_eq_left hcond]; simp [hop]
    cases hin : (C.gates[w - 6]'hcond.2).inputs with
    | nil => simp [heff, hin] at hcard
    | cons a tl =>
      cases tl with
      | nil =>
        by_cases ha : a < w <;> simp [heff, hin, ha] at hcard
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          by_cases ha : a < w
          · by_cases hb : b < w
            · have heff2 : effIn C w = {a, b} := by
                rw [heff, hin]
                ext u
                simp [ha, hb]
              have hab : a ≠ b := by
                intro heq
                subst heq
                rw [heff2] at hcard
                simp at hcard
              refine ⟨a, b, hab, ha, hb, heff2, Or.inl ?_⟩
              intro x
              have hv := val_gate C x w hcond.1 hw
              rw [hv]
              simp [hop, hin, ha, hb, GateOp.eval]
            · simp [heff, hin, ha, hb] at hcard
          · by_cases hb : b < w <;> simp [heff, hin, ha, hb] at hcard
        | cons c tl3 =>
          rw [hin] at hlen; simp at hlen
  · have heff : effIn C w = ((C.gates[w - 6]'hcond.2).inputs.filter (· < w)).toFinset := by
      unfold effIn; rw [dite_eq_left hcond]; simp [hop]
    cases hin : (C.gates[w - 6]'hcond.2).inputs with
    | nil => simp [heff, hin] at hcard
    | cons a tl =>
      cases tl with
      | nil =>
        by_cases ha : a < w <;> simp [heff, hin, ha] at hcard
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          by_cases ha : a < w
          · by_cases hb : b < w
            · have heff2 : effIn C w = {a, b} := by
                rw [heff, hin]
                ext u
                simp [ha, hb]
              have hab : a ≠ b := by
                intro heq
                subst heq
                rw [heff2] at hcard
                simp at hcard
              refine ⟨a, b, hab, ha, hb, heff2, Or.inr ?_⟩
              intro x
              have hv := val_gate C x w hcond.1 hw
              rw [hv]
              simp [hop, hin, ha, hb, GateOp.eval]
            · simp [heff, hin, ha, hb] at hcard
          · by_cases hb : b < w <;> simp [heff, hin, ha, hb] at hcard
        | cons c tl3 =>
          rw [hin] at hlen; simp at hlen
  · have hop' : (C.gates[w - 6]'hcond.2).op = GateOp.not := hop
    unfold effIn at hcard
    rw [dite_eq_left hcond] at hcard
    simp only [hop'] at hcard
    cases hin : (C.gates[w - 6]'hcond.2).inputs with
    | nil => simp [hin] at hcard
    | cons i tl =>
      simp only [hin] at hcard
      split_ifs at hcard <;> simp at hcard

def supp (C : Circuit) (w : ℕ) : Finset ℕ :=
  insert w ((effIn C w).attach.biUnion fun r => supp C r.1)
termination_by w
decreasing_by exact effIn_lt C w r.1 r.2

lemma supp_eq (C : Circuit) (w : ℕ) :
    supp C w = insert w ((effIn C w).biUnion (supp C)) := by
  rw [supp]
  ext u
  simp

lemma mem_supp_self (C : Circuit) (w : ℕ) : w ∈ supp C w := by
  rw [supp_eq]
  exact Finset.mem_insert_self _ _

lemma supp_mono (C : Circuit) (w r : ℕ) (hr : r ∈ effIn C w) :
    supp C r ⊆ supp C w := by
  intro u hu
  rw [supp_eq]
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨r, hr, hu⟩)

lemma supp_le (C : Circuit) (w : ℕ) : ∀ u ∈ supp C w, u ≤ w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro u hu
    rw [supp_eq, Finset.mem_insert, Finset.mem_biUnion] at hu
    rcases hu with rfl | ⟨r, hr, hur⟩
    · exact le_rfl
    · have hlt := effIn_lt C w r hr
      exact (ih r hlt u hur).trans hlt.le

lemma supp_trans (C : Circuit) (w : ℕ) : ∀ u ∈ supp C w, supp C u ⊆ supp C w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro u hu
    rw [supp_eq, Finset.mem_insert, Finset.mem_biUnion] at hu
    rcases hu with rfl | ⟨r, hr, hur⟩
    · exact Finset.Subset.refl _
    · have hlt := effIn_lt C w r hr
      exact (ih r hlt u hur).trans (supp_mono C w r hr)

lemma supp_cover (C : Circuit) (w : ℕ) :
    ∀ u ∈ supp C w, u ≠ w → ∃ g ∈ supp C w, u ∈ effIn C g := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro u hu hne
    rw [supp_eq, Finset.mem_insert, Finset.mem_biUnion] at hu
    rcases hu with rfl | ⟨r, hr, hur⟩
    · exact absurd rfl hne
    · by_cases hur_eq : u = r
      · subst hur_eq
        exact ⟨w, mem_supp_self C w, hr⟩
      · have hlt := effIn_lt C w r hr
        obtain ⟨g, hg, hug⟩ := ih r hlt u hur hur_eq
        exact ⟨g, supp_mono C w r hr hg, hug⟩

lemma val_congr_supp (C : Circuit) (x y : Fin 6 → Bool) (w : ℕ)
    (heq : ∀ i : Fin 6, (i : ℕ) ∈ supp C w → x i = y i) :
    val C x w = val C y w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hlt6 : w < 6
    · have hself : w ∈ supp C w := mem_supp_self C w
      have hxy := heq ⟨w, hlt6⟩ hself
      have hx := val_input C x ⟨w, hlt6⟩
      have hy := val_input C y ⟨w, hlt6⟩
      exact hx.trans (hxy.trans hy.symm)
    · by_cases hw : w < 6 + C.size
      · apply val_congr_effIn C x y w (by omega) hw
        intro r hr
        exact ih r (effIn_lt C w r hr) (fun i hi => heq i (supp_mono C w r hr hi))
      · rw [val_ge C x w (by omega), val_ge C y w (by omega)]

lemma card_biUnion_eq_sum_disj (G : Finset ℕ) (f : ℕ → Finset ℕ)
    (heq : (G.biUnion f).card = G.sum (fun g => (f g).card)) :
    ∀ g₁ ∈ G, ∀ g₂ ∈ G, ∀ u, u ∈ f g₁ → u ∈ f g₂ → g₁ = g₂ := by
  intro g₁ hg₁ g₂ hg₂ u hu₁ hu₂
  by_contra hne
  let G' := G.erase g₁
  have hg₁_not : g₁ ∉ G' := Finset.notMem_erase g₁ G
  have hg₂' : g₂ ∈ G' := Finset.mem_erase.mpr ⟨Ne.symm hne, hg₂⟩
  have hG : insert g₁ G' = G := Finset.insert_erase hg₁
  have hbi : G.biUnion f = f g₁ ∪ G'.biUnion f := by
    rw [← hG, Finset.biUnion_insert]
  have hsum : G.sum (fun g => (f g).card) = (f g₁).card + G'.sum (fun g => (f g).card) := by
    rw [← hG, Finset.sum_insert hg₁_not]
  have hinter : u ∈ f g₁ ∩ G'.biUnion f :=
    Finset.mem_inter.mpr ⟨hu₁, Finset.mem_biUnion.mpr ⟨g₂, hg₂', hu₂⟩⟩
  have hpos : 1 ≤ (f g₁ ∩ G'.biUnion f).card := Finset.card_pos.mpr ⟨u, hinter⟩
  have hle : (G'.biUnion f).card ≤ G'.sum (fun g => (f g).card) := Finset.card_biUnion_le
  have hunion := Finset.card_union_add_card_inter (f g₁) (G'.biUnion f)
  rw [← hbi] at hunion
  omega

def e0 : Fin 6 → Bool := fun _ => false
def e1 (u : Fin 6) : Fin 6 → Bool := fun i => decide (i = u)
def e2 (u v : Fin 6) : Fin 6 → Bool := fun i => decide (i = u ∨ i = v)

lemma essential (i : Fin 6) :
    ∃ x y : Fin 6 → Bool, (∀ j : Fin 6, j ≠ i → x j = y j) ∧ target x ≠ target y := by
  fin_cases i
  · exact ⟨e1 2, e2 0 2, by decide, by decide⟩
  · exact ⟨e1 4, e2 1 4, by decide, by decide⟩
  · exact ⟨e1 0, e2 0 2, by decide, by decide⟩
  · exact ⟨e1 2, e2 2 3, by decide, by decide⟩
  · exact ⟨e1 0, e2 0 4, by decide, by decide⟩
  · exact ⟨e1 0, e2 0 5, by decide, by decide⟩

lemma val_mono_on (C : Circuit) (hC : FanInTwo C) (W : Finset ℕ)
    (hclosed : ∀ w ∈ W, ∀ r ∈ effIn C w, r ∈ W)
    (hcard : ∀ w ∈ W, 6 ≤ w → (effIn C w).card = 2)
    (x y : Fin 6 → Bool) (hxy : ∀ i : Fin 6, x i = true → y i = true) :
    ∀ w ∈ W, val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases h6 : w < 6
    · have h1 := val_input C x ⟨w, h6⟩
      have h2 := val_input C y ⟨w, h6⟩
      rw [h1] at hx
      rw [h2]
      exact hxy ⟨w, h6⟩ hx
    · obtain ⟨a, b, _, ha, hb, heff, hgate⟩ := effIn_card_two C hC w (hcard w hw (by omega))
      have haW : a ∈ W := hclosed w hw a (by rw [heff]; simp)
      have hbW : b ∈ W := hclosed w hw b (by rw [heff]; simp)
      rcases hgate with hand | hor
      · rw [hand] at hx ⊢
        simp only [Bool.and_eq_true] at hx ⊢
        exact ⟨ih a ha haW hx.1, ih b hb hbW hx.2⟩
      · rw [hor] at hx ⊢
        simp only [Bool.or_eq_true] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (ih a ha haW hx)
        · exact Or.inr (ih b hb hbW hx)

lemma supp_has_input (C : Circuit) (W : Finset ℕ)
    (hcard : ∀ w ∈ W, 6 ≤ w → (effIn C w).card = 2)
    (a : ℕ) (haW : supp C a ⊆ W) :
    ∃ i : Fin 6, (i : ℕ) ∈ supp C a := by
  have hne : (supp C a).Nonempty := ⟨a, mem_supp_self C a⟩
  let u := (supp C a).min' hne
  have hu : u ∈ supp C a := Finset.min'_mem (supp C a) hne
  by_cases h6 : u < 6
  · exact ⟨⟨u, h6⟩, hu⟩
  · have hcu : (effIn C u).card = 2 := hcard u (haW hu) (by omega)
    have hne_eff : (effIn C u).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨r, hr⟩ := hne_eff
    have hr_in : r ∈ supp C a := supp_trans C a u hu (supp_mono C u r hr (mem_supp_self C r))
    have hle : u ≤ r := Finset.min'_le (supp C a) r hr_in
    have hlt : r < u := effIn_lt C u r hr
    omega

lemma lower_bound (t : ℕ) (h : HasCircuitSize 6 target t) : 6 ≤ t := by
  by_contra ht
  have ht5 : t ≤ 5 := by omega
  obtain ⟨C, hC, hsize, heval⟩ := h
  have hC5 : C.size ≤ 5 := le_trans hsize ht5
  have hval_out : ∀ x : Fin 6 → Bool, val C x C.output = target x := heval
  have hout_lt : C.output < 6 + C.size := by
    by_contra hge
    have h1 := hval_out (e2 0 2)
    have h2 := val_ge C (e2 0 2) C.output (by omega)
    rw [h2] at h1
    have h3 : target (e2 0 2) = true := by decide
    rw [h3] at h1
    cases h1
  let W := supp C C.output
  let I := W.filter (· < 6)
  let G := W.filter (6 ≤ ·)
  have hI_mem : ∀ i : Fin 6, (i : ℕ) ∈ W := by
    intro i
    by_contra hni
    obtain ⟨x, y, hxy, hne⟩ := essential i
    have hagree : ∀ j : Fin 6, (j : ℕ) ∈ W → x j = y j := by
      intro j hj
      by_cases hji : j = i
      · subst hji; exact absurd hj hni
      · exact hxy j hji
    have hveq := val_congr_supp C x y C.output hagree
    rw [hval_out x, hval_out y] at hveq
    exact hne hveq
  have hI_eq : I = Finset.range 6 := by
    ext u
    simp only [I, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨hI_mem ⟨u, h⟩, h⟩
  have hI_card : I.card = 6 := by rw [hI_eq]; simp
  have hout_ge : 6 ≤ C.output := by
    by_contra hlt6
    have hW1 : W = {C.output} := by
      unfold W
      rw [supp_eq]
      have hemp : effIn C C.output = ∅ := by
        unfold effIn
        rw [dite_eq_right (by omega)]
      simp [hemp]
    have hI_le : I.card ≤ 1 := by
      calc I.card ≤ W.card := Finset.card_filter_le _ _
        _ = 1 := by rw [hW1]; simp
    omega
  have hout_G : C.output ∈ G := Finset.mem_filter.mpr ⟨mem_supp_self C C.output, hout_ge⟩
  have hG_sub : G ⊆ Finset.Ico 6 (6 + C.size) := by
    intro g hg
    rw [Finset.mem_filter] at hg
    rw [Finset.mem_Ico]
    have hle := supp_le C C.output g hg.1
    omega
  have hG_card_le : G.card ≤ 5 := by
    have h1 := Finset.card_le_card hG_sub
    rw [Nat.card_Ico] at h1
    omega
  have hW_card : W.card = I.card + G.card := by
    have hun : I ∪ G = W := by
      ext u
      simp only [I, G, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases h6 : u < 6
        · exact Or.inl ⟨h, h6⟩
        · exact Or.inr ⟨h, by omega⟩
    have hdis : Disjoint I G := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      simp only [I, G, Finset.mem_filter] at hu1 hu2
      omega
    rw [← hun, Finset.card_union_of_disjoint hdis]
  have herase_card : (W.erase C.output).card = G.card + 5 := by
    rw [Finset.card_erase_of_mem (mem_supp_self C C.output), hW_card, hI_card]
    omega
  have hcover : W.erase C.output ⊆ G.biUnion (effIn C) := by
    intro u hu
    rw [Finset.mem_erase] at hu
    obtain ⟨g, hg, hug⟩ := supp_cover C C.output u hu.2 hu.1
    have hg6 := (effIn_ge_six C g u hug).1
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr ⟨hg, hg6⟩, hug⟩
  have hchain1 : G.card + 5 ≤ (G.biUnion (effIn C)).card := by
    rw [← herase_card]
    exact Finset.card_le_card hcover
  have hchain2 : (G.biUnion (effIn C)).card ≤ G.sum (fun g => (effIn C g).card) :=
    Finset.card_biUnion_le
  have hchain3 : G.sum (fun g => (effIn C g).card) ≤ G.sum (fun _ => 2) :=
    Finset.sum_le_sum (fun g _ => effIn_card_le_two C hC g)
  have hsum2 : G.sum (fun _ => 2) = 2 * G.card := by
    rw [Finset.sum_const, smul_eq_mul]; omega
  have hbi_eq : (G.biUnion (effIn C)).card = G.sum (fun g => (effIn C g).card) := by omega
  have hsum_eq : G.sum (fun g => (effIn C g).card) = G.sum (fun _ => 2) := by omega
  have hdisj := card_biUnion_eq_sum_disj G (effIn C) hbi_eq
  have hall_two : ∀ g ∈ G, (effIn C g).card = 2 := by
    intro g hg
    by_contra hne
    have hlt : (effIn C g).card < 2 := by
      have hle := effIn_card_le_two C hC g
      omega
    have hstrict : G.sum (fun g => (effIn C g).card) < G.sum (fun _ => 2) :=
      Finset.sum_lt_sum (fun x _ => effIn_card_le_two C hC x) ⟨g, hg, hlt⟩
    omega
  obtain ⟨a, b, hab, ha_lt, hb_lt, heff_out, hgate_out⟩ :=
    effIn_card_two C hC C.output (hall_two C.output hout_G)
  have ha_eff : a ∈ effIn C C.output := by rw [heff_out]; simp
  have hb_eff : b ∈ effIn C C.output := by rw [heff_out]; simp
  have ha_sub : supp C a ⊆ W := supp_mono C C.output a ha_eff
  have hb_sub : supp C b ⊆ W := supp_mono C C.output b hb_eff
  have hsupp_disj : Disjoint (supp C a) (supp C b) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    by_contra hne
    have hnonempty : (supp C a ∩ supp C b).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    let m := (supp C a ∩ supp C b).max' hnonempty
    have hm : m ∈ supp C a ∩ supp C b := Finset.max'_mem _ hnonempty
    rw [Finset.mem_inter] at hm
    by_cases hma : m = a
    · have hmb : m ≠ b := by omega
      obtain ⟨g, hg, hmg⟩ := supp_cover C b m hm.2 hmb
      have hgG : g ∈ G := Finset.mem_filter.mpr ⟨hb_sub hg, (effIn_ge_six C g m hmg).1⟩
      have hgeq : g = C.output := hdisj g hgG C.output hout_G m hmg (by rw [hma]; exact ha_eff)
      have hgle : g ≤ b := supp_le C b g hg
      omega
    · by_cases hmb : m = b
      · obtain ⟨g, hg, hmg⟩ := supp_cover C a m hm.1 hma
        have hgG : g ∈ G := Finset.mem_filter.mpr ⟨ha_sub hg, (effIn_ge_six C g m hmg).1⟩
        have hgeq : g = C.output := hdisj g hgG C.output hout_G m hmg (by rw [hmb]; exact hb_eff)
        have hgle : g ≤ a := supp_le C a g hg
        omega
      · obtain ⟨g₁, hg₁, hmg₁⟩ := supp_cover C a m hm.1 hma
        obtain ⟨g₂, hg₂, hmg₂⟩ := supp_cover C b m hm.2 hmb
        have hg₁G : g₁ ∈ G := Finset.mem_filter.mpr ⟨ha_sub hg₁, (effIn_ge_six C g₁ m hmg₁).1⟩
        have hg₂G : g₂ ∈ G := Finset.mem_filter.mpr ⟨hb_sub hg₂, (effIn_ge_six C g₂ m hmg₂).1⟩
        have hgeq : g₁ = g₂ := hdisj g₁ hg₁G g₂ hg₂G m hmg₁ hmg₂
        have hg₁_inter : g₁ ∈ supp C a ∩ supp C b := Finset.mem_inter.mpr ⟨hg₁, hgeq ▸ hg₂⟩
        have hle : g₁ ≤ m := Finset.le_max' _ g₁ hg₁_inter
        have hlt : m < g₁ := effIn_lt C g₁ m hmg₁
        omega
  let U : Finset (Fin 6) := Finset.univ.filter (fun i => (i : ℕ) ∈ supp C a)
  let V : Finset (Fin 6) := Finset.univ.filter (fun i => (i : ℕ) ∈ supp C b)
  have hUV_disj : ∀ i : Fin 6, ¬ (i ∈ U ∧ i ∈ V) := by
    intro i ⟨hiU, hiV⟩
    simp only [U, V, Finset.mem_filter, Finset.mem_univ, true_and] at hiU hiV
    exact Finset.disjoint_left.mp hsupp_disj hiU hiV
  have hUV_cover : ∀ i : Fin 6, i ∈ U ∨ i ∈ V := by
    intro i
    have hiW : (i : ℕ) ∈ W := hI_mem i
    unfold W at hiW
    rw [supp_eq, Finset.mem_insert, Finset.mem_biUnion] at hiW
    rcases hiW with heq | ⟨r, hr, hir⟩
    · omega
    · rw [heff_out, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hir⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hir⟩)
  have hW_card2 : ∀ w ∈ W, 6 ≤ w → (effIn C w).card = 2 := by
    intro w hw h6
    exact hall_two w (Finset.mem_filter.mpr ⟨hw, h6⟩)
  have hU_ne : U.Nonempty := by
    obtain ⟨i, hi⟩ := supp_has_input C W hW_card2 a ha_sub
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hV_ne : V.Nonempty := by
    obtain ⟨i, hi⟩ := supp_has_input C W hW_card2 b hb_sub
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let A : (Fin 6 → Bool) → Bool := fun x => val C x a
  let B : (Fin 6 → Bool) → Bool := fun x => val C x b
  have hA_congr : ∀ x y, (∀ i ∈ U, x i = y i) → A x = A y := by
    intro x y hxy
    exact val_congr_supp C x y a (fun i hi => hxy i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩))
  have hB_congr : ∀ x y, (∀ i ∈ V, x i = y i) → B x = B y := by
    intro x y hxy
    exact val_congr_supp C x y b (fun i hi => hxy i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩))
  have hW_closed : ∀ w ∈ W, ∀ r ∈ effIn C w, r ∈ W := by
    intro w hw r hr
    exact supp_trans C C.output w hw (supp_mono C w r hr (mem_supp_self C r))
  have hA_mono : ∀ x y, (∀ i : Fin 6, x i = true → y i = true) → A x = true → A y = true :=
    fun x y hxy => val_mono_on C hC W hW_closed hW_card2 x y hxy a (ha_sub (mem_supp_self C a))
  have hB_mono : ∀ x y, (∀ i : Fin 6, x i = true → y i = true) → B x = true → B y = true :=
    fun x y hxy => val_mono_on C hC W hW_closed hW_card2 x y hxy b (hb_sub (mem_supp_self C b))
  rcases hgate_out with hand | hor
  · have hf_and : ∀ x, target x = (A x && B x) := by
      intro x; rw [← hval_out x]; exact hand x
    have hA0 : A e0 = false := by
      cases hAe0 : A e0
      · rfl
      · have hAtrue : ∀ x, A x = true := fun x => hA_mono e0 x (fun _ h => by simp [e0] at h) hAe0
        obtain ⟨u, huU⟩ := hU_ne
        obtain ⟨x, y, hxy, hne⟩ := essential u
        have hBeq : B x = B y := hB_congr x y (fun j hjV => by
          apply hxy
          intro hju
          subst hju
          exact hUV_disj j ⟨huU, hjV⟩)
        have hfeq : target x = target y := by rw [hf_and x, hf_and y, hAtrue x, hAtrue y, hBeq]
        exact absurd hfeq hne
    have hB0 : B e0 = false := by
      cases hBe0 : B e0
      · rfl
      · have hBtrue : ∀ x, B x = true := fun x => hB_mono e0 x (fun _ h => by simp [e0] at h) hBe0
        obtain ⟨v, hvV⟩ := hV_ne
        obtain ⟨x, y, hxy, hne⟩ := essential v
        have hAeq : A x = A y := hA_congr x y (fun j hjU => by
          apply hxy
          intro hjv
          subst hjv
          exact hUV_disj j ⟨hjU, hvV⟩)
        have hfeq : target x = target y := by rw [hf_and x, hf_and y, hBtrue x, hBtrue y, hAeq]
        exact absurd hfeq hne
    have hedge_opp : ∀ u v : Fin 6, target (e2 u v) = true →
        (u ∈ U ∧ v ∈ V) ∨ (u ∈ V ∧ v ∈ U) := by
      intro u v huv
      rw [hf_and, Bool.and_eq_true] at huv
      rcases hUV_cover u with huU | huV <;> rcases hUV_cover v with hvU | hvV
      · exfalso
        have hBeq : B (e2 u v) = B e0 := hB_congr (e2 u v) e0 (fun j hjV => by
          have hju : j ≠ u := fun h => hUV_disj j ⟨h ▸ huU, hjV⟩
          have hjv : j ≠ v := fun h => hUV_disj j ⟨h ▸ hvU, hjV⟩
          simp [e2, e0, hju, hjv])
        rw [hBeq, hB0] at huv
        exact Bool.false_ne_true huv.2
      · exact Or.inl ⟨huU, hvV⟩
      · exact Or.inr ⟨huV, hvU⟩
      · exfalso
        have hAeq : A (e2 u v) = A e0 := hA_congr (e2 u v) e0 (fun j hjU => by
          have hju : j ≠ u := fun h => hUV_disj j ⟨hjU, h ▸ huV⟩
          have hjv : j ≠ v := fun h => hUV_disj j ⟨hjU, h ▸ hvV⟩
          simp [e2, e0, hju, hjv])
        rw [hAeq, hA0] at huv
        exact Bool.false_ne_true huv.1
    have hedge_A : ∀ u v : Fin 6, target (e2 u v) = true → u ∈ U → v ∈ V → A (e1 u) = true := by
      intro u v huv huU hvV
      rw [hf_and, Bool.and_eq_true] at huv
      have hAeq : A (e1 u) = A (e2 u v) := hA_congr (e1 u) (e2 u v) (fun j hjU => by
        have hjv : j ≠ v := fun h => hUV_disj j ⟨hjU, h ▸ hvV⟩
        simp [e1, e2, hjv])
      rw [hAeq]; exact huv.1
    have hedge_B : ∀ u v : Fin 6, target (e2 u v) = true → u ∈ U → v ∈ V → B (e1 v) = true := by
      intro u v huv huU hvV
      rw [hf_and, Bool.and_eq_true] at huv
      have hBeq : B (e1 v) = B (e2 u v) := hB_congr (e1 v) (e2 u v) (fun j hjV => by
        have hju : j ≠ u := fun h => hUV_disj j ⟨h ▸ huU, hjV⟩
        simp [e1, e2, hju])
      rw [hBeq]; exact huv.2
    have he32 : target (e2 3 2) = true := by decide
    have he20 : target (e2 2 0) = true := by decide
    have he04 : target (e2 0 4) = true := by decide
    have he34 : target (e2 3 4) = false := by decide
    have h32 := hedge_opp 3 2 he32
    have h20 := hedge_opp 2 0 he20
    have h04 := hedge_opp 0 4 he04
    rcases h32 with ⟨h3U, h2V⟩ | ⟨h3V, h2U⟩
    · have h0U : (0 : Fin 6) ∈ U := by
        rcases h20 with ⟨h2U, _⟩ | ⟨_, h0U⟩
        · exact absurd ⟨h2U, h2V⟩ (hUV_disj 2)
        · exact h0U
      have h4V : (4 : Fin 6) ∈ V := by
        rcases h04 with ⟨_, h4V⟩ | ⟨h0V, _⟩
        · exact h4V
        · exact absurd ⟨h0U, h0V⟩ (hUV_disj 0)
      have hA3 : A (e1 3) = true := hedge_A 3 2 he32 h3U h2V
      have hB4 : B (e1 4) = true := hedge_B 0 4 he04 h0U h4V
      have hA34 : A (e2 3 4) = A (e1 3) := hA_congr (e2 3 4) (e1 3) (fun j hjU => by
        have hj4 : j ≠ 4 := fun h => hUV_disj j ⟨hjU, h ▸ h4V⟩
        simp [e2, e1, hj4])
      have hB34 : B (e2 3 4) = B (e1 4) := hB_congr (e2 3 4) (e1 4) (fun j hjV => by
        have hj3 : j ≠ 3 := fun h => hUV_disj j ⟨h ▸ h3U, hjV⟩
        simp [e2, e1, hj3])
      have ht34 : target (e2 3 4) = true := by rw [hf_and, hA34, hB34, hA3, hB4]; rfl
      rw [he34] at ht34
      exact Bool.false_ne_true ht34
    · have h0V : (0 : Fin 6) ∈ V := by
        rcases h20 with ⟨_, h0V⟩ | ⟨h2V, _⟩
        · exact h0V
        · exact absurd ⟨h2U, h2V⟩ (hUV_disj 2)
      have h4U : (4 : Fin 6) ∈ U := by
        rcases h04 with ⟨h0U, _⟩ | ⟨_, h4U⟩
        · exact absurd ⟨h0U, h0V⟩ (hUV_disj 0)
        · exact h4U
      have he40 : target (e2 4 0) = true := by decide
      have he23 : target (e2 2 3) = true := by decide
      have hA4 : A (e1 4) = true := hedge_A 4 0 he40 h4U h0V
      have hB3 : B (e1 3) = true := hedge_B 2 3 he23 h2U h3V
      have hA34 : A (e2 3 4) = A (e1 4) := hA_congr (e2 3 4) (e1 4) (fun j hjU => by
        have hj3 : j ≠ 3 := fun h => hUV_disj j ⟨hjU, h ▸ h3V⟩
        simp [e2, e1, hj3])
      have hB34 : B (e2 3 4) = B (e1 3) := hB_congr (e2 3 4) (e1 3) (fun j hjV => by
        have hj4 : j ≠ 4 := fun h => hUV_disj j ⟨h ▸ h4U, hjV⟩
        simp [e2, e1, hj4])
      have ht34 : target (e2 3 4) = true := by rw [hf_and, hA34, hB34, hA4, hB3]; rfl
      rw [he34] at ht34
      exact Bool.false_ne_true ht34
  · have hf_or : ∀ x, target x = (A x || B x) := by
      intro x; rw [← hval_out x]; exact hor x
    have h0 : target e0 = false := by decide
    rw [hf_or, Bool.or_eq_false_iff] at h0
    have hA1 : ∀ u ∈ U, A (e1 u) = false := by
      intro u huU
      have h1 : target (e1 u) = false := by fin_cases u <;> decide
      rw [hf_or, Bool.or_eq_false_iff] at h1
      exact h1.1
    have hB1 : ∀ v ∈ V, B (e1 v) = false := by
      intro v hvV
      have h1 : target (e1 v) = false := by fin_cases v <;> decide
      rw [hf_or, Bool.or_eq_false_iff] at h1
      exact h1.2
    have hedge_same : ∀ u v : Fin 6, target (e2 u v) = true → (u ∈ U ↔ v ∈ U) := by
      intro u v huv
      constructor
      · intro huU
        rcases hUV_cover v with hvU | hvV
        · exact hvU
        · exfalso
          have hAeq : A (e2 u v) = A (e1 u) := hA_congr (e2 u v) (e1 u) (fun j hjU => by
            have hjv : j ≠ v := fun h => hUV_disj j ⟨hjU, h ▸ hvV⟩
            simp [e2, e1, hjv])
          have hBeq : B (e2 u v) = B (e1 v) := hB_congr (e2 u v) (e1 v) (fun j hjV => by
            have hju : j ≠ u := fun h => hUV_disj j ⟨h ▸ huU, hjV⟩
            simp [e2, e1, hju])
          rw [hf_or, hAeq, hBeq, hA1 u huU, hB1 v hvV] at huv
          exact Bool.false_ne_true huv
      · intro hvU
        rcases hUV_cover u with huU | huV
        · exact huU
        · exfalso
          have hAeq : A (e2 u v) = A (e1 v) := hA_congr (e2 u v) (e1 v) (fun j hjU => by
            have hju : j ≠ u := fun h => hUV_disj j ⟨hjU, h ▸ huV⟩
            simp [e2, e1, hju])
          have hBeq : B (e2 u v) = B (e1 u) := hB_congr (e2 u v) (e1 u) (fun j hjV => by
            have hjv : j ≠ v := fun h => hUV_disj j ⟨h ▸ hvU, hjV⟩
            simp [e2, e1, hjv])
          rw [hf_or, hAeq, hBeq, hA1 v hvU, hB1 u huV] at huv
          exact Bool.false_ne_true huv
    have h32 : (3 : Fin 6) ∈ U ↔ (2 : Fin 6) ∈ U := hedge_same 3 2 (by decide)
    have h20 : (2 : Fin 6) ∈ U ↔ (0 : Fin 6) ∈ U := hedge_same 2 0 (by decide)
    have h04 : (0 : Fin 6) ∈ U ↔ (4 : Fin 6) ∈ U := hedge_same 0 4 (by decide)
    have h41 : (4 : Fin 6) ∈ U ↔ (1 : Fin 6) ∈ U := hedge_same 4 1 (by decide)
    have h15 : (1 : Fin 6) ∈ U ↔ (5 : Fin 6) ∈ U := hedge_same 1 5 (by decide)
    have hall_iff : ∀ i : Fin 6, i ∈ U ↔ (0 : Fin 6) ∈ U := by
      intro i
      fin_cases i
      · exact Iff.rfl
      · exact h41.symm.trans h04.symm
      · exact h20
      · exact h32.trans h20
      · exact h04.symm
      · exact h15.symm.trans (h41.symm.trans h04.symm)
    by_cases h0U : (0 : Fin 6) ∈ U
    · obtain ⟨v, hvV⟩ := hV_ne
      exact hUV_disj v ⟨(hall_iff v).mpr h0U, hvV⟩
    · obtain ⟨u, huU⟩ := hU_ne
      exact h0U ((hall_iff u).mp huU)

end PEqualNP.Outside.L_meta_5488

theorem PEqualNP.Outside.L_meta_5488 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 2) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3)) t → 6 ≤ t := by
  exact PEqualNP.Outside.L_meta_5488.lower_bound
