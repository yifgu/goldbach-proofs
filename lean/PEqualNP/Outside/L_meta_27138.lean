import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27138
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def first : Gate := ⟨.and, [0, 1]⟩
def second : Gate := ⟨.and, [0, 4]⟩

def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def beforeTail (x : Fin 9 → Bool) : List Bool := step (step (List.ofFn x) first) second

def yes (i j : Fin 9) : Bool :=
  ([161, 98, 84, 140, 84, 98, 84, 140, 266] : List ℕ).getD i.val 0 |>.testBit j.val

def no (i j : Fin 9) : Bool :=
  ([160, 96, 80, 132, 68, 66, 20, 12, 10] : List ℕ).getD i.val 0 |>.testBit j.val

theorem separates : ∀ i : Fin 9, matching (yes i) = true ∧ matching (no i) = false := by
  decide +kernel

theorem prefixAgree : ∀ (i : Fin 9) (j : Fin 11), j.val ≠ i.val →
    (beforeTail (yes i)).getD j.val false = (beforeTail (no i)).getD j.val false := by
  decide +kernel

theorem beforeLen (x : Fin 9 → Bool) : (beforeTail x).length = 11 := by
  simp [beforeTail, step]

theorem agreeAll (i : Fin 9) (j : ℕ) (hne : j ≠ i.val) :
    (beforeTail (yes i)).getD j false = (beforeTail (no i)).getD j false := by
  by_cases hj : j < 11
  · exact prefixAgree i ⟨j, hj⟩ hne
  · simp [List.getD_eq_getElem?_getD, beforeLen, Nat.le_of_not_gt hj]

theorem agreeRun (gs : List Gate) (i : ℕ) (havoid : i ∉ gs.flatMap Gate.inputs)
    (u v : List Bool) (hlen : u.length = v.length)
    (hag : ∀ j, j ≠ i → u.getD j false = v.getD j false) :
    ∀ j, j ≠ i → (gs.foldl step u).getD j false = (gs.foldl step v).getD j false := by
  induction gs generalizing u v with
  | nil => exact hag
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at havoid
    change ∀ j, j ≠ i → (gs.foldl step (step u g)).getD j false =
      (gs.foldl step (step v g)).getD j false
    apply ih havoid.2 _ _ (by simp [step, hlen])
    have hm : (g.inputs.map fun j => u.getD j false) = (g.inputs.map fun j => v.getD j false) :=
      List.map_congr_left (fun j hj => hag j (fun e => havoid.1 (e ▸ hj)))
    intro j hj
    unfold step
    rw [hm]
    by_cases hj' : j < u.length
    · have hv : j < v.length := hlen ▸ hj'
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj',
        List.getElem?_append_left hv] using hag j hj
    · have hu : u.length ≤ j := Nat.le_of_not_gt hj'
      have hv : v.length ≤ j := hlen ▸ hu
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hu,
        List.getElem?_append_right hv, hlen]

theorem allInputReads (gs : List Gate) (o : ℕ) (ho : 9 ≤ o)
    (he : ∀ x, (Circuit.mk (first :: second :: gs) o).eval (List.ofFn x) = matching x)
    (i : Fin 9) : i.val ∈ gs.flatMap Gate.inputs := by
  by_contra ha
  have hs := agreeRun gs i.val ha (beforeTail (yes i)) (beforeTail (no i))
    (by rw [beforeLen, beforeLen]) (agreeAll i) o (by have := i.isLt; omega)
  change (Circuit.mk (first :: second :: gs) o).eval (List.ofFn (yes i)) =
    (Circuit.mk (first :: second :: gs) o).eval (List.ofFn (no i)) at hs
  rw [he, he, (separates i).1, (separates i).2] at hs
  contradiction

theorem allGateReads (gs : List Gate)
    (hlive : ∀ j : Fin (first :: second :: gs).length, j.val + 1 < (first :: second :: gs).length →
      ∃ k : Fin (first :: second :: gs).length, j.val < k.val ∧
        9 + j.val ∈ ((first :: second :: gs).get k).inputs)
    (j : ℕ) (hj : j + 1 < (first :: second :: gs).length) :
    9 + j ∈ gs.flatMap Gate.inputs := by
  obtain ⟨⟨k, hk⟩, hjk, hm⟩ := hlive ⟨j, by omega⟩ hj
  change j < k at hjk
  change 9 + j ∈ ((first :: second :: gs).get ⟨k, hk⟩).inputs at hm
  rcases k with _ | _ | k
  · omega
  · change 9 + j ∈ [0, 4] at hm
    simp at hm
    omega
  · have klt : k < gs.length := by simp at hk; omega
    exact List.mem_flatMap.mpr ⟨gs[k], List.getElem_mem klt, hm⟩

theorem sumInputs (gs : List Gate) (hs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := hs g (by simp)
    have ht := ih (fun g hg => hs g (by simp [hg]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem lower (C : Circuit) (hfan : FanInTwo C)
    (he : ∀ x, C.eval (List.ofFn x) = matching x)
    (ho : C.output + 1 = 9 + C.size)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (hh : C.gates.head? = some first) (ht : C.gates.tail.head? = some second) : 12 ≤ C.size := by
  rcases C with ⟨_ | ⟨g?, _ | ⟨h?, gs⟩⟩, o⟩
  · simp at hh
  · simp at ht
  · simp only [List.head?_cons, Option.some.injEq] at hh
    change some h? = some second at ht
    have ht' := Option.some.inj ht
    subst g?; subst h?
    have hout : 9 ≤ o := by change o + 1 = 9 + (first :: second :: gs).length at ho; simp at ho; omega
    have hcount := sumInputs gs (fun g hg => (hfan g (by simp [hg])).2)
    have hall : Finset.range (9 + gs.length + 1) ⊆ (gs.flatMap Gate.inputs).toFinset := by
      intro w hw
      have hw' := Finset.mem_range.mp hw
      apply List.mem_toFinset.mpr
      by_cases h9 : w < 9
      · exact allInputReads gs o hout he ⟨w, h9⟩
      · have hj : (w - 9) + 1 < (first :: second :: gs).length := by simp; omega
        have hv := allGateReads gs hlive (w - 9) hj
        rwa [show 9 + (w - 9) = w by omega] at hv
    have hc := Finset.card_le_card hall
    rw [Finset.card_range] at hc
    have hlist : (gs.flatMap Gate.inputs).toFinset.card ≤ (gs.flatMap Gate.inputs).length :=
      List.toFinset_card_le _
    change 12 ≤ (first :: second :: gs).length
    simp only [List.length_cons]
    omega

end PEqualNP.Outside.L_meta_27138

theorem PEqualNP.Outside.L_meta_27138 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩) := by
  rintro ⟨C, hfan, hs, he, ho, _, _, hl, hh, ht⟩
  have := L_meta_27138.lower C hfan he ho hl hh ht
  omega
