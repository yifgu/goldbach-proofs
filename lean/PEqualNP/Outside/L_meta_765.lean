import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L112
import PEqualNP.MetaComplexity.L153

namespace PEqualNP.Outside.L_meta_765_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem hcs_mono {m : Nat} {f : (Fin m -> Bool) -> Bool} {a b : Nat}
    (h : HasCircuitSize m f a) (hab : a <= b) : HasCircuitSize m f b := by
  obtain ⟨C, hfan, hsize, hsem⟩ := h
  exact ⟨C, hfan, Nat.le_trans hsize hab, hsem⟩

end PEqualNP.Outside.L_meta_765_aux

theorem PEqualNP.Outside.L_meta_765 :
    forall s : Nat, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 -> Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s
      ↔ 5 <= s := by
  intro s
  let g : (Fin 4 -> Bool) -> Bool := fun y => (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 0)
  have hfun : (fun x : Fin 6 -> Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2))
      = (fun x : Fin 6 -> Bool => (x 0 && x 1) || g (fun j : Fin 4 => x (Fin.natAdd 2 j))) := by
    funext x
    revert x
    decide
  rw [hfun]
  have hnc : ∃ y y' : Fin 4 -> Bool, g y ≠ g y' :=
    ⟨fun _ => false, fun j => decide (j.val <= 1), by decide⟩
  have key : forall t : Nat, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 -> Bool => (x 0 && x 1) || g (fun j : Fin 4 => x (Fin.natAdd 2 j))) (t + 2)
      ↔ PEqualNP.MetaComplexity.HasCircuitSize 4 g t := by
    intro t
    have h := PEqualNP.MetaComplexity.L153 4 t g hnc
    convert h using 2
    funext x
    revert x
    decide
  have hL : forall t : Nat, PEqualNP.MetaComplexity.HasCircuitSize 4 g t ↔ 3 <= t := by
    intro t
    exact PEqualNP.MetaComplexity.L112 t
  rcases Nat.lt_or_ge s 2 with h2 | h2
  · constructor
    · intro h
      have h2' : PEqualNP.MetaComplexity.HasCircuitSize 6
          (fun x : Fin 6 -> Bool => (x 0 && x 1) || g (fun j : Fin 4 => x (Fin.natAdd 2 j))) 2 :=
        PEqualNP.Outside.L_meta_765_aux.hcs_mono h (by omega)
      have h3 : PEqualNP.MetaComplexity.HasCircuitSize 4 g 0 := (key 0).1 h2'
      have h4 : 3 <= 0 := (hL 0).1 h3
      omega
    · intro hb
      omega
  · have hsub : s - 2 + 2 = s := by omega
    calc PEqualNP.MetaComplexity.HasCircuitSize 6
          (fun x : Fin 6 -> Bool => (x 0 && x 1) || g (fun j : Fin 4 => x (Fin.natAdd 2 j))) s
        ↔ PEqualNP.MetaComplexity.HasCircuitSize 6
          (fun x : Fin 6 -> Bool => (x 0 && x 1) || g (fun j : Fin 4 => x (Fin.natAdd 2 j))) (s - 2 + 2) := by rw [hsub]
      _ ↔ PEqualNP.MetaComplexity.HasCircuitSize 4 g (s - 2) := key (s - 2)
      _ ↔ 3 <= s - 2 := hL (s - 2)
      _ ↔ 5 <= s := by omega
