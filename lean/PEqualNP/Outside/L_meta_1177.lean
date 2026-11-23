import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1177_aux

open PEqualNP.CircuitLowerBounds

/-- The 9-gate monotone circuit from the gap sketch. Inputs are wires 0 to 7;
gate `j` produces wire `8 + j`; the output is the last wire, 16. -/
def c : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,    -- 8  = x1 ∨ x2
    ⟨GateOp.or, [8, 3]⟩,    -- 9  = x1 ∨ x2 ∨ x3
    ⟨GateOp.or, [9, 4]⟩,    -- 10 = x1 ∨ x2 ∨ x3 ∨ x4
    ⟨GateOp.and, [0, 10]⟩,  -- 11 = x0 ∧ (x1 ∨ x2 ∨ x3 ∨ x4)
    ⟨GateOp.or, [5, 6]⟩,    -- 12 = x5 ∨ x6
    ⟨GateOp.and, [1, 12]⟩,  -- 13 = x1 ∧ (x5 ∨ x6)
    ⟨GateOp.and, [5, 7]⟩,   -- 14 = x5 ∧ x7
    ⟨GateOp.or, [11, 13]⟩,  -- 15
    ⟨GateOp.or, [15, 14]⟩], -- 16 = output
   16⟩

set_option maxRecDepth 100000 in
theorem k : ∀ a b c' d e f g h : Bool,
    c.eval [a, b, c', d, e, f, g, h] =
      ((a && b) || (a && c') || (a && d) || (a && e) || (b && f) || (b && g) || (f && h)) := by
  decide

end PEqualNP.Outside.L_meta_1177_aux

theorem PEqualNP.Outside.L_meta_1177 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1177_aux.c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1177_aux.c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1177_aux.k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
