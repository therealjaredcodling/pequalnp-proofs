import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9285

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[
    -- Each consecutive triple of columns contains one of these three pairs.
    ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [10, 11]⟩,
    -- Extend the shared pairs to the neighborhoods of rows zero through five.
    ⟨.or, [12, 8]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [13, 10]⟩,
    ⟨.or, [14, 9]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [12, 11]⟩,
    -- Select the neighborhood of the active row.
    ⟨.and, [0, 15]⟩, ⟨.and, [1, 16]⟩, ⟨.and, [2, 17]⟩,
    ⟨.and, [3, 18]⟩, ⟨.and, [4, 19]⟩, ⟨.and, [5, 20]⟩,
    ⟨.or, [21, 22]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [25, 26]⟩,
    ⟨.or, [27, 28]⟩, ⟨.or, [30, 29]⟩], 31⟩

end PEqualNP.Outside.L_meta_9285

theorem PEqualNP.Outside.L_meta_9285 :
    ¬ (¬ PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 6 => (38417843079 : ℕ).testBit (6 * u.val + v.val)) 20) := by
  intro lower
  apply lower
  refine ⟨PEqualNP.Outside.L_meta_9285.circuit, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_9285.circuit]
