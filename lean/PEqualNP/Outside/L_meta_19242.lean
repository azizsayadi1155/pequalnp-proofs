import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19242

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩], 12⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 5 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (494 : ℕ).testBit (4 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_19242

theorem PEqualNP.Outside.L_meta_19242 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (494 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19242.wit, PEqualNP.Outside.L_meta_19242.wit_fan, PEqualNP.Outside.L_meta_19242.wit_size,
    PEqualNP.Outside.L_meta_19242.wit_rep⟩
