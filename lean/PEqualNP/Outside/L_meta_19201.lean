import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19201

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩], 14⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 7 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (4829 : ℕ).testBit (4 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_19201

theorem PEqualNP.Outside.L_meta_19201 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4829 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19201.wit, PEqualNP.Outside.L_meta_19201.wit_fan, PEqualNP.Outside.L_meta_19201.wit_size,
    PEqualNP.Outside.L_meta_19201.wit_rep⟩
