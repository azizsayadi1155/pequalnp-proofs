import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19295

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 18]⟩], 19⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 10 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (16235644 : ℕ).testBit (5 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_19295

theorem PEqualNP.Outside.L_meta_19295 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16235644 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19295.wit, PEqualNP.Outside.L_meta_19295.wit_fan, PEqualNP.Outside.L_meta_19295.wit_size,
    PEqualNP.Outside.L_meta_19295.wit_rep⟩
