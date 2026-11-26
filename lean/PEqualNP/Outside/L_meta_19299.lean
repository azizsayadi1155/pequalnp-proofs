import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19299

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 18]⟩], 19⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 10 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (16238126 : ℕ).testBit (5 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_19299

theorem PEqualNP.Outside.L_meta_19299 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16238126 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19299.wit, PEqualNP.Outside.L_meta_19299.wit_fan, PEqualNP.Outside.L_meta_19299.wit_size,
    PEqualNP.Outside.L_meta_19299.wit_rep⟩
