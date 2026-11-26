import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19202

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩], 14⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 7 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (4831 : ℕ).testBit (4 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_19202

theorem PEqualNP.Outside.L_meta_19202 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4831 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19202.wit, PEqualNP.Outside.L_meta_19202.wit_fan, PEqualNP.Outside.L_meta_19202.wit_size,
    PEqualNP.Outside.L_meta_19202.wit_rep⟩
