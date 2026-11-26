import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19308

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 18]⟩], 19⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 10 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7572604 : ℕ).testBit (5 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_19308

theorem PEqualNP.Outside.L_meta_19308 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7572604 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19308.wit, PEqualNP.Outside.L_meta_19308.wit_fan, PEqualNP.Outside.L_meta_19308.wit_size,
    PEqualNP.Outside.L_meta_19308.wit_rep⟩
