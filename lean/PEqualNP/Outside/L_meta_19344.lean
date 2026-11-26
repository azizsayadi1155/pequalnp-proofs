import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19344

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩], 16⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 7 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577382 : ℕ).testBit (5 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_19344

theorem PEqualNP.Outside.L_meta_19344 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577382 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19344.wit, PEqualNP.Outside.L_meta_19344.wit_fan, PEqualNP.Outside.L_meta_19344.wit_size,
    PEqualNP.Outside.L_meta_19344.wit_rep⟩
