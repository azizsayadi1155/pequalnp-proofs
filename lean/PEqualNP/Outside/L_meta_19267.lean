import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19267

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩], 11⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 4 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (23 : ℕ).testBit (4 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_19267

theorem PEqualNP.Outside.L_meta_19267 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (23 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19267.wit, PEqualNP.Outside.L_meta_19267.wit_fan, PEqualNP.Outside.L_meta_19267.wit_size,
    PEqualNP.Outside.L_meta_19267.wit_rep⟩
