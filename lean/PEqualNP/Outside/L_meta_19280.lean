import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19280

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩], 11⟩

theorem wit_fan : PEqualNP.MetaComplexity.FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem wit_size : wit.size ≤ 4 := by decide

theorem wit_rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => (6015 : ℕ).testBit (4 * u.val + v.val)) wit := by
  decide

end PEqualNP.Outside.L_meta_19280

theorem PEqualNP.Outside.L_meta_19280 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (6015 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19280.wit, PEqualNP.Outside.L_meta_19280.wit_fan, PEqualNP.Outside.L_meta_19280.wit_size,
    PEqualNP.Outside.L_meta_19280.wit_rep⟩
