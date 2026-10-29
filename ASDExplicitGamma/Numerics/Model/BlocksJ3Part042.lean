module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B42 : ModeBlockData :=
  ⟨⟨42, 43, (111460040871540068621/10000000000000000000000 : ℚ), (2079946560057573841/10000000000000000000000 : ℚ)⟩, [
    (42, modeDataJ3M43)], (5573002043577003431/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b42 : entryChecks 3 bflatBlockJ3B42.entries = true := by
  simp only [entryChecks,bflatBlockJ3B42,List.all_cons,List.all_nil,
    mode_checked_j3_m43,Bool.and_self]
theorem block_mass_checked_j3_b42 : blockMassCheck bflatBlockJ3B42 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
