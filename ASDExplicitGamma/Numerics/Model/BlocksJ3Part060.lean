module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B60 : ModeBlockData :=
  ⟨⟨60, 61, (51514381285095741099/10000000000000000000000 : ℚ), (1383453678018113621/10000000000000000000000 : ℚ)⟩, [
    (60, modeDataJ3M61)], (25757190642547870549/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b60 : entryChecks 3 bflatBlockJ3B60.entries = true := by
  simp only [entryChecks,bflatBlockJ3B60,List.all_cons,List.all_nil,
    mode_checked_j3_m61,Bool.and_self]
theorem block_mass_checked_j3_b60 : blockMassCheck bflatBlockJ3B60 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
