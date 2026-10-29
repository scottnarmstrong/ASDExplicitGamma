module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B56 : ModeBlockData :=
  ⟨⟨56, 57, (173336518075713419/1250000000000000000000 : ℚ), (130363408213421109/1000000000000000000000 : ℚ)⟩, [
    (56, modeDataJ2M57)], (1386692144605707351/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b56 : entryChecks 2 bflatBlockJ2B56.entries = true := by
  simp only [entryChecks,bflatBlockJ2B56,List.all_cons,List.all_nil,
    mode_checked_j2_m57,Bool.and_self]
theorem block_mass_checked_j2_b56 : blockMassCheck bflatBlockJ2B56 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
