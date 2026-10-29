module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B21 : ModeBlockData :=
  ⟨⟨21, 22, (12581949418901205713/5000000000000000000000 : ℚ), (9864709301326533/2500000000000000000000 : ℚ)⟩, [
    (21, modeDataJ5M22)], (1006555953512096457/400000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b21 : entryChecks 5 bflatBlockJ5B21.entries = true := by
  simp only [entryChecks,bflatBlockJ5B21,List.all_cons,List.all_nil,
    mode_checked_j5_m22,Bool.and_self]
theorem block_mass_checked_j5_b21 : blockMassCheck bflatBlockJ5B21 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
