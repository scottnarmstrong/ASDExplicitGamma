module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B25 : ModeBlockData :=
  ⟨⟨25, 26, (25141493902763808181/10000000000000000000000 : ℚ), (2464781302503307/625000000000000000000 : ℚ)⟩, [
    (25, modeDataJ5M26)], (1257074695138190409/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b25 : entryChecks 5 bflatBlockJ5B25.entries = true := by
  simp only [entryChecks,bflatBlockJ5B25,List.all_cons,List.all_nil,
    mode_checked_j5_m26,Bool.and_self]
theorem block_mass_checked_j5_b25 : blockMassCheck bflatBlockJ5B25 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
