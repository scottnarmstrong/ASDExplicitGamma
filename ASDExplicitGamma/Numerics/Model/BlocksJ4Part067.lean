module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B67 : ModeBlockData :=
  ⟨⟨76, 80, (58351434726585964727/2500000000000000000000 : ℚ), (1209461029966134533/10000000000000000000000 : ℚ)⟩, [
    (76, modeDataJ4M77),
    (77, modeDataJ4M78),
    (78, modeDataJ4M79),
    (79, modeDataJ4M80)], (29175717363292982363/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b67 : entryChecks 4 bflatBlockJ4B67.entries = true := by
  simp only [entryChecks,bflatBlockJ4B67,List.all_cons,List.all_nil,
    mode_checked_j4_m77,
    mode_checked_j4_m78,
    mode_checked_j4_m79,
    mode_checked_j4_m80,Bool.and_self]
theorem block_mass_checked_j4_b67 : blockMassCheck bflatBlockJ4B67 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
