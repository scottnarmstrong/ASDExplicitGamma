module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part007

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B88 : ModeBlockData :=
  ⟨⟨118, 121, (1081268613862324631/10000000000000000000000 : ℚ), (1868873405793673/20000000000000000000 : ℚ)⟩, [
    (118, modeDataJ3M119),
    (119, modeDataJ3M120),
    (120, modeDataJ3M121)], (270317153465581157/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b88 : entryChecks 3 bflatBlockJ3B88.entries = true := by
  simp only [entryChecks,bflatBlockJ3B88,List.all_cons,List.all_nil,
    mode_checked_j3_m119,
    mode_checked_j3_m120,
    mode_checked_j3_m121,Bool.and_self]
theorem block_mass_checked_j3_b88 : blockMassCheck bflatBlockJ3B88 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
