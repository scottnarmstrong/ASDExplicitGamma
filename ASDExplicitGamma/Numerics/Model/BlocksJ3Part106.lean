module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part011

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B106 : ModeBlockData :=
  ⟨⟨179, 183, (535516954887626487/10000000000000000000000 : ℚ), (255701600652569573/5000000000000000000000 : ℚ)⟩, [
    (179, modeDataJ3M180),
    (180, modeDataJ3M181),
    (181, modeDataJ3M182),
    (182, modeDataJ3M183)], (535516954887626483/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b106 : entryChecks 3 bflatBlockJ3B106.entries = true := by
  simp only [entryChecks,bflatBlockJ3B106,List.all_cons,List.all_nil,
    mode_checked_j3_m180,
    mode_checked_j3_m181,
    mode_checked_j3_m182,
    mode_checked_j3_m183,Bool.and_self]
theorem block_mass_checked_j3_b106 : blockMassCheck bflatBlockJ3B106 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
