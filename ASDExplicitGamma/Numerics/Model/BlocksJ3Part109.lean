module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part011
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part012

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B109 : ModeBlockData :=
  ⟨⟨191, 195, (484399303406193887/10000000000000000000000 : ℚ), (2238195331207221/50000000000000000000 : ℚ)⟩, [
    (191, modeDataJ3M192),
    (192, modeDataJ3M193),
    (193, modeDataJ3M194),
    (194, modeDataJ3M195)], (484399303406193883/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b109 : entryChecks 3 bflatBlockJ3B109.entries = true := by
  simp only [entryChecks,bflatBlockJ3B109,List.all_cons,List.all_nil,
    mode_checked_j3_m192,
    mode_checked_j3_m193,
    mode_checked_j3_m194,
    mode_checked_j3_m195,Bool.and_self]
theorem block_mass_checked_j3_b109 : blockMassCheck bflatBlockJ3B109 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
