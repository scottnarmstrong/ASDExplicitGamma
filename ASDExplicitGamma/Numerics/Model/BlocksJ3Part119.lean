module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part014
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part015

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B119 : ModeBlockData :=
  ⟨⟨239, 244, (45270743143630191/1250000000000000000000 : ℚ), (88319558005148961/2500000000000000000000 : ℚ)⟩, [
    (239, modeDataJ3M240),
    (240, modeDataJ3M241),
    (241, modeDataJ3M242),
    (242, modeDataJ3M243),
    (243, modeDataJ3M244)], (362165945149041523/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b119 : entryChecks 3 bflatBlockJ3B119.entries = true := by
  simp only [entryChecks,bflatBlockJ3B119,List.all_cons,List.all_nil,
    mode_checked_j3_m240,
    mode_checked_j3_m241,
    mode_checked_j3_m242,
    mode_checked_j3_m243,
    mode_checked_j3_m244,Bool.and_self]
theorem block_mass_checked_j3_b119 : blockMassCheck bflatBlockJ3B119 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
