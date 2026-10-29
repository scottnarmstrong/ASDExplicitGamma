module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part014

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B116 : ModeBlockData :=
  ⟨⟨224, 229, (208049657326629969/5000000000000000000000 : ℚ), (201372297668055623/5000000000000000000000 : ℚ)⟩, [
    (224, modeDataJ3M225),
    (225, modeDataJ3M226),
    (226, modeDataJ3M227),
    (227, modeDataJ3M228),
    (228, modeDataJ3M229)], (416099314653259933/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b116 : entryChecks 3 bflatBlockJ3B116.entries = true := by
  simp only [entryChecks,bflatBlockJ3B116,List.all_cons,List.all_nil,
    mode_checked_j3_m225,
    mode_checked_j3_m226,
    mode_checked_j3_m227,
    mode_checked_j3_m228,
    mode_checked_j3_m229,Bool.and_self]
theorem block_mass_checked_j3_b116 : blockMassCheck bflatBlockJ3B116 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
