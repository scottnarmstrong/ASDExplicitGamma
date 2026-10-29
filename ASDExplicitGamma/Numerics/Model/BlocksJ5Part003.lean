module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B3 : ModeBlockData :=
  ⟨⟨3, 4, (3152323370589605753/1250000000000000000000 : ℚ), (39513340085113249/10000000000000000000000 : ℚ)⟩, [
    (3, modeDataJ5M4)], (25218586964716846023/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b3 : entryChecks 5 bflatBlockJ5B3.entries = true := by
  simp only [entryChecks,bflatBlockJ5B3,List.all_cons,List.all_nil,
    mode_checked_j5_m4,Bool.and_self]
theorem block_mass_checked_j5_b3 : blockMassCheck bflatBlockJ5B3 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
