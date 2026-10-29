module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B31 : ModeBlockData :=
  ⟨⟨31, 32, (1985079374823856083/5000000000000000000000 : ℚ), (1981997392991090907/5000000000000000000000 : ℚ)⟩, [
    (31, modeDataJ0M32)], (794031749929542433/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b31 : entryChecks 0 bflatBlockJ0B31.entries = true := by
  simp only [entryChecks,bflatBlockJ0B31,List.all_cons,List.all_nil,
    mode_checked_j0_m32,Bool.and_self]
theorem block_mass_checked_j0_b31 : blockMassCheck bflatBlockJ0B31 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
