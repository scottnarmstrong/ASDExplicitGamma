module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B30 : ModeBlockData :=
  ⟨⟨30, 31, (25108270028978792439/10000000000000000000000 : ℚ), (7880674158980527/2000000000000000000000 : ℚ)⟩, [
    (30, modeDataJ5M31)], (12554135014489396219/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b30 : entryChecks 5 bflatBlockJ5B30.entries = true := by
  simp only [entryChecks,bflatBlockJ5B30,List.all_cons,List.all_nil,
    mode_checked_j5_m31,Bool.and_self]
theorem block_mass_checked_j5_b30 : blockMassCheck bflatBlockJ5B30 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
