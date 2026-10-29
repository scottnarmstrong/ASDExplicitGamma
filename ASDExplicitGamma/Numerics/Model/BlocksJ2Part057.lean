module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B57 : ModeBlockData :=
  ⟨⟨57, 58, (331289005717900539/2500000000000000000000 : ℚ), (251366829756002599/2000000000000000000000 : ℚ)⟩, [
    (57, modeDataJ2M58)], (265031204574320431/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b57 : entryChecks 2 bflatBlockJ2B57.entries = true := by
  simp only [entryChecks,bflatBlockJ2B57,List.all_cons,List.all_nil,
    mode_checked_j2_m58,Bool.and_self]
theorem block_mass_checked_j2_b57 : blockMassCheck bflatBlockJ2B57 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
