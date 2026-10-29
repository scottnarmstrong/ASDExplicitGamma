module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B51 : ModeBlockData :=
  ⟨⟨51, 52, (366860977153778639/2000000000000000000000 : ℚ), (791251879052686997/5000000000000000000000 : ℚ)⟩, [
    (51, modeDataJ2M52)], (917152442884446597/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b51 : entryChecks 2 bflatBlockJ2B51.entries = true := by
  simp only [entryChecks,bflatBlockJ2B51,List.all_cons,List.all_nil,
    mode_checked_j2_m52,Bool.and_self]
theorem block_mass_checked_j2_b51 : blockMassCheck bflatBlockJ2B51 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
