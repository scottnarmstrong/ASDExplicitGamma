module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B52 : ModeBlockData :=
  ⟨⟨52, 53, (69055931409728431/400000000000000000000 : ℚ), (759992329107080099/5000000000000000000000 : ℚ)⟩, [
    (52, modeDataJ2M53)], (863199142621605387/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b52 : entryChecks 2 bflatBlockJ2B52.entries = true := by
  simp only [entryChecks,bflatBlockJ2B52,List.all_cons,List.all_nil,
    mode_checked_j2_m53,Bool.and_self]
theorem block_mass_checked_j2_b52 : blockMassCheck bflatBlockJ2B52 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
