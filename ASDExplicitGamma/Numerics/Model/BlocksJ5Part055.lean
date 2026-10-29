module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B55 : ModeBlockData :=
  ⟨⟨55, 56, (12428015759568899533/5000000000000000000000 : ℚ), (39151536942305177/10000000000000000000000 : ℚ)⟩, [
    (55, modeDataJ5M56)], (4971206303827559813/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b55 : entryChecks 5 bflatBlockJ5B55.entries = true := by
  simp only [entryChecks,bflatBlockJ5B55,List.all_cons,List.all_nil,
    mode_checked_j5_m56,Bool.and_self]
theorem block_mass_checked_j5_b55 : blockMassCheck bflatBlockJ5B55 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
