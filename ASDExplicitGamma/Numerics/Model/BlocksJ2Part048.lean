module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B48 : ModeBlockData :=
  ⟨⟨48, 49, (546765795603091417/2500000000000000000000 : ℚ), (897542550399387737/5000000000000000000000 : ℚ)⟩, [
    (48, modeDataJ2M49)], (2187063182412365667/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b48 : entryChecks 2 bflatBlockJ2B48.entries = true := by
  simp only [entryChecks,bflatBlockJ2B48,List.all_cons,List.all_nil,
    mode_checked_j2_m49,Bool.and_self]
theorem block_mass_checked_j2_b48 : blockMassCheck bflatBlockJ2B48 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
