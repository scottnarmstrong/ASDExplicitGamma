module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part008

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B92 : ModeBlockData :=
  ⟨⟨130, 133, (1054217286789893267/10000000000000000000000 : ℚ), (754385614702025737/10000000000000000000000 : ℚ)⟩, [
    (130, modeDataJ3M131),
    (131, modeDataJ3M132),
    (132, modeDataJ3M133)], (65888580424368329/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b92 : entryChecks 3 bflatBlockJ3B92.entries = true := by
  simp only [entryChecks,bflatBlockJ3B92,List.all_cons,List.all_nil,
    mode_checked_j3_m131,
    mode_checked_j3_m132,
    mode_checked_j3_m133,Bool.and_self]
theorem block_mass_checked_j3_b92 : blockMassCheck bflatBlockJ3B92 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
