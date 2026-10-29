module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B3 : ModeBlockData :=
  ⟨⟨3, 4, (645924656290493073681/10000000000000000000000 : ℚ), (27833942622971853331/10000000000000000000000 : ℚ)⟩, [
    (3, modeDataJ2M4)], (8074058203631163421/125000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b3 : entryChecks 2 bflatBlockJ2B3.entries = true := by
  simp only [entryChecks,bflatBlockJ2B3,List.all_cons,List.all_nil,
    mode_checked_j2_m4,Bool.and_self]
theorem block_mass_checked_j2_b3 : blockMassCheck bflatBlockJ2B3 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
