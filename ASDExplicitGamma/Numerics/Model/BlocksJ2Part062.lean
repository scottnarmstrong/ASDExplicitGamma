module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B62 : ModeBlockData :=
  ⟨⟨62, 63, (110839480176577521/1000000000000000000000 : ℚ), (132181592066597509/1250000000000000000000 : ℚ)⟩, [
    (62, modeDataJ2M63)], (1108394801765775209/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b62 : entryChecks 2 bflatBlockJ2B62.entries = true := by
  simp only [entryChecks,bflatBlockJ2B62,List.all_cons,List.all_nil,
    mode_checked_j2_m63,Bool.and_self]
theorem block_mass_checked_j2_b62 : blockMassCheck bflatBlockJ2B62 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
