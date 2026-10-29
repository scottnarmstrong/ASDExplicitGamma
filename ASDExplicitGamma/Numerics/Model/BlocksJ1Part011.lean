module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B11 : ModeBlockData :=
  ⟨⟨11, 12, (10795282181708856001/2500000000000000000000 : ℚ), (6482837002437998151/2000000000000000000000 : ℚ)⟩, [
    (11, modeDataJ1M12)], (43181128726835424003/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b11 : entryChecks 1 bflatBlockJ1B11.entries = true := by
  simp only [entryChecks,bflatBlockJ1B11,List.all_cons,List.all_nil,
    mode_checked_j1_m12,Bool.and_self]
theorem block_mass_checked_j1_b11 : blockMassCheck bflatBlockJ1B11 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
