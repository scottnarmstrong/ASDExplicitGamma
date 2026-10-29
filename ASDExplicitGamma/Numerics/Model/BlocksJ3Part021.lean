module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B21 : ModeBlockData :=
  ⟨⟨21, 22, (7569870024818499229/400000000000000000000 : ℚ), (713268875844138673/2500000000000000000000 : ℚ)⟩, [
    (21, modeDataJ3M22)], (47311687655115620181/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b21 : entryChecks 3 bflatBlockJ3B21.entries = true := by
  simp only [entryChecks,bflatBlockJ3B21,List.all_cons,List.all_nil,
    mode_checked_j3_m22,Bool.and_self]
theorem block_mass_checked_j3_b21 : blockMassCheck bflatBlockJ3B21 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
