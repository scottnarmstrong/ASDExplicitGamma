module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B27 : ModeBlockData :=
  ⟨⟨27, 28, (12564449550604760867/5000000000000000000000 : ℚ), (39423942712481789/10000000000000000000000 : ℚ)⟩, [
    (27, modeDataJ5M28)], (25128899101209521733/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b27 : entryChecks 5 bflatBlockJ5B27.entries = true := by
  simp only [entryChecks,bflatBlockJ5B27,List.all_cons,List.all_nil,
    mode_checked_j5_m28,Bool.and_self]
theorem block_mass_checked_j5_b27 : blockMassCheck bflatBlockJ5B27 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
