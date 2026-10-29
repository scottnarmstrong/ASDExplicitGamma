module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B12 : ModeBlockData :=
  ⟨⟨12, 13, (15749991257960878883/5000000000000000000000 : ℚ), (13377380197000735717/5000000000000000000000 : ℚ)⟩, [
    (12, modeDataJ1M13)], (6299996503184351553/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b12 : entryChecks 1 bflatBlockJ1B12.entries = true := by
  simp only [entryChecks,bflatBlockJ1B12,List.all_cons,List.all_nil,
    mode_checked_j1_m13,Bool.and_self]
theorem block_mass_checked_j1_b12 : blockMassCheck bflatBlockJ1B12 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
