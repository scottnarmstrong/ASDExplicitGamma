module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B32 : ModeBlockData :=
  ⟨⟨32, 33, (12546680713764790847/5000000000000000000000 : ℚ), (39388501244548379/10000000000000000000000 : ℚ)⟩, [
    (32, modeDataJ5M33)], (25093361427529581693/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b32 : entryChecks 5 bflatBlockJ5B32.entries = true := by
  simp only [entryChecks,bflatBlockJ5B32,List.all_cons,List.all_nil,
    mode_checked_j5_m33,Bool.and_self]
theorem block_mass_checked_j5_b32 : blockMassCheck bflatBlockJ5B32 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
