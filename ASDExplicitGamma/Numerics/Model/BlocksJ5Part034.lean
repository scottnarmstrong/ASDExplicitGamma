module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B34 : ModeBlockData :=
  ⟨⟨34, 35, (12538764930101830883/5000000000000000000000 : ℚ), (39372709073033301/10000000000000000000000 : ℚ)⟩, [
    (34, modeDataJ5M35)], (5015505972040732353/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b34 : entryChecks 5 bflatBlockJ5B34.entries = true := by
  simp only [entryChecks,bflatBlockJ5B34,List.all_cons,List.all_nil,
    mode_checked_j5_m35,Bool.and_self]
theorem block_mass_checked_j5_b34 : blockMassCheck bflatBlockJ5B34 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
