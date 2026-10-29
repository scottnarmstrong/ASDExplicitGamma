module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B43 : ModeBlockData :=
  ⟨⟨43, 44, (107666108043313616977/10000000000000000000000 : ℚ), (2039436239958842911/10000000000000000000000 : ℚ)⟩, [
    (43, modeDataJ3M44)], (6729131752707101061/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b43 : entryChecks 3 bflatBlockJ3B43.entries = true := by
  simp only [entryChecks,bflatBlockJ3B43,List.all_cons,List.all_nil,
    mode_checked_j3_m44,Bool.and_self]
theorem block_mass_checked_j3_b43 : blockMassCheck bflatBlockJ3B43 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
