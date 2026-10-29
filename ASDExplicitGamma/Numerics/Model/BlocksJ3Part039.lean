module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B39 : ModeBlockData :=
  ⟨⟨39, 40, (24599628807103717417/2000000000000000000000 : ℚ), (1100569892070069187/5000000000000000000000 : ℚ)⟩, [
    (39, modeDataJ3M40)], (30749536008879646771/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b39 : entryChecks 3 bflatBlockJ3B39.entries = true := by
  simp only [entryChecks,bflatBlockJ3B39,List.all_cons,List.all_nil,
    mode_checked_j3_m40,Bool.and_self]
theorem block_mass_checked_j3_b39 : blockMassCheck bflatBlockJ3B39 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
