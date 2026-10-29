module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B61 : ModeBlockData :=
  ⟨⟨61, 62, (571885877359555069/5000000000000000000000 : ℚ), (546614821976855731/5000000000000000000000 : ℚ)⟩, [
    (61, modeDataJ2M62)], (1143771754719110137/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b61 : entryChecks 2 bflatBlockJ2B61.entries = true := by
  simp only [entryChecks,bflatBlockJ2B61,List.all_cons,List.all_nil,
    mode_checked_j2_m62,Bool.and_self]
theorem block_mass_checked_j2_b61 : blockMassCheck bflatBlockJ2B61 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
