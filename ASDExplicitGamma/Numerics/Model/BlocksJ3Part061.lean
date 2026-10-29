module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B61 : ModeBlockData :=
  ⟨⟨61, 62, (48864036323451911661/10000000000000000000000 : ℚ), (1348575132583810847/10000000000000000000000 : ℚ)⟩, [
    (61, modeDataJ3M62)], (2443201816172595583/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b61 : entryChecks 3 bflatBlockJ3B61.entries = true := by
  simp only [entryChecks,bflatBlockJ3B61,List.all_cons,List.all_nil,
    mode_checked_j3_m62,Bool.and_self]
theorem block_mass_checked_j3_b61 : blockMassCheck bflatBlockJ3B61 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
