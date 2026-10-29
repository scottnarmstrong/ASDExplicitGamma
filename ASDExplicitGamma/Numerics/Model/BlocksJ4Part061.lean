module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B61 : ModeBlockData :=
  ⟨⟨61, 62, (32194906931375520509/5000000000000000000000 : ℚ), (32129919843806893/1000000000000000000000 : ℚ)⟩, [
    (61, modeDataJ4M62)], (64389813862751041017/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b61 : entryChecks 4 bflatBlockJ4B61.entries = true := by
  simp only [entryChecks,bflatBlockJ4B61,List.all_cons,List.all_nil,
    mode_checked_j4_m62,Bool.and_self]
theorem block_mass_checked_j4_b61 : blockMassCheck bflatBlockJ4B61 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
