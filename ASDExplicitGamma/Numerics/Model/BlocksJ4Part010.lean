module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B10 : ModeBlockData :=
  ⟨⟨10, 11, (75280843169974392187/10000000000000000000000 : ℚ), (354496511200935409/10000000000000000000000 : ℚ)⟩, [
    (10, modeDataJ4M11)], (37640421584987196093/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b10 : entryChecks 4 bflatBlockJ4B10.entries = true := by
  simp only [entryChecks,bflatBlockJ4B10,List.all_cons,List.all_nil,
    mode_checked_j4_m11,Bool.and_self]
theorem block_mass_checked_j4_b10 : blockMassCheck bflatBlockJ4B10 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
