module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B39 : ModeBlockData :=
  ⟨⟨39, 40, (17692053585147510673/2500000000000000000000 : ℚ), (170438546922933151/5000000000000000000000 : ℚ)⟩, [
    (39, modeDataJ4M40)], (70768214340590042691/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b39 : entryChecks 4 bflatBlockJ4B39.entries = true := by
  simp only [entryChecks,bflatBlockJ4B39,List.all_cons,List.all_nil,
    mode_checked_j4_m40,Bool.and_self]
theorem block_mass_checked_j4_b39 : blockMassCheck bflatBlockJ4B39 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
