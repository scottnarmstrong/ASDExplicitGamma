module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B52 : ModeBlockData :=
  ⟨⟨52, 53, (12446903244306553589/5000000000000000000000 : ℚ), (19594643046247531/5000000000000000000000 : ℚ)⟩, [
    (52, modeDataJ5M53)], (24893806488613107177/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b52 : entryChecks 5 bflatBlockJ5B52.entries = true := by
  simp only [entryChecks,bflatBlockJ5B52,List.all_cons,List.all_nil,
    mode_checked_j5_m53,Bool.and_self]
theorem block_mass_checked_j5_b52 : blockMassCheck bflatBlockJ5B52 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
