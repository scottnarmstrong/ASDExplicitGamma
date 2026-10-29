module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B59 : ModeBlockData :=
  ⟨⟨59, 60, (24802519793781653459/10000000000000000000000 : ℚ), (39098040698123781/10000000000000000000000 : ℚ)⟩, [
    (59, modeDataJ5M60)], (12401259896890826729/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b59 : entryChecks 5 bflatBlockJ5B59.entries = true := by
  simp only [entryChecks,bflatBlockJ5B59,List.all_cons,List.all_nil,
    mode_checked_j5_m60,Bool.and_self]
theorem block_mass_checked_j5_b59 : blockMassCheck bflatBlockJ5B59 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
