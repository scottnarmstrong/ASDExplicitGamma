module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B57 : ModeBlockData :=
  ⟨⟨57, 58, (4965944771840643389/2000000000000000000000 : ℚ), (39125239987514111/10000000000000000000000 : ℚ)⟩, [
    (57, modeDataJ5M58)], (1551857741200201059/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b57 : entryChecks 5 bflatBlockJ5B57.entries = true := by
  simp only [entryChecks,bflatBlockJ5B57,List.all_cons,List.all_nil,
    mode_checked_j5_m58,Bool.and_self]
theorem block_mass_checked_j5_b57 : blockMassCheck bflatBlockJ5B57 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
