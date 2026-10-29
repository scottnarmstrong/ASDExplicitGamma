module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B13 : ModeBlockData :=
  ⟨⟨13, 14, (12786613536134123373/5000000000000000000000 : ℚ), (22575120921904410197/10000000000000000000000 : ℚ)⟩, [
    (13, modeDataJ1M14)], (5114645414453649349/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b13 : entryChecks 1 bflatBlockJ1B13.entries = true := by
  simp only [entryChecks,bflatBlockJ1B13,List.all_cons,List.all_nil,
    mode_checked_j1_m14,Bool.and_self]
theorem block_mass_checked_j1_b13 : blockMassCheck bflatBlockJ1B13 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
