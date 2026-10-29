module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B2 : ModeBlockData :=
  ⟨⟨2, 3, (792435021290086049391/5000000000000000000000 : ℚ), (218147950057422073057/10000000000000000000000 : ℚ)⟩, [
    (2, modeDataJ1M3)], (1584870042580172098781/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b2 : entryChecks 1 bflatBlockJ1B2.entries = true := by
  simp only [entryChecks,bflatBlockJ1B2,List.all_cons,List.all_nil,
    mode_checked_j1_m3,Bool.and_self]
theorem block_mass_checked_j1_b2 : blockMassCheck bflatBlockJ1B2 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
