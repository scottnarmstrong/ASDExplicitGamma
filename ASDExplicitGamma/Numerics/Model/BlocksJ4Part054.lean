module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B54 : ModeBlockData :=
  ⟨⟨54, 55, (33327260145614765073/5000000000000000000000 : ℚ), (65659410621556883/2000000000000000000000 : ℚ)⟩, [
    (54, modeDataJ4M55)], (13330904058245906029/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b54 : entryChecks 4 bflatBlockJ4B54.entries = true := by
  simp only [entryChecks,bflatBlockJ4B54,List.all_cons,List.all_nil,
    mode_checked_j4_m55,Bool.and_self]
theorem block_mass_checked_j4_b54 : blockMassCheck bflatBlockJ4B54 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
