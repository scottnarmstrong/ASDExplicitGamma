module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B49 : ModeBlockData :=
  ⟨⟨49, 50, (2067470974410065381/10000000000000000000000 : ℚ), (68787008384531511/400000000000000000000 : ℚ)⟩, [
    (49, modeDataJ2M50)], (103373548720503269/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b49 : entryChecks 2 bflatBlockJ2B49.entries = true := by
  simp only [entryChecks,bflatBlockJ2B49,List.all_cons,List.all_nil,
    mode_checked_j2_m50,Bool.and_self]
theorem block_mass_checked_j2_b49 : blockMassCheck bflatBlockJ2B49 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
