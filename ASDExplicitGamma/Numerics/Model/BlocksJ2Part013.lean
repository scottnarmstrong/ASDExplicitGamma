module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B13 : ModeBlockData :=
  ⟨⟨13, 14, (87736885165061132357/2500000000000000000000 : ℚ), (19083868751023015197/10000000000000000000000 : ℚ)⟩, [
    (13, modeDataJ2M14)], (350947540660244529427/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b13 : entryChecks 2 bflatBlockJ2B13.entries = true := by
  simp only [entryChecks,bflatBlockJ2B13,List.all_cons,List.all_nil,
    mode_checked_j2_m14,Bool.and_self]
theorem block_mass_checked_j2_b13 : blockMassCheck bflatBlockJ2B13 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
