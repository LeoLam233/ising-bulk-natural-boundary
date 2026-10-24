import IsingBulk.Anisotropic.Geometry.HighTopology
import IsingBulk.Anisotropic.Geometry.BoundaryProfiles
import IsingBulk.Anisotropic.Final.LocalExtension

namespace IsingBulk.Anisotropic.Controls
noncomputable section
open Set

theorem high_domain_nonempty {lam : ℝ} (hlam : 0<lam) : (omegaH lam).Nonempty :=
  ⟨0,zero_mem_omegaH hlam⟩

theorem low_domain_nonempty (lam : ℝ) : (omegaL lam).Nonempty := by
  refine ⟨((sliceL lam 0+1:ℝ):ℂ),?_⟩
  change sliceL lam (((sliceL lam 0+1:ℝ):ℂ).im)<(((sliceL lam 0+1:ℝ):ℂ).re)
  simp only [Complex.ofReal_im,Complex.ofReal_re]
  linarith

theorem low_boundary_nonempty {lam : ℝ} (hlam : 0<lam) : (frontier (omegaL lam)).Nonempty := by
  refine ⟨((sliceL lam 0:ℝ):ℂ),?_⟩
  rw [mem_frontier_omegaL_iff hlam]
  simp only [Complex.ofReal_re,Complex.ofReal_im]

theorem constant_has_domain_extension (D : Set ℂ) (c z : ℂ) :
    HasDomainExtension D (fun _ => c) z :=
  ⟨univ,isOpen_univ,mem_univ z,(fun _ => c),(fun _ _ => analyticAt_const),(fun _ _ => rfl)⟩

/-- A genuine constant function is rejected by the actual natural-boundary
predicate on the actual nonempty LT frontier. -/
theorem constant_not_low_natural_boundary {lam : ℝ} (hlam : 0<lam) (c : ℂ) :
    ¬NaturalBoundaryOn (omegaL lam) (fun _ => c) := by
  intro h
  obtain ⟨z,hz⟩ := low_boundary_nonempty hlam
  exact h.2 z hz (constant_has_domain_extension (omegaL lam) c z)

example : (omegaH 1).Nonempty := high_domain_nonempty (by norm_num)
example : (omegaH 2).Nonempty := high_domain_nonempty (by norm_num)
example : (omegaL (1/2)).Nonempty := low_domain_nonempty _
example : ¬NaturalBoundaryOn (omegaL 2) (fun _ => (0:ℂ)) :=
  constant_not_low_natural_boundary (by norm_num) 0

end
end IsingBulk.Anisotropic.Controls
