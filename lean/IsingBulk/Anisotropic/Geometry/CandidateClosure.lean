import IsingBulk.Anisotropic.Geometry.ZeroPersistence
import IsingBulk.Anisotropic.Geometry.ClosedSpectralSet

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

def spectralEquation (lam : ℝ) (uv : ℝ × ℝ) (z : ℂ) : ℂ :=
  spectralA lam z-spectralS z*(uv.1:ℂ)-spectralT lam z*(uv.2:ℂ)

def cosineSquare : Set (ℝ × ℝ) := Set.Icc (-1) 1 ×ˢ Set.Icc (-1) 1

def candidateSet (lam : ℝ) (D : Set (ℝ × ℝ)) : Set ℂ :=
  {z | ∃uv∈D,spectralEquation lam uv z=0}

theorem spectralEquation_continuous (lam : ℝ) :
    Continuous (fun pz : (ℝ × ℝ) × ℂ => spectralEquation lam pz.1 pz.2) := by
  unfold spectralEquation spectralA spectralS spectralT
  fun_prop

theorem spectralEquation_differentiable (lam : ℝ) (uv : ℝ × ℝ) :
    Differentiable ℂ (spectralEquation lam uv) := by
  unfold spectralEquation spectralA spectralS spectralT
  fun_prop

@[simp] theorem spectralEquation_zero (lam : ℝ) (uv : ℝ × ℝ) : spectralEquation lam uv 0=1 := by
  simp [spectralEquation,spectralA,spectralS,spectralT]

theorem candidateSet_subset_spectralSet (lam : ℝ) {D : Set (ℝ × ℝ)} (hD : D⊆cosineSquare) :
    candidateSet lam D⊆spectralSet lam := by
  rintro z ⟨uv,huv,he⟩
  refine ⟨uv.1,(hD huv).1,uv.2,(hD huv).2,?_⟩
  unfold spectralEquation at he
  linear_combination he

/-- Any dense allowed parameter grids have exactly the full spectral set as their zero closure.
All multiple roots, endpoints, collinear contacts, and vanishing sinh coefficients are included. -/
theorem closure_candidateSet_eq_spectralSet (lam : ℝ) {D : Set (ℝ × ℝ)}
    (hD : D⊆cosineSquare) (hdense : cosineSquare⊆closure D) :
    closure (candidateSet lam D)=spectralSet lam := by
  apply Set.Subset.antisymm
  · exact closure_minimal (candidateSet_subset_spectralSet lam hD) (spectralSet_isClosed lam)
  · rintro z ⟨u,hu,v,hv,he⟩
    apply mem_closure_iff.mpr
    intro N hN hzN
    have hf : spectralEquation lam (u,v) z=0 := by
      unfold spectralEquation
      linear_combination he
    have hp := eventually_exists_zero_mem_nhds (spectralEquation_continuous lam)
      (spectralEquation_differentiable lam) ⟨0,by simp⟩ hf (hN.mem_nhds hzN)
    have hcl : (u,v)∈closure D := hdense ⟨hu,hv⟩
    rcases (mem_closure_iff_nhds.mp hcl) _ hp with ⟨uv,hzero,huv⟩
    rcases hzero with ⟨w,hwN,hw⟩
    exact ⟨w,hwN,uv,huv,hw⟩

end
end IsingBulk.Anisotropic
