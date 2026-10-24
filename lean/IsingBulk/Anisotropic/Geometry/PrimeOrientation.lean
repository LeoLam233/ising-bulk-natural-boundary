import IsingBulk.Anisotropic.Geometry.EdgeDerivativeSymmetries
import IsingBulk.Anisotropic.Geometry.RegularPrimeDensity

namespace IsingBulk.Anisotropic
noncomputable section
open Set

theorem abs_lt_one_of_primePhaseCosines {b : ℝ} (hb : b∈primePhaseCosines) : |b|<1 := by
  obtain ⟨p,k,hp,_ho,hk,hkp,rfl⟩ := (mem_primePhaseCosines_iff b).mp hb
  obtain ⟨ha,hb⟩ := primePhase_bounds hp hk hkp
  have hlow := Real.strictAntiOn_cos ⟨ha.le,hb.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ hb
  have hhigh := Real.strictAntiOn_cos ⟨le_rfl,Real.pi_pos.le⟩ ⟨ha.le,hb.le⟩ ha
  apply abs_lt.mpr
  exact ⟨by simpa only [Real.cos_pi] using hlow,by simpa only [Real.cos_zero] using hhigh⟩

theorem endpoint_not_primePhaseCosines {e : ℝ} (he : e=1 ∨ e= -1) : e∉primePhaseCosines := by
  intro hp
  have hh := abs_lt_one_of_primePhaseCosines hp
  rcases he with rfl | rfl <;> norm_num at hh

def OrientedPrimeVEdge (lam : ℝ) (z : ℂ) : Prop :=
  spectralDet lam z≠0 ∧ ∃ e : ℝ, (e=1 ∨ e= -1) ∧ spectralV lam z=e ∧
    |spectralU lam z|<1 ∧ deriv (edgeMapV lam (e:ℂ)) z≠0 ∧
    spectralU lam z∈primePhaseCosines ∧ 0<e*spectralDet lam z

theorem prime_V_or_conjugate {lam : ℝ} {z : ℂ} {e : ℝ}
    (hd : spectralDet lam z≠0) (he : e=1 ∨ e= -1) (hv : spectralV lam z=e)
    (hu : |spectralU lam z|<1) (hder : deriv (edgeMapV lam (e:ℂ)) z≠0)
    (hp : spectralU lam z∈primePhaseCosines) :
    OrientedPrimeVEdge lam z ∨ OrientedPrimeVEdge lam (star z) := by
  by_cases ho : 0<e*spectralDet lam z
  · exact Or.inl ⟨hd,e,he,hv,hu,hder,hp,ho⟩
  · have hen : e≠0 := by rcases he with rfl | rfl <;> norm_num
    have hn : e*spectralDet lam z<0 := lt_of_le_of_ne (le_of_not_gt ho) (mul_ne_zero hen hd)
    right
    refine ⟨by rw [spectralDet_conj]; exact neg_ne_zero.mpr hd,e,he,?_,?_,?_,?_,?_⟩
    · simpa only [spectralV_conj] using hv
    · simpa only [spectralU_conj] using hu
    · rw [edgeMapV_deriv_conj e hd]
      simpa only [star_ne_zero] using hder
    · simpa only [spectralU_conj] using hp
    · rw [spectralDet_conj]
      nlinarith

/-- Every prime regular edge is an oriented V edge after at most one conjugation
and one genuine axis exchange; the coupling ratio remains positive. -/
theorem prime_regular_orientation {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : PrimeRegularEdgePoint lam z) :
    OrientedPrimeVEdge lam z ∨ OrientedPrimeVEdge lam (star z) ∨
    OrientedPrimeVEdge (lam⁻¹) ((lam:ℂ)*z) ∨
    OrientedPrimeVEdge (lam⁻¹) ((lam:ℂ)*star z) := by
  obtain ⟨⟨hd,hU | hV⟩,hprime⟩ := hz
  · obtain ⟨e,he,hu,hv,hder⟩ := hU
    have hp : spectralV lam z∈primePhaseCosines := by
      rcases hprime with hp | hp
      · exact False.elim (endpoint_not_primePhaseCosines he (hu ▸ hp))
      · exact hp
    have hd' : spectralDet (lam⁻¹) ((lam:ℂ)*z)≠0 := by
      rw [spectralDet_axis_exchange hlam.ne']
      exact neg_ne_zero.mpr hd
    have hv' : spectralV (lam⁻¹) ((lam:ℂ)*z)=e := by simpa only [spectralV_axis_exchange hlam.ne'] using hu
    have hu' : |spectralU (lam⁻¹) ((lam:ℂ)*z)|<1 := by simpa only [spectralU_axis_exchange hlam.ne'] using hv
    have hp' : spectralU (lam⁻¹) ((lam:ℂ)*z)∈primePhaseCosines := by
      simpa only [spectralU_axis_exchange hlam.ne'] using hp
    rcases prime_V_or_conjugate hd' he hv' hu'
      (edgeMapV_deriv_axis_nonzero hlam.ne' (e:ℂ) hd hder) hp' with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · right; right; right
      have hs : star ((lam:ℂ)*z)=(lam:ℂ)*star z := by simp
      rw [hs] at h
      exact h
  · obtain ⟨e,he,hv,hu,hder⟩ := hV
    have hp : spectralU lam z∈primePhaseCosines := by
      rcases hprime with hp | hp
      · exact hp
      · exact False.elim (endpoint_not_primePhaseCosines he (hv ▸ hp))
    rcases prime_V_or_conjugate hd he hv hu hder hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end
end IsingBulk.Anisotropic
