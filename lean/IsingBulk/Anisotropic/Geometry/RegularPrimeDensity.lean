import IsingBulk.Anisotropic.Geometry.RegularFrontierChart
import IsingBulk.Anisotropic.Geometry.PrimePhases

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology
open Set Filter Metric

/-- Prime phases are dense in the real diameter of an actual local inverse chart. -/
theorem real_chart_prime_density {E : OpenPartialHomeomorph ℂ ℂ} {z : ℂ} {b c : ℝ}
    (hz : z∈E.source) (hEz : E z=((c*b:ℝ):ℂ)) (hb : |b|<1)
    {r : ℝ} (hr : 0<r) (hball : ball (E z) r⊆E.target) {B : Set ℂ}
    (hB : ∀ w∈ball (E z) r, w.im=0 → E.symm w∈B)
    {Q : ℂ→ℝ→Prop}
    (hQ : ∀ᶠ w in 𝓝 z, ∀ t : ℝ, |t|<1 → E w=((c*t:ℝ):ℂ) → Q w t) :
    z∈closure {w | w∈B ∧ ∃ t∈primePhaseCosines, Q w t} := by
  let g : ℝ→ℂ := fun t => E.symm ((c*t:ℝ):ℂ)
  have hct : Continuous (fun t : ℝ => ((c*t:ℝ):ℂ)) := by fun_prop
  have hg : Tendsto g (𝓝 b) (𝓝 z) := by
    exact (E.tendsto_symm hz).comp (by rw [hEz]; exact hct.continuousAt)
  have hgb : ∀ᶠ t in 𝓝 b, ((c*t:ℝ):ℂ)∈ball (E z) r :=
    hct.continuousAt.preimage_mem_nhds (by rw [←hEz]; exact ball_mem_nhds _ hr)
  have hti : ∀ᶠ t in 𝓝 b, |t|<1 := continuousAt_id.abs.eventually_lt_const hb
  have hgQ := hg.eventually hQ
  have hgood : ∀ᶠ t in 𝓝 b, g t∈B ∧ Q (g t) t := by
    filter_upwards [hgb,hti,hgQ] with t ht hi hq
    exact ⟨hB _ ht (Complex.ofReal_im _),hq t hi (E.right_inv (hball ht))⟩
  have hbD := interior_subset_closure_primePhaseCosines (show b∈Ioo (-1:ℝ) 1 from abs_lt.mp hb)
  rw [mem_closure_iff_nhds]
  intro N hN
  obtain ⟨t,ht,htD⟩ := mem_closure_iff_nhds.mp hbD _ (inter_mem (hg hN) hgood)
  exact ⟨g t,ht.1,ht.2.1,t,htD,ht.2.2⟩

def PrimeRegularEdgePoint (lam : ℝ) (z : ℂ) : Prop :=
  RegularEdgePoint lam z ∧ (spectralU lam z∈primePhaseCosines ∨ spectralV lam z∈primePhaseCosines)

theorem coordinates_of_edgeMapU_real {lam e t : ℝ} {z : ℂ}
    (hd : spectralDet lam z≠0) (h : edgeMapU lam (e:ℂ) z=(t:ℂ)) :
    spectralU lam z=e ∧ spectralV lam z=t := by
  have ha := (div_eq_iff (spectralT_ne_zero_of_det_ne_zero hd)).mp h
  have heq : spectralS z*(spectralU lam z:ℂ)+spectralT lam z*(spectralV lam z:ℂ)=
      spectralS z*(e:ℂ)+spectralT lam z*(t:ℂ) := by
    rw [←spectral_reconstruction hd]
    unfold edgeMapU at h
    linear_combination ha
  exact real_coordinates_injective _ _ hd _ _ _ _ heq

theorem coordinates_of_edgeMapV_real {lam e t : ℝ} {z : ℂ}
    (hd : spectralDet lam z≠0) (h : edgeMapV lam (e:ℂ) z=(t:ℂ)) :
    spectralV lam z=e ∧ spectralU lam z=t := by
  have ha := (div_eq_iff (spectralS_ne_zero_of_det_ne_zero hd)).mp h
  have heq : spectralS z*(spectralU lam z:ℂ)+spectralT lam z*(spectralV lam z:ℂ)=
      spectralS z*(t:ℂ)+spectralT lam z*(e:ℂ) := by
    rw [←spectral_reconstruction hd]
    unfold edgeMapV at h
    linear_combination ha
  exact (real_coordinates_injective _ _ hd _ _ _ _ heq).symm



theorem regular_U_frontier_mem_closure_prime {lam : ℝ} {z : ℂ} (a : ℂ) {e : ℝ}
    (hz : z∈frontier (connectedComponentIn (spectralSet lam)ᶜ a))
    (hd : spectralDet lam z≠0) (he : e=1 ∨ e= -1) (hu : spectralU lam z=e)
    (hv : |spectralV lam z|<1) (hder : deriv (edgeMapU lam (e:ℂ)) z≠0) :
    z∈closure {w | w∈frontier (connectedComponentIn (spectralSet lam)ᶜ a) ∧ PrimeRegularEdgePoint lam w} := by
  obtain ⟨E,hE,hzE,r,hr,hball,hfront⟩ := actual_U_same_component_frontier_chart a hz hd he hu hv hder
  have hc : ((-e*spectralDet lam z:ℝ):ℂ)≠0 := by
    exact_mod_cast mul_ne_zero (by rcases he with rfl | rfl <;> norm_num) hd
  have hEz : E z=((-e*spectralDet lam z*spectralV lam z:ℝ):ℂ) := by
    simp only [hE,edgeMapU_at_endpoint hd hu,Complex.ofReal_mul]
  have ha := edgeMapU_analyticAt (lam := lam) (e := (e:ℂ)) (spectralT_ne_zero_of_det_ne_zero hd)
  have hQ : ∀ᶠ w in 𝓝 z, ∀ t : ℝ, |t|<1 → E w=((-e*spectralDet lam z*t:ℝ):ℂ) →
      RegularEdgePoint lam w ∧ spectralV lam w=t := by
    filter_upwards [(spectralDet_continuous lam).continuousAt.eventually_ne hd,
      ha.deriv.continuousAt.eventually_ne hder] with w hdw hderw
    intro t ht heq
    have heqw : edgeMapU lam (e:ℂ) w=(t:ℂ) :=
      mul_left_cancel₀ hc (by simpa only [hE,Complex.ofReal_mul] using heq)
    have hcoords := coordinates_of_edgeMapU_real hdw heqw
    exact ⟨⟨hdw,Or.inl ⟨e,he,hcoords.1,by simpa only [hcoords.2] using ht,hderw⟩⟩,hcoords.2⟩
  have hcl := real_chart_prime_density hzE hEz hv hr hball hfront hQ
  apply closure_mono (s := {w | w∈frontier (connectedComponentIn (spectralSet lam)ᶜ a) ∧
    ∃ t∈primePhaseCosines, RegularEdgePoint lam w ∧ spectralV lam w=t}) ?_ hcl
  rintro w ⟨hw,t,ht,hreg,heq⟩
  exact ⟨hw,hreg,Or.inr (heq.symm ▸ ht)⟩


theorem regular_V_frontier_mem_closure_prime {lam : ℝ} {z : ℂ} (a : ℂ) {e : ℝ}
    (hz : z∈frontier (connectedComponentIn (spectralSet lam)ᶜ a))
    (hd : spectralDet lam z≠0) (he : e=1 ∨ e= -1) (hu : spectralV lam z=e)
    (hv : |spectralU lam z|<1) (hder : deriv (edgeMapV lam (e:ℂ)) z≠0) :
    z∈closure {w | w∈frontier (connectedComponentIn (spectralSet lam)ᶜ a) ∧ PrimeRegularEdgePoint lam w} := by
  obtain ⟨E,hE,hzE,r,hr,hball,hfront⟩ := actual_V_same_component_frontier_chart a hz hd he hu hv hder
  have hc : ((e*spectralDet lam z:ℝ):ℂ)≠0 := by
    exact_mod_cast mul_ne_zero (by rcases he with rfl | rfl <;> norm_num) hd
  have hEz : E z=((e*spectralDet lam z*spectralU lam z:ℝ):ℂ) := by
    simp only [hE,edgeMapV_at_endpoint hd hu,Complex.ofReal_mul]
  have ha := edgeMapV_analyticAt (lam := lam) (e := (e:ℂ)) (spectralS_ne_zero_of_det_ne_zero hd)
  have hQ : ∀ᶠ w in 𝓝 z, ∀ t : ℝ, |t|<1 → E w=((e*spectralDet lam z*t:ℝ):ℂ) →
      RegularEdgePoint lam w ∧ spectralU lam w=t := by
    filter_upwards [(spectralDet_continuous lam).continuousAt.eventually_ne hd,
      ha.deriv.continuousAt.eventually_ne hder] with w hdw hderw
    intro t ht heq
    have heqw : edgeMapV lam (e:ℂ) w=(t:ℂ) :=
      mul_left_cancel₀ hc (by simpa only [hE,Complex.ofReal_mul] using heq)
    have hcoords := coordinates_of_edgeMapV_real hdw heqw
    exact ⟨⟨hdw,Or.inr ⟨e,he,hcoords.1,by simpa only [hcoords.2] using ht,hderw⟩⟩,hcoords.2⟩
  have hcl := real_chart_prime_density hzE hEz hv hr hball hfront hQ
  apply closure_mono (s := {w | w∈frontier (connectedComponentIn (spectralSet lam)ᶜ a) ∧
    ∃ t∈primePhaseCosines, RegularEdgePoint lam w ∧ spectralU lam w=t}) ?_ hcl
  rintro w ⟨hw,t,ht,hreg,heq⟩
  exact ⟨hw,hreg,Or.inl (heq.symm ▸ ht)⟩

/-- Primitive odd-prime phases occur densely on every anisotropic component frontier,
with the actual regular-point geometry retained at the approximating points. -/
theorem frontier_spectral_component_subset_closure_prime_regular {lam : ℝ} (hlam : 0<lam)
    (hne : lam≠1) (a : ℂ) :
    frontier (connectedComponentIn (spectralSet lam)ᶜ a) ⊆
      closure {z | z∈frontier (connectedComponentIn (spectralSet lam)ᶜ a) ∧ PrimeRegularEdgePoint lam z} := by
  apply Set.Subset.trans (frontier_spectral_component_subset_closure_regular hlam hne a)
  apply closure_minimal _ isClosed_closure
  rintro z ⟨hz,hd,hreg⟩
  rcases hreg with ⟨e,he,hu,hv,hder⟩ | ⟨e,he,hv,hu,hder⟩
  · exact regular_U_frontier_mem_closure_prime a hz hd he hu hv hder
  · exact regular_V_frontier_mem_closure_prime a hz hd he hv hu hder

end
end IsingBulk.Anisotropic
