import IsingBulk.Joint.Negative.FamilyFullControl
import IsingBulk.Joint.Negative.FamilyAnalyticControl

/-! # All-particle full-resolvent Cauchy estimates for complex families
Every constant precedes the center, every particle index, and every derivative
order. The input is the actual joint analytic parameter map, not a jet oracle.
-/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
  IsingBulk.Joint.RegularEdges Set Metric
open scoped Topology BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Pullback of the complete odd integrand along an arbitrary jointly analytic
map, with a common polynomial-scale ball in every parameter direction. -/
theorem compact_parametric_odd_integrand_control {b : ℝ} {Q : Set E}
    (H : E → NumeratorParameter) (hb : |b|<1) (hQ : IsCompact Q)
    (hH : ∀ eta∈Q, AnalyticAt ℂ H eta)
    (hzero : ∀ eta∈Q, (H eta).1=0)
    (hB : ∀ eta∈Q, 0<(H eta).2.1.im) (hS : ∀ eta∈Q, (H eta).2.2≠0) :
    ∃ a r C M K : ℝ, 0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ eta∈Q, ∀ n : ℕ, Odd (n+1) → ∀ v : Fin n→ℝ,
      ∀ x∈ball eta (a/((n+1:ℕ):ℝ)^3),
        AnalyticAt ℂ (fun x => independentFullIntegrand b (H x) (negativeShiftedAngles n v)) x ∧
        ‖independentFullIntegrand b (H x) (negativeShiftedAngles n v)‖≤
          K*((n+1:ℕ):ℝ)^2*particleEdgeMajorant r C M (n+1) := by
  have hc : ContinuousOn (fun eta => (H eta).2) Q :=
    fun eta heta => (hH eta heta).continuousAt.snd.continuousWithinAt
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcontrol⟩ :=
    compact_odd_full_integrand_control hb (hQ.image_of_continuousOn hc)
      (by rintro w ⟨eta,heta,rfl⟩; exact hB eta heta)
      (by rintro w ⟨eta,heta,rfl⟩; exact hS eta heta)
  obtain ⟨δ,L,hδ,hL,hlin⟩ := compact_analytic_linear_bound H hQ hH
  refine ⟨min δ (a/L),r,C,M,K,lt_min hδ (div_pos ha hL),hr,hr1,hC,hM,hK,?_⟩
  intro eta heta n hn v x hx
  let N : ℝ := (n+1:ℕ)
  have hN : 1≤N := by dsimp [N]; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hN3 : 1≤N^3 := one_le_pow₀ hN
  have hsmall : min δ (a/L)/N^3≤min δ (a/L) :=
    (div_le_iff₀ (pow_pos hN0 _)).mpr (by nlinarith [lt_min hδ (div_pos ha hL)])
  have hxδ : x∈ball eta δ := ball_subset_ball (hsmall.trans (min_le_left _ _)) hx
  obtain ⟨hHx,hHn⟩ := hlin eta heta x hxδ
  have hHe : H eta=((0:ℂ),(H eta).2) := Prod.ext (hzero eta heta) rfl
  have hHball : H x∈ball ((0:ℂ),(H eta).2) (a/N^3) := by
    rw [mem_ball,dist_eq_norm,←hHe]
    calc
      ‖H x-H eta‖ ≤ L*‖x-eta‖ := hHn
      _ < L*(min δ (a/L)/N^3) := mul_lt_mul_of_pos_left
        (by simpa only [mem_ball,dist_eq_norm] using hx) hL
      _ ≤ L*((a/L)/N^3) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)) hL.le
      _ = a/N^3 := by field_simp
  obtain ⟨hA,hbound⟩ := hcontrol (H eta).2 (mem_image_of_mem _ heta) n hn v (H x) hHball
  exact ⟨hA.comp hHx,hbound⟩

/-- Every full mixed Frechet derivative is controlled, including derivatives in
complex anisotropy parameters. The radius is fixed before the derivative order. -/
theorem compact_parametric_odd_integrand_mixed_cauchy {b : ℝ} {Q : Set E}
    (H : E → NumeratorParameter) (hb : |b|<1) (hQ : IsCompact Q)
    (hH : ∀ eta∈Q, AnalyticAt ℂ H eta)
    (hzero : ∀ eta∈Q, (H eta).1=0)
    (hB : ∀ eta∈Q, 0<(H eta).2.1.im) (hS : ∀ eta∈Q, (H eta).2.2≠0) :
    ∃ a r C M K : ℝ, 0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ eta∈Q, ∀ (j n : ℕ), Odd (n+1) → ∀ v : Fin n→ℝ,
      ∀ x∈ball eta (a/((n+1:ℕ):ℝ)^3),
        ‖iteratedFDeriv ℂ j
          (fun x => independentFullIntegrand b (H x) (negativeShiftedAngles n v)) x‖≤
          (K*((n+1:ℕ):ℝ)^2*particleEdgeMajorant r C M (n+1))/
            (a/(((j+1:ℕ):ℝ)*((n+1:ℕ):ℝ)^3))^j := by
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcontrol⟩ :=
    compact_parametric_odd_integrand_control H hb hQ hH hzero hB hS
  refine ⟨a/2,r,C,M,K,half_pos ha,hr,hr1,hC,hM,hK,?_⟩
  intro eta heta j n hn v x hx
  have hrad : 0<a/((n+1:ℕ):ℝ)^3 := by positivity
  have hx' : x∈ball eta ((a/((n+1:ℕ):ℝ)^3)/2) := by
    convert hx using 1
    congr 1
    ring
  have hh := norm_iteratedFDeriv_le_on_half_ball j hrad
    (show 0≤K*((n+1:ℕ):ℝ)^2*particleEdgeMajorant r C M (n+1) from
      mul_nonneg (by positivity) (particleEdgeMajorant_nonneg hr.le hC.le hM.le _))
    (fun x hx => (hcontrol eta heta n hn v x hx).1)
    (fun x hx => (hcontrol eta heta n hn v x hx).2) hx'
  convert hh using 1
  congr 1
  ring

/-- Scalar transverse Cauchy estimates, retaining the sharp factorial. All
constants still precede the entire compact complex parameter family. -/
theorem compact_family_odd_integrand_cauchy {b : ℝ} {Q : Set E}
    (H : ℂ × E → NumeratorParameter) (hb : |b|<1) (hQ : IsCompact Q)
    (hH : ∀ eta∈Q, AnalyticAt ℂ H (0,eta))
    (hzero : ∀ eta∈Q, (H (0,eta)).1=0)
    (hB : ∀ eta∈Q, 0<(H (0,eta)).2.1.im) (hS : ∀ eta∈Q, (H (0,eta)).2.2≠0) :
    ∃ a r C M K : ℝ, 0<a ∧ 0<r ∧ r<1 ∧ 0<C ∧ 0<M ∧ 0<K ∧
      ∀ eta∈Q, ∀ (j n : ℕ), Odd (n+1) → ∀ v : Fin n→ℝ,
      ∀ u : ℂ, ‖u‖<a/((n+1:ℕ):ℝ)^3 →
        ‖iteratedDeriv j
          (fun t => independentFullIntegrand b (H (t,eta)) (negativeShiftedAngles n v)) u‖≤
          (j.factorial:ℝ)*(K*((n+1:ℕ):ℝ)^2*particleEdgeMajorant r C M (n+1))/
            (a/((n+1:ℕ):ℝ)^3)^j := by
  let Z : E → ℂ × E := fun eta => (0,eta)
  have hZ : Continuous Z := continuous_const.prodMk continuous_id
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,hK,hcontrol⟩ :=
    compact_parametric_odd_integrand_control H hb (hQ.image hZ)
      (by rintro z ⟨eta,heta,rfl⟩; exact hH eta heta)
      (by rintro z ⟨eta,heta,rfl⟩; exact hzero eta heta)
      (by rintro z ⟨eta,heta,rfl⟩; exact hB eta heta)
      (by rintro z ⟨eta,heta,rfl⟩; exact hS eta heta)
  have hcontrol' : ∀ eta∈Q, ∀ n : ℕ, Odd (n+1) → ∀ v : Fin n→ℝ,
      ∀ u : ℂ, ‖u‖<a/((n+1:ℕ):ℝ)^3 →
      AnalyticAt ℂ (fun t => independentFullIntegrand b (H (t,eta)) (negativeShiftedAngles n v)) u ∧
      ‖independentFullIntegrand b (H (u,eta)) (negativeShiftedAngles n v)‖≤
        K*((n+1:ℕ):ℝ)^2*particleEdgeMajorant r C M (n+1) := by
    intro eta heta n hn v u hu
    have hh := hcontrol (0,eta) (mem_image_of_mem Z heta) n hn v (u,eta)
      (by simpa only [mem_ball,Prod.dist_eq,dist_zero_right,dist_self,max_eq_left (norm_nonneg u)] using hu)
    exact ⟨hh.1.comp (f := fun t : ℂ => (t,eta)) (analyticAt_id.prod analyticAt_const),hh.2⟩
  refine ⟨a/3,r,C,M,K,by positivity,hr,hr1,hC,hM,hK,?_⟩
  intro eta heta j n hn v u hu
  let R : ℝ := (a/3)/((n+1:ℕ):ℝ)^3
  have hR : 0<R := by dsimp [R]; positivity
  have hbig : a/((n+1:ℕ):ℝ)^3=3*R := by dsimp [R]; ring
  have hsub : closedBall u R⊆ball 0 (a/((n+1:ℕ):ℝ)^3) := by
    intro w hw
    have hwu : ‖w-u‖≤R := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have htri := norm_add_le (w-u) u
    rw [sub_add_cancel] at htri
    change dist w 0<a/((n+1:ℕ):ℝ)^3
    rw [dist_zero_right,hbig]
    change ‖u‖<R at hu
    linarith
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR
  · apply DifferentiableOn.diffContOnCl_ball
      (U := ball 0 (a/((n+1:ℕ):ℝ)^3)) _ hsub
    intro w hw
    exact (hcontrol' eta heta n hn v w
      (by simpa only [mem_ball,dist_zero_right] using hw)).1.differentiableAt.differentiableWithinAt
  · intro w hw
    exact (hcontrol' eta heta n hn v w
      (by simpa only [mem_ball,dist_zero_right] using hsub (sphere_subset_closedBall hw))).2

end
end IsingBulk.Joint.Negative
