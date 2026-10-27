import IsingBulk.Preferred22.ContourPartition
import IsingBulk.Preferred22.PhaseAttenuation
import IsingBulk.Preferred22.BumpChoice

/-! The genuine occupancy-dependent damping of the selected population.
The support margin is proved for the actual capped sine bump. The full
physical phase and the actual coupled deformation are retained throughout.
This is the damping part of Lemma 5.2, not its determinant/integral bound. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem preferred_selected_population_support {N : ℕ} (p m : ℝ → ℝ)
    (θ : Fin N → ℝ)
    (hw : preferredFullPopulationWeight preferredPopulationCutoff p m θ ≠ 0) :
    1/4 < occupancy p θ ∧ 1/4 < occupancy m θ := by
  have hp : preferredPopulationCutoff (occupancy p θ) ≠ 0 := by
    intro hp
    apply hw
    simp [preferredFullPopulationWeight,fullWeight,hp]
  have hm : preferredPopulationCutoff (occupancy m θ) ≠ 0 := by
    intro hm
    apply hw
    simp [preferredFullPopulationWeight,fullWeight,hm]
  exact ⟨lt_of_not_ge (fun h => hp (preferredPopulationCutoff_zero h)),
    lt_of_not_ge (fun h => hm (preferredPopulationCutoff_zero h))⟩

theorem cappedCanonicalPreferredBump_sine_margin (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ γ : ℝ, 0<γ ∧ ∀ θ : ℝ,
      (cappedCanonicalPreferredBump d cap hcap).p θ ≠ 0 → γ ≤ Real.sin θ := by
  let δ := cappedPreferredDelta d cap
  have hδ : 0<δ := (cappedPreferredDelta_bounds d hcap).1
  have hδπ : δ<Real.pi/2 := by
    have h := (cappedPreferredDelta_bounds d hcap).2.2
    dsimp only [δ]
    linarith [(preferredBumpDelta_margins d).2.1,d.alpha_lt,Real.pi_pos]
  refine ⟨Real.sin δ/2,div_pos
    (Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])) (by norm_num),?_⟩
  intro θ hp
  have hm := sineCutoff_sine_margin hδ hδπ hp
  linarith

lemma preferred_sinh_margin {h t : ℝ} (hht : h*t≤0) :
    -h*t ≤ -Real.sinh h*t := by
  by_cases hh : h=0
  · simp [hh]
  by_cases hp : 0<h
  · have ht : t≤0 := by nlinarith
    have hs := Real.self_le_sinh_iff.mpr hp.le
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hs) ht]
  · have hn : h<0 := lt_of_le_of_ne (le_of_not_gt hp) hh
    have ht : 0≤t := by nlinarith
    have hs := Real.sinh_le_self_iff.mpr hn.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) ht]

/-- The imaginary part gains both occupancy contributions at the actual
angular configuration; neither population is replaced by a constant. -/
theorem preferred_actual_selected_im_margin {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {γ ε τ : ℝ} (_hγ : 0≤γ)
    (hmargin : ∀ x : ℝ, B.p x≠0 → γ≤Real.sin x)
    (hε : 0≤ε) (hτ : 0≤τ) (θ : Fin N → ℝ) (i : Fin N) :
    ε*Real.sin d.alpha+γ*(τ/(N:ℝ))*
      (occupancy B.p θ*B.m (θ i)+occupancy B.m θ*B.p (θ i)) ≤
      (preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)).im := by
  have hP : 0≤occupancy B.p θ := Finset.sum_nonneg (fun j _ => B.lower_bound _)
  have hQ : 0≤occupancy B.m θ := Finset.sum_nonneg (fun j _ => B.lower_bound _)
  have hp : γ*B.p (θ i)≤B.p (θ i)*Real.sin (θ i) := by
    by_cases hz : B.p (θ i)=0
    · simp [hz]
    · nlinarith [mul_le_mul_of_nonneg_left (hmargin _ hz) (B.lower_bound (θ i))]
  have hm : γ*B.m (θ i)≤ -(B.m (θ i)*Real.sin (θ i)) := by
    by_cases hz : B.m (θ i)=0
    · simp [hz]
    · have h := mul_le_mul_of_nonneg_left (hmargin (-θ i) hz) (B.lower_bound (-θ i))
      rw [Real.sin_neg] at h
      change B.m (θ i)*γ ≤ B.m (θ i)*(-Real.sin (θ i)) at h
      nlinarith
  have ht : 0≤τ/(N:ℝ) := div_nonneg hτ (Nat.cast_nonneg N)
  have hheight : γ*(τ/(N:ℝ))*
      (occupancy B.p θ*B.m (θ i)+occupancy B.m θ*B.p (θ i)) ≤
      -balancedShift τ B.p B.m θ i*Real.sin (θ i) := by
    have hp' := mul_le_mul_of_nonneg_left hp hQ
    have hm' := mul_le_mul_of_nonneg_left hm hP
    have h := mul_le_mul_of_nonneg_left (add_le_add hm' hp') ht
    dsimp only [balancedShift]
    nlinarith only [h]
  have hs := preferred_sinh_margin
    (balancedShift_sine_nonpos hτ B.p B.m θ B.lower_bound
      (fun x => B.lower_bound (-x)) (fun x hx => B.p_zero_of_sin_nonpos hx)
      (fun x hx => B.m_zero_of_sin_nonneg hx) i)
  have hroot : Complex.exp (((balancedShift τ B.p B.m θ i:ℝ):ℂ)+(θ i:ℂ)*Complex.I)=
      homotopyRoot τ 1 B.p B.m θ i := by
    unfold homotopyRoot
    congr 1
    simp only [Complex.ofReal_one,one_mul]
    ring
  have he := complexW_polar_im (IsingBulk.Branch.radialParameter d.alpha ε)
    (balancedShift τ B.p B.m θ i) (θ i)
  rw [hroot,complexW_homotopyRoot_eq] at he
  change (preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)).im =
    (preferredRadialTrace d ε).im-Real.sinh (balancedShift τ B.p B.m θ i)*Real.sin (θ i) at he
  rw [he]
  linarith [preferredRadialTrace_im_lower d hε]

/-- Exact source damping, with both P and Q retained, uniform in all
particle numbers and in the entire final deformed contour. -/
theorem preferred_actual_occupancy_attenuation {N : ℕ} (hN : 0<N)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {γ ε τ : ℝ}
    (hγ : 0≤γ) (hmargin : ∀ x : ℝ, B.p x≠0 → γ≤Real.sin x)
    (hε : 0<ε) (hε1 : ε≤1) (hτ : 0≤τ) (hτ1 : τ≤1)
    (θ : Fin N → ℝ) :
    ((N:ℝ)*ε*Real.sin d.alpha+2*γ*(τ/(N:ℝ))*occupancy B.p θ*occupancy B.m θ)/
      (7+2*Real.exp 1) ≤ -(preferredTotalPhase d ε τ B.p B.m θ).im := by
  let R := 3+Real.exp 1
  have hsin : 0<Real.sin d.alpha := Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])
  have hpoint (i : Fin N) :
      ε*Real.sin d.alpha+γ*(τ/(N:ℝ))*
        (occupancy B.p θ*B.m (θ i)+occupancy B.m θ*B.p (θ i)) ≤
        (7+2*Real.exp 1)*(-(preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)).im) := by
    let W := preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)
    have hi : 0<W.im := (mul_pos hε hsin).trans_le
      (preferredActualW_im_lower d B hε.le hτ θ i)
    have hn : ‖W‖≤R := (norm_sub_le _ _).trans
      (add_le_add (preferredRadialTrace_norm_bound d hε.le hε1)
        (preferred_cos_norm_le_exp_one
          ((preferred_deformedAngles_im_bound hN d B hτ θ i).trans hτ1)))
    have ha := (preferred_phase_bounds hi hn).2.2
    have hb := preferred_actual_selected_im_margin d B hγ hmargin hε.le hτ θ i
    have hfactor : 2*R+1=7+2*Real.exp 1 := by dsimp only [R]; ring
    rw [hfactor] at ha
    exact hb.trans ha
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
  have him : (preferredTotalPhase d ε τ B.p B.m θ).im =
      ∑ i,(preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)).im :=
    map_sum Complex.imCLM _ _
  rw [him]
  apply (div_le_iff₀ (by positivity : 0<7+2*Real.exp 1)).mpr
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Finset.sum_neg_distrib] at hh
  change ε*((N:ℝ)*Real.sin d.alpha)+γ*(τ/(N:ℝ))*
    (occupancy B.p θ*occupancy B.m θ+occupancy B.m θ*occupancy B.p θ) ≤
    (7+2*Real.exp 1)*(-(∑ i,(preferredAngularPhase d ε (deformedAngles τ B.p B.m θ i)).im)) at hh
  nlinarith only [hh]

/-- The selected weight itself forces the claimed reciprocal-particle
damping gap. The constant is chosen before N, epsilon, tau and the angles. -/
theorem preferred_selected_attenuation_gap (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ c : ℝ, 0<c ∧ ∀ N : ℕ, 0<N → ∀ ε τ : ℝ,
      0<ε → ε≤1 → 0≤τ → τ≤1 → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      c*τ/(N:ℝ) ≤ -(preferredTotalPhase d ε τ
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ).im := by
  let B := cappedCanonicalPreferredBump d cap hcap
  obtain ⟨γ,hγ,hmargin⟩ := cappedCanonicalPreferredBump_sine_margin d hcap
  let D := 7+2*Real.exp 1
  have hD : 0<D := by dsimp only [D]; positivity
  refine ⟨γ/(8*D),by positivity,?_⟩
  intro N hN ε τ hε hε1 hτ hτ1 θ hw
  have hg := preferred_actual_occupancy_attenuation hN d B hγ.le hmargin hε hε1 hτ hτ1 θ
  obtain ⟨hP,hQ⟩ := preferred_selected_population_support B.p B.m θ hw
  have hPQ : (1:ℝ)/16 ≤ occupancy B.p θ*occupancy B.m θ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hP.le) (sub_nonneg.mpr hQ.le)]
  have hcoef : 0≤2*γ*(τ/(N:ℝ)) := by positivity
  have hm := mul_le_mul_of_nonneg_left hPQ hcoef
  have hsin : 0≤Real.sin d.alpha := (Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
    (by linarith [d.alpha_lt,Real.pi_pos])).le
  have hrad : 0≤(N:ℝ)*ε*Real.sin d.alpha := by positivity
  have hlo : γ/(8*D)*τ/(N:ℝ) ≤
      ((N:ℝ)*ε*Real.sin d.alpha+2*γ*(τ/(N:ℝ))*occupancy B.p θ*occupancy B.m θ)/D := by
    apply (le_div_iff₀ hD).mpr
    have hN0 : (N:ℝ)≠0 := by positivity
    have he : γ/(8*D)*τ/(N:ℝ)*D=2*γ*(τ/(N:ℝ))*(1/16) := by
      field_simp
      ring
    rw [he]
    nlinarith only [hm,hrad]
  exact hlo.trans hg

end
end IsingBulk.Preferred22
