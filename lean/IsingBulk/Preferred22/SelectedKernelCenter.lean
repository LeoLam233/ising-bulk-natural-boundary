import IsingBulk.Preferred22.SelectedKernelRows
import IsingBulk.Preferred22.SelectedPeriodic

/-! The selected row estimate at the actual radial center. All source
margins, real occupancies, same-branch cancellation, and exceptional-entry
counting are discharged here before the particle number is chosen. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def preferredSelectedAngularRoot {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i)

def preferredSelectedCenterW {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)

def preferredSelectedCenterRoot {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  physicalRoot (preferredSelectedCenterW d B ε τ θ i)

theorem preferred_selected_actual_center_rows (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {γ : ℝ} (hγ : 0<γ)
    (hmargin : ∀ x : ℝ,B.p x≠0 → γ≤Real.sin x) :
    ∃ a C ρ : ℝ,0<a ∧ 0<C ∧ 0<ρ ∧ ρ≤1 ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ρ → 0<τ → τ<ρ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi) Real.pi) →
      preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ≠0 →
      (∀ i j,a*τ/(N:ℝ)≤‖1-preferredSelectedCenterRoot d B ε τ θ i*
        preferredSelectedCenterRoot d B ε τ θ j‖) ∧
      (∀ i,∑ j,‖gaugeKernel (preferredSelectedAngularRoot d B τ θ)
        (preferredSelectedCenterRoot d B ε τ θ) i j‖^2≤C*(N:ℝ)/τ) := by
  obtain ⟨H,ρH,hH,hρH,hHbound⟩ := preferred_selected_opposite_endpoint_gap d B
  obtain ⟨L,ρL,hL,hρL,hLbound⟩ := preferred_selected_same_plateau_angular_gap d B
  obtain ⟨g,ρg,hg,hρg,hgbound⟩ := preferred_selected_regular_source_gap d B
  let E := Real.exp 1
  let R := 3+E
  let K := 2*R+1
  let μ := 1/K
  let η := min 1 (2*H/K)
  let c := 2*(η^2/8)^2*μ
  let a₀ := min (γ/4) (g/(R+1))
  let a := c*a₀/2
  let C₀ := 4*(E*K)^2/L^2+4*E^4*(R+1)/(c*g)+4*E^4/(c*γ)
  let ρ := min 1 (min ρH (min ρL ρg))
  have hE : 0<E := Real.exp_pos _
  have hR : 0<R := by dsimp only [R]; positivity
  have hK : 0<K := by dsimp only [K]; positivity
  have hμ : 0<μ := by dsimp only [μ]; positivity
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hc : 0<c := by dsimp only [c]; positivity
  have ha₀ : 0<a₀ := lt_min (by positivity) (by positivity)
  have ha : 0<a := by dsimp only [a]; positivity
  have hC₀ : 0<C₀ := by dsimp only [C₀]; positivity
  have hρ : 0<ρ := lt_min (by norm_num) (lt_min hρH (lt_min hρL hρg))
  have hρ1 : ρ≤1 := min_le_left _ _
  refine ⟨a,2*C₀,ρ,ha,by positivity,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hθ hw
  have hεs : ε<1 ∧ ε<ρH ∧ ε<ρL ∧ ε<ρg := by simpa only [ρ,lt_min_iff] using hερ
  have hτs : τ<1 ∧ τ<ρH ∧ τ<ρL ∧ τ<ρg := by simpa only [ρ,lt_min_iff] using hτρ
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hscale : τ/(N:ℝ)≤1 := (div_le_one₀ hNr).mpr (by linarith)
  let W := preferredSelectedCenterW d B ε τ θ
  let z := preferredSelectedCenterRoot d B ε τ θ
  let y := preferredSelectedAngularRoot d B τ θ
  obtain ⟨hP,hQ⟩ := actual_occupancy_box hN B θ
  have hWi (i : Fin N) : 0<(W i).im :=
    (mul_pos hε (Real.sin_pos_of_pos_of_lt_pi d.alpha_pos
      (by linarith [d.alpha_lt,Real.pi_pos]))).trans_le
      (preferredActualW_im_lower d B hε.le hτ.le θ i)
  have hoff (i : Fin N) : OffRealSegment (W i) := Or.inl (hWi i).ne'
  have hWR (i : Fin N) : ‖W i‖≤R := by
    exact (norm_sub_le _ _).trans (add_le_add (preferredRadialTrace_norm_bound d hε.le hεs.1.le)
      (preferred_cos_norm_le_exp_one ((preferred_deformedAngles_im_bound hN d B hτ.le θ i).trans hτs.1.le)))
  have hzn (i : Fin N) : z i≠0 := physicalRoot_ne_zero _
  have hzlt (i : Fin N) : ‖z i‖<1 := physicalRoot_inside (hoff i)
  have hziK (i : Fin N) : ‖(z i)⁻¹‖≤K := preferred_physical_root_inverse_bound (hoff i) (hWR i)
  have hzμ (i : Fin N) : μ≤‖z i‖ := preferred_physical_root_lower (hoff i) (hWR i)
  have hzη (i : Fin N) : η≤‖1+z i‖ := by
    have hh := hHbound ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hεs.2.1)
      (by simpa only [abs_of_pos hτ] using hτs.2.1) hP hQ (hθ i)
    rw [←actual_bump_angle d B τ θ i] at hh
    apply preferred_physical_root_plus_lower (hoff i) (hWR i) hH.le hh hη.le
    have hη1 : η≤1 := min_le_left _ _
    have hηH : η≤2*H/K := min_le_right _ _
    change η^2≤2*H/K
    nlinarith
  have hpair (i j : Fin N) : c*(‖W i-1‖+‖W j-1‖)≤‖1-z i*z j‖^2 :=
    preferred_physical_pair_squared_lower (hWi i) (hWi j) hη hμ.le (hzη i) (hzη j) (hzμ i) (hzμ j)
  have hDn (i j : Fin N) : 1-z i*z j≠0 := by
    intro he
    have hp : ‖z i*z j‖<1 := by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hzlt j).le (norm_nonneg _)).trans_lt
        (by simpa only [mul_one] using hzlt i)
    rw [show z i*z j=1 from (sub_eq_zero.mp he).symm,norm_one] at hp
    exact lt_irrefl _ hp
  have hyi (i : Fin N) : ‖y i‖≤E ∧ ‖(y i)⁻¹‖≤E := by
    have hwim := (preferred_deformedAngles_im_bound hN d B hτ.le θ i).trans hτs.1.le
    have hwre : (Complex.I*deformedAngles τ B.p B.m θ i).re=
        -(deformedAngles τ B.p B.m θ i).im := by simp [Complex.mul_re]
    constructor
    · change ‖Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i)‖≤Real.exp 1
      rw [Complex.norm_exp,hwre]
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hwim).1])
    · change ‖(Complex.exp (Complex.I*deformedAngles τ B.p B.m θ i))⁻¹‖≤Real.exp 1
      rw [←Complex.exp_neg,Complex.norm_exp,Complex.neg_re,hwre]
      exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hwim).2])
  have hyn (i : Fin N) : y i≠0 := Complex.exp_ne_zero _
  have hdisp (i : Fin N) : y i+(y i)⁻¹+z i+(z i)⁻¹=2*preferredRadialTrace d ε := by
    have hyt : y i+(y i)⁻¹=2*Complex.cos (deformedAngles τ B.p B.m θ i) := by
      dsimp only [y,preferredSelectedAngularRoot]
      rw [←Complex.exp_neg]
      simpa only [mul_comm Complex.I _,neg_mul] using
        (Complex.two_cos (deformedAngles τ B.p B.m θ i)).symm
    have hzt := physicalRoot_trace (W i)
    change z i+(z i)⁻¹=2*W i at hzt
    dsimp only [W,preferredSelectedCenterW] at hzt
    linear_combination hyt+hzt
  have hreg (i : Fin N) (hp : B.p (θ i)≠1) (hm : B.m (θ i)≠1) : g≤‖(W i)^2-1‖ := by
    have hh := hgbound ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hεs.2.2.2)
      (by simpa only [abs_of_pos hτ] using hτs.2.2.2) hP hQ
      (preferred_selected_nonplateau_regular B (hθ i) hp hm)
    simpa only [W,preferredSelectedCenterW,actual_bump_angle d B τ θ i] using hh
  have hsame (i j : Fin N) (hh : (θ i,θ j)∈preferredSamePlateauPairs d B) : L≤‖1-y i*y j‖ := by
    have hb := hLbound τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i) (θ j)
      (by simpa only [abs_of_pos hτ] using hτs.2.2.1) hP hQ hh
    simpa only [y,preferredSelectedAngularRoot,actual_bump_angle d B τ θ i,
      actual_bump_angle d B τ θ j] using hb
  have him (i : Fin N) : γ*τ/(N:ℝ)*(occupancy B.p θ*B.m (θ i)+occupancy B.m θ*B.p (θ i))≤(W i).im := by
    have h := preferred_actual_selected_im_margin d B hγ.le hmargin hε.le hτ.le θ i
    have he : 0≤ε*Real.sin d.alpha := mul_nonneg hε.le
      (Real.sin_pos_of_pos_of_lt_pi d.alpha_pos (by linarith [d.alpha_lt,Real.pi_pos])).le
    dsimp only [W,preferredSelectedCenterW]
    rw [show γ*τ/(N:ℝ)=γ*(τ/(N:ℝ)) by ring]
    linarith only [h,he]
  obtain ⟨hPsel,hQsel⟩ := preferred_selected_population_support B.p B.m θ hw
  have hpop : 0<occupancy B.p θ+occupancy B.m θ := by linarith
  have hentry := preferred_selected_kernel_occupancy_bound hN d B θ y z W (preferredRadialTrace d ε)
    hE hK hR.le hc hL hg hγ hτ hθ hpop hyn hzn (fun i => (hyi i).1) (fun i => (hyi i).2)
    (fun i => (hzlt i).le) hziK hWR hdisp hDn hpair hreg hsame him
  have hbranch (i : Fin N) : a₀*τ/(N:ℝ)≤‖W i-1‖ := by
    by_cases hip : B.p (θ i)=1 ∨ B.m (θ i)=1
    · have hh := preferred_selected_plateau_margin d B hγ.le hmargin hε.le hτ.le θ hw i hip
      have hnorm := Complex.im_le_norm (W i-1)
      simp only [Complex.sub_im,Complex.one_im,sub_zero] at hnorm
      have haγ : a₀≤γ/4 := min_le_left _ _
      change γ*τ/(4*(N:ℝ))≤(W i).im at hh
      calc
        _ ≤ (γ/4)*τ/(N:ℝ) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right haγ hτ.le) hNr.le
        _ = γ*τ/(4*(N:ℝ)) := by ring
        _ ≤ (W i).im := hh
        _ ≤ _ := hnorm
    · have hi := not_or.mp hip
      have hh := preferred_dispersion_factor_margin (hWR i) (hreg i hi.1 hi.2)
      have ha₀g : a₀≤g/(R+1) := min_le_right _ _
      have hgW : g/(R+1)≤‖W i-1‖ := (div_le_iff₀ (by positivity)).mpr (hh.trans_eq (mul_comm _ _))
      calc
        _ = a₀*(τ/(N:ℝ)) := by ring
        _ ≤ a₀*1 := mul_le_mul_of_nonneg_left hscale ha₀.le
        _ = a₀ := mul_one _
        _ ≤ g/(R+1) := ha₀g
        _ ≤ _ := hgW
  constructor
  · intro i j
    have hupper : ‖1-z i*z j‖≤2 := by
      have hp : ‖z i*z j‖≤1 := by rw [norm_mul]; nlinarith [hzlt i,hzlt j,norm_nonneg (z i),norm_nonneg (z j)]
      exact (norm_sub_le _ _).trans (by simpa only [norm_one] using (by linarith : (1:ℝ)+‖z i*z j‖≤2))
    have hlow := hpair i j
    have hm := mul_le_mul_of_nonneg_left (hbranch i) hc.le
    change a*τ/(N:ℝ)≤‖1-z i*z j‖
    rw [show a*τ/(N:ℝ)=(c*(a₀*τ/(N:ℝ)))/2 by dsimp only [a]; ring]
    nlinarith [norm_nonneg (W j-1),norm_nonneg (1-z i*z j)]
  · exact preferred_occupancy_row_sum (gaugeKernel y z)
      (fun j => B.p (θ j)+B.m (θ j)) hpop hC₀.le hτ hτs.1.le
      (by simp only [occupancy,Finset.sum_add_distrib]) hentry

lemma preferred_selected_angular_root_lift {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (θ : Fin N → ℝ) :
    preferredSelectedAngularRoot d B τ (preferredLiftedAngles 0 θ)=
      preferredSelectedAngularRoot d B τ θ := by
  funext i
  unfold preferredSelectedAngularRoot
  rw [←homotopyRoot_eq_exp_deformedAngles,←homotopyRoot_eq_exp_deformedAngles]
  exact congrFun (preferred_homotopyRoot_lift τ 0 B.p B.m B.periodic B.m_periodic θ) i

lemma preferred_selected_center_root_lift {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (ε τ : ℝ) (θ : Fin N → ℝ) :
    preferredSelectedCenterRoot d B ε τ (preferredLiftedAngles 0 θ)=
      preferredSelectedCenterRoot d B ε τ θ := by
  funext i
  simp only [preferredSelectedCenterRoot,preferredSelectedCenterW,
    preferred_cos_deformed_lift τ 0 B.p B.m B.periodic B.m_periodic]

/-- Periodic transfer includes the unreduced dependent constrained angle.
No angular range hypothesis remains in the actual selected row estimate. -/
theorem preferred_selected_center_rows_all_angles (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {γ : ℝ} (hγ : 0<γ)
    (hmargin : ∀ x : ℝ,B.p x≠0 → γ≤Real.sin x) :
    ∃ a C ρ : ℝ,0<a ∧ 0<C ∧ 0<ρ ∧ ρ≤1 ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ρ → 0<τ → τ<ρ →
      ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ≠0 →
      (∀ i j,a*τ/(N:ℝ)≤‖1-preferredSelectedCenterRoot d B ε τ θ i*
        preferredSelectedCenterRoot d B ε τ θ j‖) ∧
      (∀ i,∑ j,‖gaugeKernel (preferredSelectedAngularRoot d B τ θ)
        (preferredSelectedCenterRoot d B ε τ θ) i j‖^2≤C*(N:ℝ)/τ) := by
  obtain ⟨a,C,ρ,ha,hC,hρ,hρ1,hbound⟩ := preferred_selected_actual_center_rows d B hγ hmargin
  refine ⟨a,C,ρ,ha,hC,hρ,hρ1,?_⟩
  intro N hN ε τ hε hερ hτ hτρ θ hw
  let θ' := preferredLiftedAngles 0 θ
  have hθ (i : Fin N) : θ' i∈Icc (-Real.pi) Real.pi := by
    have h := toIocMod_mem_Ioc (by positivity : 0<2*Real.pi) (-Real.pi-0) (θ i)
    change θ' i∈Ioc (-Real.pi-0) (-Real.pi-0+2*Real.pi) at h
    constructor <;> linarith [h.1,h.2]
  have hw' : preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ'≠0 := by
    simpa only [θ',preferredFullPopulationWeight,preferred_occupancy_lift B.p B.periodic,
      preferred_occupancy_lift B.m B.m_periodic] using hw
  have hb := hbound N hN ε τ hε hερ hτ hτρ θ' hθ hw'
  simpa only [θ',preferred_selected_angular_root_lift,preferred_selected_center_root_lift] using hb

end
end IsingBulk.Preferred22
