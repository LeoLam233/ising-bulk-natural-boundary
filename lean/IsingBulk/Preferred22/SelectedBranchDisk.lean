import IsingBulk.Preferred22.SelectedResolvent

/-! The actual true-branch coordinates are protected throughout a uniform
N^(-3) parameter disk on the selected population. This establishes branch
legality on the two genuine plateaux; it does not assert the remaining
whole selected determinant or convolution estimates. -/
namespace IsingBulk.Preferred22
noncomputable section
set_option maxHeartbeats 800000

lemma preferred_temperatureTrace_lipschitz {s t : ℂ}
    (hs : 1≤‖s‖) (ht : (1:ℝ)/2≤‖t‖) :
    ‖temperatureTrace t-temperatureTrace s‖≤3*‖t-s‖ := by
  have hs0 : s≠0 := by intro h; norm_num [h] at hs
  have ht0 : t≠0 := by intro h; norm_num [h] at ht
  have he : temperatureTrace t-temperatureTrace s=(t-s)+(s-t)/(t*s) := by
    unfold temperatureTrace
    field_simp
    ring
  rw [he]
  have hden : 0<‖t‖*‖s‖ := mul_pos (norm_pos_iff.mpr ht0) (norm_pos_iff.mpr hs0)
  have hd : (1:ℝ)/2≤‖t‖*‖s‖ := by
    have h := mul_le_mul ht hs (by norm_num : (0:ℝ)≤1) (norm_nonneg t)
    nlinarith
  have hdiv : ‖t-s‖/(‖t‖*‖s‖)≤2*‖t-s‖ := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg (t-s))]
  calc
    _ ≤ ‖t-s‖+‖(s-t)/(t*s)‖ := norm_add_le _ _
    _ = ‖t-s‖+‖t-s‖/(‖t‖*‖s‖) := by rw [norm_div,norm_mul,norm_sub_rev s t]
    _ ≤ 3*‖t-s‖ := by linarith

/-- Both true-branch plateaux have a quantitative imaginary W margin at
the actual radial point, using the selected population's real occupancies. -/
theorem preferred_selected_plateau_margin {N : ℕ} (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {γ ε τ : ℝ} (hγ : 0≤γ)
    (hmargin : ∀ x : ℝ,B.p x≠0 → γ≤Real.sin x)
    (hε : 0≤ε) (hτ : 0≤τ) (θ : Fin N → ℝ)
    (hw : preferredFullPopulationWeight preferredPopulationCutoff B.p B.m θ≠0)
    (i : Fin N) (hi : B.p (θ i)=1 ∨ B.m (θ i)=1) :
    γ*τ/(4*(N:ℝ))≤
      (preferredRadialTrace d ε-Complex.cos (deformedAngles τ B.p B.m θ i)).im := by
  obtain ⟨hP,hQ⟩ := preferred_selected_population_support B.p B.m θ hw
  have hP0 : 0≤occupancy B.p θ := by linarith
  have hQ0 : 0≤occupancy B.m θ := by linarith
  have hpop : (1:ℝ)/4≤occupancy B.p θ*B.m (θ i)+occupancy B.m θ*B.p (θ i) := by
    rcases hi with hi|hi
    · rw [hi,mul_one]
      have hm : 0≤B.m (θ i) := B.lower_bound (-θ i)
      linarith [mul_nonneg hP0 hm]
    · rw [hi,mul_one]
      linarith [mul_nonneg hQ0 (B.lower_bound (θ i))]
  have hh := mul_le_mul_of_nonneg_left hpop
    (mul_nonneg hγ (div_nonneg hτ (Nat.cast_nonneg N)))
  have hs : 0≤ε*Real.sin d.alpha := mul_nonneg hε
    (Real.sin_pos_of_pos_of_lt_pi d.alpha_pos (by linarith [d.alpha_lt,Real.pi_pos])).le
  have hbound := preferred_actual_selected_im_margin d B hγ hmargin hε hτ θ i
  have he : γ*(τ/(N:ℝ))*(1/4)=γ*τ/(4*(N:ℝ)) := by ring
  rw [he] at hh
  linarith

/-- A genuine N^(-3) complex parameter disk protects the physical upper W
sheet at every selected true-branch coordinate, uniformly in particle count.
The smooth cutoffs are held fixed on the original real angular configuration. -/
theorem preferred_selected_true_branch_disk (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ c : ℝ,0<c ∧ ∀ N : ℕ,0<N → ∀ ε τ : ℝ,
      0≤ε → 0<τ → τ≤1 → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ∀ t : ℂ,‖t-IsingBulk.Branch.radialParameter d.alpha ε‖≤c*τ/(N:ℝ)^3 →
      ∀ i : Fin N,
      ((cappedCanonicalPreferredBump d cap hcap).p (θ i)=1 ∨
        (cappedCanonicalPreferredBump d cap hcap).m (θ i)=1) →
      c*τ/(N:ℝ)≤(temperatureTrace t-Complex.cos
        (deformedAngles τ (cappedCanonicalPreferredBump d cap hcap).p
          (cappedCanonicalPreferredBump d cap hcap).m θ i)).im := by
  let B := cappedCanonicalPreferredBump d cap hcap
  obtain ⟨γ,hγ,hmargin⟩ := cappedCanonicalPreferredBump_sine_margin d hcap
  let c := min (1/4:ℝ) (γ/16)
  have hc : 0<c := lt_min (by norm_num) (by positivity)
  have hc4 : c≤1/4 := min_le_left _ _
  have hcg : c≤γ/16 := min_le_right _ _
  refine ⟨c,hc,?_⟩
  intro N hN ε τ hε hτ hτ1 θ hw t ht i hi
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hpow : (N:ℝ)≤(N:ℝ)^3 := by
    have hsq : 1≤(N:ℝ)^2 := one_le_pow₀ hN1
    nlinarith [mul_le_mul_of_nonneg_left hsq hNr.le]
  have hradius : c*τ/(N:ℝ)^3≤c*τ/(N:ℝ) :=
    div_le_div_of_nonneg_left (mul_nonneg hc.le hτ.le) hNr hpow
  have hradius1 : c*τ/(N:ℝ)≤1/4 := by
    apply (div_le_iff₀ hNr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hτ1 hc.le]
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  have hs : 1≤‖s‖ := by
    have he : ‖s‖=1+ε := by
      simp only [s,IsingBulk.Branch.radialParameter,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        Complex.norm_exp_ofReal_mul_I,abs_of_nonneg (by positivity : 0≤1+ε),mul_one]
    rw [he]
    linarith
  have ht' : ‖t-s‖≤1/4 := ht.trans (hradius.trans hradius1)
  have htNorm : (1:ℝ)/2≤‖t‖ := by
    have hn := norm_sub_norm_le s t
    rw [norm_sub_rev s t] at hn
    linarith
  have htrace := preferred_temperatureTrace_lipschitz hs htNorm
  have him := (abs_le.mp (Complex.abs_im_le_norm (temperatureTrace t-temperatureTrace s))).1
  simp only [Complex.sub_im] at him
  have hmargin' := preferred_selected_plateau_margin d B hγ.le hmargin hε hτ.le θ hw i hi
  have hscale : γ*τ/(4*(N:ℝ))≥4*(c*τ/(N:ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right hcg hτ.le
    have hd := div_le_div_of_nonneg_right hm hNr.le
    calc
      4*(c*τ/(N:ℝ)) ≤ 4*(γ/16*τ/(N:ℝ)) := mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = γ*τ/(4*(N:ℝ)) := by ring
  have hdist := ht.trans hradius
  change c*τ/(N:ℝ)≤(temperatureTrace t).im-
    (Complex.cos (deformedAngles τ B.p B.m θ i)).im
  change γ*τ/(4*(N:ℝ))≤(temperatureTrace s).im-
    (Complex.cos (deformedAngles τ B.p B.m θ i)).im at hmargin'
  linarith

end
end IsingBulk.Preferred22
