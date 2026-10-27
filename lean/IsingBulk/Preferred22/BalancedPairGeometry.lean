import IsingBulk.Preferred22.ContourBumpJets
import IsingBulk.Preferred22.ContourLegality
import IsingBulk.Preferred22.Transport
import Mathlib.Analysis.Calculus.MeanValue

/-! The collective denominator on the literal balanced contour. Smooth
periodic bump functions supply the pairwise displacement bound uniformly in
particle count; the small-slope hypothesis is proved, not assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem periodic_bump_bound_and_lipschitz (p : ℝ → ℝ) (hp : ContDiff ℝ ∞ p)
    (hper : Function.Periodic p (2*Real.pi)) :
    ∃ B : ℝ, 0<B ∧ (∀ x, |p x|≤B) ∧
      (∀ x y, |p x-p y|≤B*|x-y|) := by
  obtain ⟨B,hB,hjets⟩ := bump_finite_jets p hp hper 1
  have hd (x : ℝ) : ‖deriv p x‖≤B := by
    rw [norm_deriv_eq_norm_fderiv]
    simpa only [norm_iteratedFDeriv_one] using hjets 1 (by omega) x
  have hLip : LipschitzWith ⟨B,hB.le⟩ p :=
    lipschitzWith_of_nnnorm_deriv_le (hp.differentiable (by simp)) (fun x => by
      exact_mod_cast hd x)
  refine ⟨B,hB,?_,?_⟩
  · intro x
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hjets 0 (by omega) x
  · intro x y
    have hh := hLip.dist_le_mul x y
    change dist (p x) (p y) ≤ B * dist x y at hh
    simpa only [Real.dist_eq] using hh

theorem normalizedOccupancy_abs_le {N : ℕ} (hN : 0<N) (p : ℝ → ℝ)
    (θ : Fin N → ℝ) (B : ℝ) (hp : ∀ x, |p x|≤B) :
    |normalizedOccupancy p θ|≤B := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  rw [normalizedOccupancy, abs_div, abs_of_nonneg hn.le]
  apply (div_le_iff₀ hn).mpr
  unfold occupancy
  calc
    _ ≤ ∑ i, |p (θ i)| := by simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ (fun i => p (θ i))
    _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum (fun i _ => hp (θ i))
    _ = B*N := by simp [mul_comm]

theorem balancedShift_pair_bound {N : ℕ} (hN : 0<N) (τ : ℝ)
    (p m : ℝ → ℝ) (θ : Fin N → ℝ) (Bp Bm : ℝ) (hBp : 0≤Bp) (hBm : 0≤Bm)
    (hp : ∀ x, |p x|≤Bp) (hm : ∀ x, |m x|≤Bm)
    (hpL : ∀ x y, |p x-p y|≤Bp*|x-y|)
    (hmL : ∀ x y, |m x-m y|≤Bm*|x-y|) (i j : Fin N) :
    |balancedShift τ p m θ i-balancedShift τ p m θ j| ≤
      2*|τ| * Bp*Bm*|θ i-θ j| := by
  have he : balancedShift τ p m θ i-balancedShift τ p m θ j =
      τ*(normalizedOccupancy p θ*(m (θ i)-m (θ j))-
        normalizedOccupancy m θ*(p (θ i)-p (θ j))) := by
    unfold balancedShift normalizedOccupancy
    ring
  rw [he, abs_mul]
  calc
    _ ≤ |τ| * (|normalizedOccupancy p θ| * |m (θ i)-m (θ j)|+
        |normalizedOccupancy m θ| * |p (θ i)-p (θ j)|) := by
      gcongr
      simpa only [abs_mul] using abs_sub
        (normalizedOccupancy p θ*(m (θ i)-m (θ j)))
        (normalizedOccupancy m θ*(p (θ i)-p (θ j)))
    _ ≤ |τ| * (Bp*(Bm*|θ i-θ j|)+Bm*(Bp*|θ i-θ j|)) := by
      gcongr
      · exact normalizedOccupancy_abs_le hN p θ Bp hp
      · exact hmL _ _
      · exact normalizedOccupancy_abs_le hN m θ Bm hm
      · exact hpL _ _
    _ = _ := by ring

/-- The same displacement threshold works for every N and every angular
configuration. There is no physical radial parameter in this estimate. -/
theorem balancedShift_pair_uniform (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi)) :
    ∃ τ₀ : ℝ, 0<τ₀ ∧ ∀ τ : ℝ, 0≤τ → τ≤τ₀ →
      ∀ N : ℕ, 0<N → ∀ (θ : Fin N → ℝ) (i j : Fin N),
        (balancedShift τ p m θ i-balancedShift τ p m θ j)^2 ≤
          (1/4:ℝ)*(θ i-θ j)^2 := by
  obtain ⟨Bp,hBp,hpb,hpL⟩ := periodic_bump_bound_and_lipschitz p hp hpp
  obtain ⟨Bm,hBm,hmb,hmL⟩ := periodic_bump_bound_and_lipschitz m hm hmp
  refine ⟨1/(4*Bp*Bm),by positivity,?_⟩
  intro τ hτ hτmax N hN θ i j
  have hsmall : 2*τ*Bp*Bm≤(1/2:ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0<4*Bp*Bm)).mp hτmax
    nlinarith
  have hh := balancedShift_pair_bound hN τ p m θ Bp Bm hBp.le hBm.le hpb hmb hpL hmL i j
  rw [abs_of_nonneg hτ] at hh
  have hh' : |balancedShift τ p m θ i-balancedShift τ p m θ j| ≤
      (1/2:ℝ) * |θ i-θ j| := by
    exact hh.trans (mul_le_mul_of_nonneg_right hsmall (abs_nonneg (θ i-θ j)))
  have hs := pow_le_pow_left₀ (abs_nonneg _) hh' 2
  simpa only [mul_pow, sq_abs, show (1/2:ℝ)^2=1/4 by norm_num] using hs

/-- Actual LT22 denominator coercivity, including full pair-square control,
with constants fixed before N and before the radial approach. -/
theorem balanced_collective_geometry (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi)) :
    ∃ τ₀ : ℝ, 0<τ₀ ∧ ∀ τ : ℝ, 0≤τ → τ≤τ₀ →
      ∀ N : ℕ, 0<N → ∀ θ : Fin N → ℝ,
        (∀ i j, (3/8:ℝ)*(θ i-θ j)^2 ≤
          ‖collectiveDenominator (deformedAngles τ p m θ)‖) ∧
        ((∑ i, ∑ j, ‖deformedAngles τ p m θ i-deformedAngles τ p m θ j‖^2) ≤
          (10/3:ℝ)*‖collectiveDenominator (deformedAngles τ p m θ)‖) ∧
        (∀ i j, θ i≠θ j → collectiveDenominator (deformedAngles τ p m θ)≠0) := by
  obtain ⟨τ₀,hτ₀,hpair⟩ := balancedShift_pair_uniform p m hp hm hpp hmp
  refine ⟨τ₀,hτ₀,?_⟩
  intro τ hτ hτmax N hN θ
  have hpair' (i j : Fin N) :
      (balancedShift τ p m θ i-balancedShift τ p m θ j)^2 ≤
        (1/2:ℝ)^2*(θ i-θ j)^2 := by
    simpa only [show (1/2:ℝ)^2=1/4 by norm_num] using hpair τ hτ hτmax N hN θ i j
  have hd : displacedAngles θ (balancedShift τ p m θ)=deformedAngles τ p m θ := rfl
  refine ⟨?_,?_,?_⟩
  · intro i j
    simpa only [hd,show ((1-(1/2:ℝ)^2)/2)=3/8 by norm_num] using
      collectiveDenominator_norm_lower θ (balancedShift τ p m θ) (1/2) (by norm_num) hpair' i j
  · have hh := collectiveDenominator_pair_norm_control θ (balancedShift τ p m θ)
      (1/2) (by norm_num) hpair'
    rw [hd] at hh
    norm_num at hh
    nlinarith
  · intro i j hij
    rw [←hd]
    exact collectiveDenominator_ne_zero θ (balancedShift τ p m θ) (1/2)
      (by norm_num) hpair' i j hij

/-- The literal angular diameter controls the same collective denominator;
the estimate is valid even at coincident configurations. -/
theorem collective_diameter_of_pair_bound {N : ℕ} (θ : Fin N → ℝ)
    (u : Fin N → ℂ)
    (hp : ∀ i j, (3/8:ℝ)*(θ i-θ j)^2 ≤ ‖collectiveDenominator u‖) :
    (3/8:ℝ)*(preferredAngularDiameter θ)^2 ≤ ‖collectiveDenominator u‖ := by
  have hd : preferredAngularDiameter θ ≤
      Real.sqrt ((8/3:ℝ)*‖collectiveDenominator u‖) := by
    apply Metric.diam_le_of_forall_dist_le (Real.sqrt_nonneg _)
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    rw [Real.dist_eq]
    apply Real.abs_le_sqrt
    have hh := hp i j
    nlinarith
  have hs := pow_le_pow_left₀ (Metric.diam_nonneg (s:=Set.range θ)) hd 2
  rw [Real.sq_sqrt (by positivity)] at hs
  change (preferredAngularDiameter θ)^2 ≤ (8/3:ℝ)*‖collectiveDenominator u‖ at hs
  nlinarith

theorem balanced_collective_diameter_geometry (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi)) :
    ∃ τ₀ : ℝ, 0<τ₀ ∧ ∀ τ : ℝ, 0≤τ → τ≤τ₀ →
      ∀ N : ℕ, 0<N → ∀ θ : Fin N → ℝ,
        (3/8:ℝ)*(preferredAngularDiameter θ)^2 ≤
          ‖collectiveDenominator (deformedAngles τ p m θ)‖ ∧
        (∑ i, ∑ j, ‖deformedAngles τ p m θ i-deformedAngles τ p m θ j‖^2) ≤
          (10/3:ℝ)*‖collectiveDenominator (deformedAngles τ p m θ)‖ ∧
        (0<preferredAngularDiameter θ → collectiveDenominator (deformedAngles τ p m θ)≠0) := by
  obtain ⟨τ₀,hτ₀,hgeom⟩ := balanced_collective_geometry p m hp hm hpp hmp
  refine ⟨τ₀,hτ₀,?_⟩
  intro τ hτ hτmax N hN θ
  obtain ⟨hpairs,hsum,_⟩ := hgeom τ hτ hτmax N hN θ
  have hd := collective_diameter_of_pair_bound θ _ hpairs
  refine ⟨hd,hsum,?_⟩
  intro hdiam hzero
  rw [hzero,norm_zero] at hd
  nlinarith [sq_pos_of_pos hdiam]

/-- At the actual balanced source coordinates, the collective U-values are
exactly the deformed angles throughout the entire one-sided chart. -/
theorem preferred_balanced_source_inverse {N : ℕ} (p m : ℝ → ℝ)
    (τ δ : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2) (hτ : 0≤τ)
    (hS : 0<(temperatureTrace s).re) (hSi : 0<(temperatureTrace s).im)
    (hSδ : (temperatureTrace s).re<2*Real.cos δ)
    (hθ : ∀ i, θ i ∈ Set.Icc (-Real.pi-δ) δ)
    (hp0 : ∀ x, 0≤p x) (hm0 : ∀ x, 0≤m x)
    (hps : ∀ x, Real.sin x≤0 → p x=0) (hms : ∀ x, 0≤Real.sin x → m x=0) :
    (fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i)) =
      deformedAngles τ p m θ := by
  funext i
  have hre : (deformedAngles τ p m θ i).re=θ i := by simp [deformedAngles,Complex.mul_re]
  apply preferred_global_one_sided_inverse s (deformedAngles τ p m θ i) δ hδ hδπ hS hSδ
    (by rw [hre]; exact (hθ i).1) (by rw [hre]; exact (hθ i).2)
  have hh := homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1) p m θ hp0 hm0 hps hms i
  simpa only [complexW_homotopyRoot_eq] using hh

/-- The coercivity used by the literal source residual field. In particular,
its R denominator is proved nonzero at every positive-diameter right point. -/
theorem balanced_source_collective_geometry (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (hpp : Function.Periodic p (2*Real.pi)) (hmp : Function.Periodic m (2*Real.pi)) :
    ∃ τ₀ : ℝ, 0<τ₀ ∧ ∀ τ : ℝ, 0≤τ → τ≤τ₀ →
      ∀ N : ℕ, 0<N → ∀ (θ : Fin N → ℝ) (s : ℂ) (δ : ℝ),
        0<δ → δ<Real.pi/2 → 0<(temperatureTrace s).re → 0<(temperatureTrace s).im →
        (temperatureTrace s).re<2*Real.cos δ →
        (∀ i, θ i ∈ Set.Icc (-Real.pi-δ) δ) →
        (∀ x, 0≤p x) → (∀ x, 0≤m x) →
        (∀ x, Real.sin x≤0 → p x=0) → (∀ x, 0≤Real.sin x → m x=0) →
        let u := fun i => preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i)
        (3/8:ℝ)*(preferredAngularDiameter θ)^2 ≤ ‖collectiveDenominator u‖ ∧
        (∑ i, ∑ j, ‖u i-u j‖^2) ≤ (10/3:ℝ)*‖collectiveDenominator u‖ ∧
        (0<preferredAngularDiameter θ → collectiveDenominator u≠0) := by
  obtain ⟨τ₀,hτ₀,hgeom⟩ := balanced_collective_diameter_geometry p m hp hm hpp hmp
  refine ⟨τ₀,hτ₀,?_⟩
  intro τ hτ hτmax N hN θ s δ hδ hδπ hS hSi hSδ hθ hp0 hm0 hps hms
  have hu := preferred_balanced_source_inverse p m τ δ s θ hδ hδπ hτ hS hSi hSδ hθ hp0 hm0 hps hms
  have hui (i : Fin N) : preferredMovingInverse s (preferredSourceCoordinate τ p m s θ i)=
      deformedAngles τ p m θ i := congrFun hu i
  dsimp only
  simp_rw [hui]
  exact hgeom τ hτ hτmax N hN θ

end
end IsingBulk.Preferred22
