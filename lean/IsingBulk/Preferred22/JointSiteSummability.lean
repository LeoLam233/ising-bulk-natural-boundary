import IsingBulk.Preferred22.SiteBounds
import IsingBulk.Preferred22.LatticeFourierAssembly

/-! Joint absolute site/particle summability from a genuine common strip
translation of the actual angular coefficient. No physical summability input
and no older boundary-tail theorem are used. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Set MeasureTheory
open scoped BigOperators

def siteTranslation (h : ℝ) (a : ℤ) : ℝ := if 0≤a then h else -h

theorem siteTranslation_abs {h : ℝ} (hh : 0≤h) (a : ℤ) : |siteTranslation h a|=h := by
  unfold siteTranslation
  split_ifs <;> simp [abs_of_nonneg hh]

theorem siteTranslation_product (h : ℝ) (a : ℤ) :
    (a:ℝ)*siteTranslation h a=(a.natAbs:ℝ)*h := by
  have habs : (a.natAbs:ℝ)=|(a:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  rw [habs]
  unfold siteTranslation
  split_ifs with ha
  · rw [abs_of_nonneg (by exact_mod_cast ha)]
  · rw [abs_of_neg (by exact_mod_cast (lt_of_not_ge ha))]
    ring

theorem siteTranslation_exponential_bound {N : ℕ} (hN : 0<N) {h : ℝ}
    (hh : 0≤h) (a : ℤ) :
    Real.exp (-(a:ℝ)*(N:ℝ)*siteTranslation h a)≤(Real.exp (-h))^a.natAbs := by
  have he : -(a:ℝ)*(N:ℝ)*siteTranslation h a=-(a.natAbs:ℝ)*(N:ℝ)*h := by
    calc
      _ = -(N:ℝ)*((a:ℝ)*siteTranslation h a) := by ring
      _ = -(N:ℝ)*((a.natAbs:ℝ)*h) := by rw [siteTranslation_product]
      _ = _ := by ring
  rw [he,← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have ha : (0:ℝ)≤a.natAbs := Nat.cast_nonneg _
  nlinarith [mul_nonneg (mul_nonneg ha hh) (sub_nonneg.mpr hn)]

theorem siteCoefficient_uniform_geometric_bound {N : ℕ} (hN : 0<N)
    {x h q : ℝ} (hh : 0≤h) (hgap : Real.cosh h<x+x⁻¹-1)
    (hq0 : 0≤q) (hq1 : q<1)
    (hz : ∀ w : ℂ,|w.im|≤h → ‖physicalRoot (temperatureTrace (x:ℂ)-cos w)‖≤q)
    (a b : ℤ) :
    ‖siteCoefficient N a b (x:ℂ)‖≤
      (Real.exp 1*(kernelEnvelope q)^2/Real.sqrt N)^N *
        ((Real.exp (-h))^a.natAbs*q^b.natAbs) := by
  let t := siteTranslation h a
  let D := (Real.sqrt N*(kernelEnvelope q)^2)^N
  let L := (Real.exp (-h))^a.natAbs*q^b.natAbs
  have hD : 0≤D := by dsimp [D]; positivity
  have ht : |t|≤h := (siteTranslation_abs hh a).le
  have hp (θ : Fin N → ℝ) :
      ‖complexSiteDensity (x:ℂ) a b (fun i => (θ i:ℂ)+(t:ℂ)*I)‖≤D*L := by
    have hb := complexSiteDensity_shifted_bound hN hq0 hq1 hz a b t ht θ
    have he := siteTranslation_exponential_bound hN hh a
    exact hb.trans (by
      simpa only [D,L,t,mul_assoc] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he hD) (pow_nonneg hq0 b.natAbs)))
  have hvol : volume (angularBox N)<⊤ := by rw [angularBox_volume]; exact ENNReal.ofReal_lt_top
  have hi : ‖∫ θ in angularBox N,
      complexSiteDensity (x:ℂ) a b (fun i => (θ i:ℂ)+(t:ℂ)*I)‖≤D*L*(2*Real.pi)^N := by
    rw [← angularBox_volume_real]
    exact norm_setIntegral_le_of_norm_le_const_ae hvol (Filter.Eventually.of_forall hp)
  have hn : ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^N)⁻¹‖=
      ((N.factorial:ℝ)*(2*Real.pi)^N)⁻¹ := by
    rw [norm_inv,norm_mul,norm_pow]
    norm_num [norm_mul,Complex.norm_real,Real.pi_pos.le]
  rw [actual_site_contour_shift N hh hgap a b t ht,norm_mul,hn]
  calc
    _ ≤ ((N.factorial:ℝ)*(2*Real.pi)^N)⁻¹*(D*L*(2*Real.pi)^N) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (D/(N.factorial:ℝ))*L := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (sqrt_factorial_envelope hN (sq_nonneg _))
      (mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (pow_nonneg hq0 _))

/-- The exact remaining P1 summability obligation is discharged by actual
physical site integrals, with constants chosen before both indices. -/
theorem preferred_joint_site_summability : PreferredJointSiteSummability := by
  intro x hx
  obtain ⟨h,hh,hgap⟩ := real_temperature_strip_exists hx
  obtain ⟨q,hq0,hq1,hq⟩ := real_strip_root_bound hh.le hgap
  let r := Real.exp (-h)
  let B := Real.exp 1*(kernelEnvelope q)^2
  have hr0 : 0≤r := (Real.exp_pos _).le
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsite : Summable (fun ab : ℤ × ℤ => r^ab.1.natAbs*q^ab.2.natAbs) :=
    (twoSided_geometric_norm_summable hr0 hr1).mul_of_nonneg
      (twoSided_geometric_norm_summable hq0.le hq1)
      (fun _ => pow_nonneg hr0 _) (fun _ => pow_nonneg hq0.le _)
  have hN : Summable (fun n : ℕ => (B/Real.sqrt (2*(n+1):ℕ))^(2*(n+1))) := by
    simpa only [one_mul] using even_numerical_envelope_summable 1 B
  have hall := hN.mul_of_nonneg hsite (fun _ => by dsimp [B]; positivity)
    (fun _ => mul_nonneg (pow_nonneg hr0 _) (pow_nonneg hq0.le _))
  apply hall.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  exact siteCoefficient_uniform_geometric_bound (by omega) hh.le hgap hq0.le hq1 hq p.2.1 p.2.2

theorem preferred_lattice_fubini : PreferredLatticeFubiniStatement :=
  latticeFubini_of_joint preferred_joint_site_summability

/-- The full connected physical susceptibility series, in either pure phase,
including the origin and all sites. Only the permitted published real
temperature correlation and magnetization identities occur as premises. -/
theorem preferred_physical_bulk_identification
    (correlation : Bool → ℝ → ℤ → ℤ → ℂ) (M : ℝ → ℂ)
    (hInputs : PublishedPhysicalInputs correlation M) :
    ∀ phase : Bool, ∀ x : ℝ, 1<x →
      Summable (fun ab : ℤ × ℤ => ‖correlation phase x ab.1 ab.2-M x‖) ∧
      connectedLatticeSum (correlation phase) M x=bulkFunction (x:ℂ) := by
  intro phase x hx
  exact ⟨connectedLattice_absolute_of_fubini preferred_lattice_fubini (hInputs.2 phase) hx,
    connectedLatticeSum_eq_bulk_of_fubini preferred_lattice_fubini (hInputs.2 phase) hInputs.1 hx⟩

/-- Conditional only on the selected-point first/finite/tail analytic
obligations. The real physical joint lattice/particle summation is proved. -/
theorem preferredFullTarget_of_selected_obligations
    (hselected : PreferredSelectedAnalyticObligations) : PreferredFullTarget :=
  preferredFullTarget_of_obligations preferred_lattice_fubini hselected

end
end IsingBulk.Preferred22
