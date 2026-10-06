import IsingBulk.Analysis.JetsPoleCalculus

/-! Kernel freezing in the actual regular coordinates. Derivatives along
(1,Bres) mean fixed-phi parameter derivative plus Bres times spatial
derivatives; the direction is evaluated at the differentiation point. -/
namespace IsingBulk.Jets
noncomputable section
open IsingBulk.Branch
open scoped BigOperators

def regularYProduct {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) : ℂ := ∏ i, regularY s (φ i)
def regularZProduct {N : ℕ} (_s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  Complex.exp (-Complex.I * ∑ i, φ i)
def regularKernel {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  (1-regularYProduct s φ)*(1-regularZProduct s φ)

def regularTransport {N : ℕ} (p q : Fin N) (F : ℂ → (Fin N → ℂ) → ℂ)
    (s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  deriv (fun t : ℂ => F (s+t) (fun i => φ i+t*regularResidualField p q s φ i)) 0

theorem regularY_transport_value (s φ v : ℂ) (hg : regularG s φ ≠ 0)
    (hn : Complex.sin φ ≠ 0) (hd : 1-(regularY s φ)^(-2:ℤ) ≠ 0) :
    2*(sourceSPrime s+Complex.sin φ*(regularB s φ*(regularA s φ-v)))/
      (1-(regularY s φ)^(-2:ℤ)) = -Complex.I*regularY s φ*v := by
  unfold regularA regularB
  have hG : regularG s φ = Complex.I*(regularY s φ-(regularY s φ)⁻¹)/2 := rfl
  simp only [zpow_neg, zpow_ofNat] at hd ⊢
  have hysq : -1+(regularY s φ)^2 ≠ 0 := by
    intro h
    have he : (regularY s φ)^2 = 1 := by linear_combination h
    apply hd
    simp [he]
  field_simp
  rw [hG]
  field_simp [regularY_ne_zero, hysq]
  ring_nf
  field_simp [hysq]
  ring

theorem regularY_component_transport {N : ℕ} (p q i : Fin N) (s : ℂ) (φ : Fin N → ℂ)
    (hs : s ≠ 0) (hslit : 1-(s+s⁻¹-Complex.cos (φ i))^2 ∈ Complex.slitPlane)
    (hd : 1-(regularY s (φ i))^(-2:ℤ) ≠ 0)
    (hg : regularG s (φ i) ≠ 0) (hn : Complex.sin (φ i) ≠ 0) :
    HasDerivAt (fun t : ℂ => regularY (s+t) (φ i+t*regularResidualField p q s φ i))
      (-Complex.I*regularY s (φ i)*regularSelectedField p q s φ i) 0 := by
  have hh := regularY_line_derivative s (φ i) 1 (regularResidualField p q s φ i) hs hslit hd
  have he : regularResidualField p q s φ i =
      regularB s (φ i)*(regularA s (φ i)-regularSelectedField p q s φ i) := by
    unfold regularResidualField residualField regularSelectedField
    ring
  simp only [mul_one, he] at hh
  rw [regularY_transport_value s (φ i) _ hg hn hd] at hh
  simpa only [← he] using hh

theorem regularYProduct_transport {N : ℕ} (p q : Fin N) (s : ℂ) (φ : Fin N → ℂ)
    (hs : s ≠ 0) (hslit : ∀ i, 1-(s+s⁻¹-Complex.cos (φ i))^2 ∈ Complex.slitPlane)
    (hd : ∀ i, 1-(regularY s (φ i))^(-2:ℤ) ≠ 0)
    (hg : ∀ i, regularG s (φ i) ≠ 0) (hn : ∀ i, Complex.sin (φ i) ≠ 0)
    (hpq : regularB s (φ p)-regularB s (φ q) ≠ 0) :
    HasDerivAt (fun t : ℂ => regularYProduct (s+t)
      (fun i => φ i+t*regularResidualField p q s φ i)) 0 0 := by
  have hh := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun i _ => regularY_component_transport p q i s φ hs (hslit i) (hd i) (hg i) (hn i))
  have hsum : (∑ i, (∏ k ∈ Finset.univ.erase i, regularY s (φ k))*
      (-Complex.I*regularY s (φ i)*regularSelectedField p q s φ i)) = 0 := by
    calc
      _ = (-Complex.I*∏ k, regularY s (φ k))*∑ i, regularSelectedField p q s φ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
        ring
      _ = 0 := by rw [show (∑ i, regularSelectedField p q s φ i) = 0 from selectedField_sum _ _ p q hpq]; ring
  convert! hh using 1
  simpa only [zero_mul, add_zero, smul_eq_mul] using hsum.symm

theorem regularZProduct_transport {N : ℕ} (p q : Fin N) (s : ℂ) (φ : Fin N → ℂ) :
    HasDerivAt (fun t : ℂ => regularZProduct (s+t)
      (fun i => φ i+t*regularResidualField p q s φ i)) 0 0 := by
  have hh : HasDerivAt (fun t : ℂ => ∑ i, (φ i+t*regularResidualField p q s φ i))
      (∑ i, regularResidualField p q s φ i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    convert! ((hasDerivAt_id (0:ℂ)).mul_const (regularResidualField p q s φ i)).const_add (φ i) using 1
    simp
  have hz : (∑ i, regularResidualField p q s φ i) = 0 := residualField_sum _ _ p q
  have he := (hh.const_mul (-Complex.I)).cexp
  simpa only [hz, mul_zero, regularZProduct] using he

theorem regularKernel_frozen {N : ℕ} (p q : Fin N) (s : ℂ) (φ : Fin N → ℂ)
    (hs : s ≠ 0) (hslit : ∀ i, 1-(s+s⁻¹-Complex.cos (φ i))^2 ∈ Complex.slitPlane)
    (hd : ∀ i, 1-(regularY s (φ i))^(-2:ℤ) ≠ 0)
    (hg : ∀ i, regularG s (φ i) ≠ 0) (hn : ∀ i, Complex.sin (φ i) ≠ 0)
    (hpq : regularB s (φ p)-regularB s (φ q) ≠ 0) :
    regularTransport p q regularKernel s φ = 0 := by
  have hY := regularYProduct_transport p q s φ hs hslit hd hg hn hpq
  have hZ := regularZProduct_transport p q s φ
  have hh := (hY.const_sub 1).fun_mul (hZ.const_sub 1)
  simpa only [regularTransport, regularKernel, neg_zero, zero_mul, mul_zero, add_zero] using hh.deriv

theorem regularKernel_chart {n : ℕ} (s : ℂ) (v θ : ℝ) (x : IsingBulk.Lie.AngularSpace n)
    (hg : ∀ i, 0 < (angularG v θ (x i)).re) :
    regularKernel s (fun i => chartPhase s v θ (x i)) =
      (1-actualY v θ s x)*(1-actualZ v θ s x) := by
  simp only [regularKernel, regularYProduct, regularY_chartPhase _ _ _ _ (hg _),
    actualY_eq_product, regularZProduct, actualZ]

/-- The line definition is the genuine derivative along the vector (1,B).
It is a local differential operator, not a flow with B held fixed in s. -/
theorem regularTransport_fderiv {N : ℕ} (p q : Fin N)
    (F : ℂ → (Fin N → ℂ) → ℂ) (s : ℂ) (φ : Fin N → ℂ)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2) (s,φ)) :
    regularTransport p q F s φ =
      fderiv ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2) (s,φ)
        (1,regularResidualField p q s φ) := by
  have hl := ((hasDerivAt_id (0:ℂ)).smul_const
    ((1:ℂ),regularResidualField p q s φ)).const_add (s,φ)
  have hl' : HasDerivAt (fun t : ℂ => (s+t,fun i => φ i+t*regularResidualField p q s φ i))
      (1,regularResidualField p q s φ) 0 := by
    convert! hl using 1
    · ext t i <;> simp
    · simp
  have hh := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl' (by simp)
  convert! hh.deriv using 1

theorem regularKernel_inverse_frozen {N : ℕ} (p q : Fin N) (s : ℂ) (φ : Fin N → ℂ)
    (hs : s ≠ 0) (hslit : ∀ i, 1-(s+s⁻¹-Complex.cos (φ i))^2 ∈ Complex.slitPlane)
    (hd : ∀ i, 1-(regularY s (φ i))^(-2:ℤ) ≠ 0)
    (hg : ∀ i, regularG s (φ i) ≠ 0) (hn : ∀ i, Complex.sin (φ i) ≠ 0)
    (hpq : regularB s (φ p)-regularB s (φ q) ≠ 0) (hK : regularKernel s φ ≠ 0) :
    regularTransport p q (fun t ψ => (regularKernel t ψ)⁻¹) s φ = 0 := by
  have hY := regularYProduct_transport p q s φ hs hslit hd hg hn hpq
  have hZ := regularZProduct_transport p q s φ
  have hh := (hY.const_sub 1).fun_mul (hZ.const_sub 1)
  have hne : (1-regularYProduct (s+0) (fun i => φ i+0*regularResidualField p q s φ i))*
      (1-regularZProduct (s+0) (fun i => φ i+0*regularResidualField p q s φ i)) ≠ 0 := by
    simpa only [regularKernel, zero_mul, add_zero] using hK
  have hh' := hh.inv hne
  convert! hh'.deriv using 1
  simp

theorem regularTransport_eq_partials {N : ℕ} (p q : Fin N)
    (F : ℂ → (Fin N → ℂ) → ℂ) (s : ℂ) (φ : Fin N → ℂ)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2) (s,φ)) :
    regularTransport p q F s φ = deriv (fun t => F t φ) s +
      ∑ i, regularResidualField p q s φ i*fderiv ℂ (F s) φ (Pi.single i 1) := by
  rw [regularTransport_fderiv p q F s φ hF]
  have hv : ((1:ℂ),regularResidualField p q s φ) =
      ((1:ℂ),(0:Fin N → ℂ))+∑ i, regularResidualField p q s φ i • spatialDirection i := by
    apply Prod.ext
    · change (1:ℂ) = 1+(ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ))
        (∑ i, regularResidualField p q s φ i • spatialDirection i)
      rw [map_sum]
      simp [spatialDirection]
    · change regularResidualField p q s φ = 0+(ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))
        (∑ i, regularResidualField p q s φ i • spatialDirection i)
      rw [map_sum, zero_add]
      funext k
      simp [spatialDirection, Pi.single_apply, Finset.sum_apply]
  rw [hv, map_add, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hp := hF.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s φ))
  have hp' : deriv (fun t => F t φ) s =
      fderiv ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2) (s,φ) (1,0) := by
    convert! hp.deriv using 1
  rw [hp']
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [joint_spatial_eq _ s φ i hF]

theorem regularTransport_hasDerivAt {N : ℕ} (p q : Fin N)
    (F : ℂ → (Fin N → ℂ) → ℂ) (s : ℂ) (φ : Fin N → ℂ)
    (hF : DifferentiableAt ℂ (fun z : ℂ × (Fin N → ℂ) => F z.1 z.2) (s,φ)) :
    HasDerivAt (fun t : ℂ => F (s+t) (fun i => φ i+t*regularResidualField p q s φ i))
      (regularTransport p q F s φ) 0 := by
  have hl := ((hasDerivAt_id (0:ℂ)).smul_const
    ((1:ℂ),regularResidualField p q s φ)).const_add (s,φ)
  have hl' : HasDerivAt (fun t : ℂ => (s+t,fun i => φ i+t*regularResidualField p q s φ i))
      (1,regularResidualField p q s φ) 0 := by
    convert! hl using 1
    · ext t i <;> simp
    · simp
  have hh := hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl' (by simp)
  convert! hh.differentiableAt.hasDerivAt using 1

end
end IsingBulk.Jets
