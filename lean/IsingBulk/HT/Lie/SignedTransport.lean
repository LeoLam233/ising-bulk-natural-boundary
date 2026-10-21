import IsingBulk.Analysis.LieTheorem
import IsingBulk.Analysis.JetsRegularKernel

/-!
HT-1.0, Appendix A: the signed global factors are frozen by the same
parameter-dependent transport field as the unsigned factors. The sign is
constant; it need not be positive. All analytic hypotheses are local and
are visible in the statements. This file does not assert that the HT
physical integrand satisfies the chart or vanishing-flux hypotheses.
-/
namespace IsingBulk.HT.Lie
noncomputable section
open Set IsingBulk.Lie IsingBulk.Jets IsingBulk.Branch
open scoped BigOperators

/-- The literal pair of HT signed simple global kernels. -/
def signedKernel {n : ℕ} (σ : ℂ) (Y Z : ℂ → AngularSpace n → ℂ)
    (s : ℂ) (x : AngularSpace n) : ℂ :=
  (1 - σ * Y s x)⁻¹ * (1 - σ * Z s x)⁻¹

theorem signedKernel_eq_simpleKernel {n : ℕ} (σ : ℂ)
    (Y Z : ℂ → AngularSpace n → ℂ) :
    signedKernel σ Y Z = simpleKernel (fun s x => σ * Y s x) (fun s x => σ * Z s x) := rfl

@[simp] theorem signedKernel_one {n : ℕ} (Y Z : ℂ → AngularSpace n → ℂ) :
    signedKernel 1 Y Z = simpleKernel Y Z := by
  funext s x
  simp [signedKernel, simpleKernel]

/-- Multiplication by a fixed sign commutes with the actual transport,
not merely with a formal descriptor of that transport. -/
theorem transport_const_mul {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ) (σ s : ℂ) (x : AngularSpace n)
    (hAs : DifferentiableAt ℂ (fun t => A t x) s)
    (hAx : DifferentiableAt ℝ (A s) x) :
    transport V (fun t y => σ * A t y) s x = σ * transport V A s x := by
  have hc : transport V (fun _ _ => σ) s x = 0 := by simp [transport]
  rw [transport_mul V (fun _ _ => σ) A s x
    (differentiableAt_const _) hAs (differentiableAt_const _) hAx,
    hc, zero_mul, zero_add]

/-- The two signed products use the existing LT frozen-kernel structure.
Only the newly relevant signed denominator gaps must be supplied. -/
theorem frozenKernel_scale {n : ℕ} {U : Set ℂ} {R : Set (AngularSpace n)}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ}
    {Y Z : ℂ → AngularSpace n → ℂ} (h : FrozenKernel U R V Y Z)
    (σ : ℂ)
    (hY : ∀ s ∈ U, ∀ x ∈ R, 1 - σ * Y s x ≠ 0)
    (hZ : ∀ s ∈ U, ∀ x ∈ R, 1 - σ * Z s x ≠ 0) :
    FrozenKernel U R V (fun s x => σ * Y s x) (fun s x => σ * Z s x) := by
  refine ⟨?_, ?_, ?_, ?_, hY, hZ, ?_, ?_⟩
  · intro s hs x hx
    exact (h.Y_parameter s hs x hx).const_mul σ
  · intro s hs x hx
    exact (h.Z_parameter s hs x hx).const_mul σ
  · intro s hs x hx
    exact (h.Y_spatial s hs x hx).const_mul σ
  · intro s hs x hx
    exact (h.Z_spatial s hs x hx).const_mul σ
  · intro s hs x hx
    rw [transport_const_mul V Y σ s x (h.Y_parameter s hs x hx)
      (h.Y_spatial s hs x hx), h.Y_frozen s hs x hx, mul_zero]
  · intro s hs x hx
    rw [transport_const_mul V Z σ s x (h.Z_parameter s hs x hx)
      (h.Z_spatial s hs x hx), h.Z_frozen s hs x hx, mul_zero]

/-- A signed kernel is frozen on the actual open regular locus. -/
theorem signedKernel_frozen {n : ℕ} {U : Set ℂ} {R : Set (AngularSpace n)}
    {V : ℂ → AngularSpace n → Fin (n+1) → ℂ}
    {Y Z : ℂ → AngularSpace n → ℂ} (h : FrozenKernel U R V Y Z)
    (σ : ℂ)
    (hY : ∀ s ∈ U, ∀ x ∈ R, 1 - σ * Y s x ≠ 0)
    (hZ : ∀ s ∈ U, ∀ x ∈ R, 1 - σ * Z s x ≠ 0)
    {s : ℂ} (hs : s ∈ U) {x : AngularSpace n} (hx : x ∈ R) :
    transport V (signedKernel σ Y Z) s x = 0 :=
  (frozenKernel_scale h σ hY hZ).transport_zero hs hx

/-- The full previous top-form density is differentiated at every stage.
The imported theorem includes the divergence and the derivative of the
real cutoff; neither is omitted by the sign change. -/
theorem signed_kernel_preserved_of_regular {n : ℕ} (T : PuncturedTorus n)
    (U : Set ℂ) (hU : IsOpen U)
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (w : AngularSpace n → ℝ)
    (A B Y Z : ℂ → CoordinateTopForm n) (σ : ℂ) (j : ℕ)
    (hV : ∀ s ∈ U, ∀ x ∈ T.regular, ∀ i,
      DifferentiableAt ℝ (fun y => V s y i) x)
    (hr : ∀ k < j, StageRegularity T U V
      ((lieStep V)^[k] (fun s x => (w x : ℂ) * A s x)))
    (hK : FrozenKernel U T.regular V Y Z)
    (hY : ∀ s ∈ U, ∀ x ∈ T.regular, 1 - σ * Y s x ≠ 0)
    (hZ : ∀ s ∈ U, ∀ x ∈ T.regular, 1 - σ * Z s x ≠ 0)
    (hfactor : ∀ s ∈ U, ∀ x ∈ T.regular,
      A s x = signedKernel σ Y Z s x * B s x) :
    ∀ k ≤ j, ∀ s ∈ U, ∀ x ∈ T.regular,
      ((lieStep V)^[k] (fun t y => (w y : ℂ) * A t y)) s x =
        signedKernel σ Y Z s x *
          ((lieStep V)^[k] (fun t y => (w y : ℂ) * B t y)) s x := by
  exact fixed_domain_lie_kernel_of_regular T U hU V w A B
    (fun s x => σ * Y s x) (fun s x => σ * Z s x) j hV hr
    (frozenKernel_scale hK σ hY hZ) hfactor

/-- The signed denominator in regular branch coordinates. -/
def signedRegularKernel {N : ℕ} (σ s : ℂ) (φ : Fin N → ℂ) : ℂ :=
  (1 - σ * regularYProduct s φ) * (1 - σ * regularZProduct s φ)

@[simp] theorem signedRegularKernel_one {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) :
    signedRegularKernel 1 s φ = regularKernel s φ := by
  simp [signedRegularKernel, regularKernel]

/-- Exact signed chart correspondence; the contour Jacobian is not altered. -/
theorem signedRegularKernel_chart {n : ℕ} (σ s : ℂ) (v θ : ℝ)
    (x : AngularSpace n) (hg : ∀ i, 0 < (angularG v θ (x i)).re) :
    signedRegularKernel σ s (fun i => chartPhase s v θ (x i)) =
      (1 - σ * actualY v θ s x) * (1 - σ * actualZ v θ s x) := by
  simp only [signedRegularKernel, regularYProduct,
    regularY_chartPhase _ _ _ _ (hg _), actualY_eq_product,
    regularZProduct, actualZ]

/-- Both regular-coordinate product transport identities are imported
unchanged, then composed with the constant sign. -/
theorem signedRegularKernel_frozen {N : ℕ} (p q : Fin N) (σ s : ℂ)
    (φ : Fin N → ℂ) (hs : s ≠ 0)
    (hslit : ∀ i, 1 - (s+s⁻¹-Complex.cos (φ i))^2 ∈ Complex.slitPlane)
    (hd : ∀ i, 1 - (regularY s (φ i))^(-2:ℤ) ≠ 0)
    (hg : ∀ i, regularG s (φ i) ≠ 0)
    (hn : ∀ i, Complex.sin (φ i) ≠ 0)
    (hpq : regularB s (φ p)-regularB s (φ q) ≠ 0) :
    regularTransport p q (signedRegularKernel σ) s φ = 0 := by
  have hY := regularYProduct_transport p q s φ hs hslit hd hg hn hpq
  have hZ := regularZProduct_transport p q s φ
  have hh := ((hY.const_mul σ).const_sub 1).fun_mul
    ((hZ.const_mul σ).const_sub 1)
  simpa only [regularTransport, signedRegularKernel, mul_zero, neg_zero,
    zero_mul, add_zero] using hh.deriv

/-- The signed inverse remains a simple inverse, at every particle number.
This local statement has no even-particle premise. -/
theorem signedRegularKernel_inverse_frozen {N : ℕ} (p q : Fin N) (σ s : ℂ)
    (φ : Fin N → ℂ) (hs : s ≠ 0)
    (hslit : ∀ i, 1 - (s+s⁻¹-Complex.cos (φ i))^2 ∈ Complex.slitPlane)
    (hd : ∀ i, 1 - (regularY s (φ i))^(-2:ℤ) ≠ 0)
    (hg : ∀ i, regularG s (φ i) ≠ 0)
    (hn : ∀ i, Complex.sin (φ i) ≠ 0)
    (hpq : regularB s (φ p)-regularB s (φ q) ≠ 0)
    (hK : signedRegularKernel σ s φ ≠ 0) :
    regularTransport p q (fun t ψ => (signedRegularKernel σ t ψ)⁻¹) s φ = 0 := by
  have hY := regularYProduct_transport p q s φ hs hslit hd hg hn hpq
  have hZ := regularZProduct_transport p q s φ
  have hh := ((hY.const_mul σ).const_sub 1).fun_mul
    ((hZ.const_mul σ).const_sub 1)
  have hne : (1 - σ * regularYProduct (s+0)
      (fun i => φ i+0*regularResidualField p q s φ i)) *
      (1 - σ * regularZProduct (s+0)
      (fun i => φ i+0*regularResidualField p q s φ i)) ≠ 0 := by
    simpa only [signedRegularKernel, zero_mul, add_zero] using hK
  have hh' := hh.inv hne
  convert! hh'.deriv using 1
  simp

end
end IsingBulk.HT.Lie
