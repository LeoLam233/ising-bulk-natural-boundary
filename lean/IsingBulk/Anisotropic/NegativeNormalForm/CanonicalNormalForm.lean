import IsingBulk.Anisotropic.NegativeNormalForm.EquivariantLocalNormalForm

/-! Exact scalar normalization of the actual quadratic pole coordinate. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.NegativeNormalForm

def scalarConfiguration {n : ℕ} (c : ℂ) : Config n →L[ℂ] Config n :=
  c • ContinuousLinearMap.id ℂ (Config n)

@[simp] theorem scalarConfiguration_apply {n : ℕ} (c : ℂ) (v : Config n) (i : Fin n) :
    scalarConfiguration c v i = c * v i := rfl

 theorem scalarConfiguration_zeroMean {n : ℕ} (c : ℂ) (v : Config n) (hv : ZeroMean v) :
    ZeroMean (scalarConfiguration c v) := by
  change ∑ i, c*v i = 0
  rw [← Finset.mul_sum,show ∑ i, v i=0 from hv,mul_zero]

@[simp] theorem scalarConfiguration_quadratic {n : ℕ} (c : ℂ) (v : Config n) :
    quadratic (scalarConfiguration c v) = c^2 * quadratic v := by
  simp [quadratic,mul_pow,Finset.mul_sum]

@[simp] theorem scalarConfiguration_permute {n : ℕ} (c : ℂ) (e : Equiv.Perm (Fin n)) (v : Config n) :
    scalarConfiguration c (permute e v)=permute e (scalarConfiguration c v) := rfl

 theorem hessian_inverse_sqrt_identity (h : ℂ) (hh : h ≠ 0) : h * (Complex.sqrt h)⁻¹^2 = 1 := by
  have hs : Complex.sqrt h ≠ 0 := by
    intro hz
    have hp := sqrt_sq h
    rw [hz,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hp
    exact hh hp.symm
  nth_rw 1 [← sqrt_sq h]
  field_simp [hs]

 theorem exists_canonical_actual_local_normal_form {n : ℕ} (hn : n ≠ 0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hh : centralHessian B phi d ≠ 0) :
    ∃ T : Config n → ℂ, ∃ Psi : Config n → Config n,
      AnalyticAt ℂ T 0 ∧ T 0=1-Complex.cos d ∧
      AnalyticAt ℂ Psi 0 ∧ Psi 0=0 ∧
      HasFDerivAt Psi (scalarConfiguration (Complex.sqrt (centralHessian B phi d))⁻¹) 0 ∧
      (∀ e : Equiv.Perm (Fin n), ∀ v, Psi (permute e v)=permute e (Psi v)) ∧
      (∀ᶠ y in 𝓝 (0:Config n), ZeroMean y →
        ZeroMean (Psi y) ∧ poleEquation B phi hphi d (T (Psi y)) (Psi y)=0 ∧
        T (Psi y)=1-Complex.cos d+quadratic y/(2*n)) := by
  obtain ⟨T,Phi,hT,hT0,_hTsym,hPhi,hPhi0,hd,hperm,hactual⟩ :=
    exists_equivariant_actual_local_normal_form hn B phi hphi d hB hBn hh
  let c := (Complex.sqrt (centralHessian B phi d))⁻¹
  let Psi : Config n → Config n := fun y => Phi (scalarConfiguration c y)
  have hPsi : AnalyticAt ℂ Psi 0 := hPhi.comp_of_eq ((scalarConfiguration c).analyticAt 0) (map_zero _)
  have hPsi0 : Psi 0=0 := by simp [Psi,hPhi0]
  have hd' : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config n)) (scalarConfiguration c 0) := by
    simpa using hd
  have hdPsi : HasFDerivAt Psi (scalarConfiguration c) 0 := by
    convert! hd'.comp (f := fun y => scalarConfiguration c y) 0
      ((scalarConfiguration c).hasFDerivAt (x := 0)) using 1
  have hsym (e : Equiv.Perm (Fin n)) (v : Config n) : Psi (permute e v)=permute e (Psi v) := by
    simp only [Psi,scalarConfiguration_permute,hperm]
  have ht : Tendsto (scalarConfiguration (n := n) c) (𝓝 0) (𝓝 0) := by
    simpa using ((scalarConfiguration (n := n) c).continuous.continuousAt (x := 0)).tendsto
  refine ⟨T,Psi,hT,hT0,hPsi,hPsi0,hdPsi,hsym,?_⟩
  filter_upwards [ht.eventually hactual] with y hy
  intro hm
  obtain ⟨hm',hp,hq⟩ := hy (scalarConfiguration_zeroMean c y hm)
  refine ⟨hm',hp,?_⟩
  rw [scalarConfiguration_quadratic] at hq
  change T (Phi (scalarConfiguration c y)) = _
  rw [hq]
  have hc : centralHessian B phi d*c^2=1 := hessian_inverse_sqrt_identity _ hh
  calc
    _ = 1-Complex.cos d+(centralHessian B phi d*c^2)*quadratic y/(2*n) := by ring
    _ = _ := by rw [hc,one_mul]

end IsingBulk.Anisotropic.NegativeNormalForm
