import IsingBulk.Anisotropic.RegularEdges.OddRadialPrimitive
import IsingBulk.First.ShapePolar
import IsingBulk.First.ShapeSource

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace IsingBulk.Anisotropic.RegularEdges

theorem oddRadialKernel_integral (m : ℕ) {Q c : ℂ} (hQ : 0<Q.re) (hc : 0<c.re) :
    ∫ r in Ioi (0:ℝ), oddRadialKernel m Q c r = 1/(2*((m+1:ℕ):ℂ)*Q*c^(m+1)) := by
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r (_hr : r∈Ici (0:ℝ)) => oddRadialPrimitive_hasDerivAt m hQ hc r)
    (oddRadialKernel_integrable m hQ hc).integrableOn
    (oddRadialPrimitive_tendsto m hQ hc)
  simpa [oddRadialPrimitive] using hh

theorem oddRadialKernel_integral_ne_zero (m : ℕ) {Q c : ℂ} (hQ : 0<Q.re) (hc : 0<c.re) :
    (∫ r in Ioi (0:ℝ), oddRadialKernel m Q c r) ≠ 0 := by
  rw [oddRadialKernel_integral m hQ hc]
  have hq : Q≠0 := by intro h; simp [h] at hQ
  have hc0 : c≠0 := by intro h; simp [h] at hc
  exact one_div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Nat.cast_ne_zero.mpr (by omega))) hq) (pow_ne_zero _ hc0))

open IsingBulk.First

theorem shapePeriod_odd_eq_radial {n m : ℕ} (hn : 1≤n)
    (hdegree : n-1+(n+1)*n=2*m+1) (Q : ℝ) (c : ℂ) :
    shapePeriod n (m+1) Q c = shapeAngularConstant n •
      (∫ r in Ioi (0:ℝ), oddRadialKernel m Q c r) := by
  rw [shapePeriod_eq_intrinsic]
  have h := integral_shapeVandermonde_polar hn
    (fun r => (((Q:ℂ)+c*(r:ℂ)^2)^(m+2))⁻¹)
  rw [hdegree] at h
  have hi : shapePeriodIntrinsic n (m+1) Q c = shapeSphereIntegral n •
      (∫ r in Ioi (0:ℝ), oddRadialKernel m Q c r) := by
    simpa only [shapePeriodIntrinsic,oddRadialKernel,Complex.real_smul,
      Complex.ofReal_pow,div_eq_mul_inv,Nat.add_assoc] using h
  rw [hi,smul_smul]
  rfl

theorem shapePeriod_odd_ne_zero {n m : ℕ} (hn : 1≤n)
    (hdegree : n-1+(n+1)*n=2*m+1) {Q : ℝ} (hQ : 0<Q)
    {c : ℂ} (hc : 0<c.re) : shapePeriod n (m+1) Q c≠0 := by
  rw [shapePeriod_odd_eq_radial hn hdegree]
  exact smul_ne_zero (shapeAngularConstant_pos hn).ne'
    (oddRadialKernel_integral_ne_zero m hQ hc)

theorem odd_edge_shapePeriod_ne_zero {n : ℕ} (hn : 1≤n) (ho : Odd (n+1))
    {Q : ℝ} (hQ : 0<Q) {c : ℂ} (hc : 0<c.re) :
    shapePeriod n (((n+1)^2-1)/2) Q c≠0 := by
  obtain ⟨a,ha⟩ := ho.pow (n:=2)
  have ha1 : 1≤a := by nlinarith
  have hpoly : n-1+(n+1)*n+2=(n+1)^2 := by
    have hh := Nat.sub_add_cancel hn
    nlinarith
  have hj : ((n+1)^2-1)/2=a := by omega
  rw [hj,←Nat.sub_add_cancel ha1]
  exact shapePeriod_odd_ne_zero hn (by omega) hQ hc

theorem shapeMajorant_odd_integrable {n m : ℕ} (hn : 1≤n)
    (hdegree : n-1+(n+1)*n=2*m+1) : Integrable (@shapeMajorant n (m+1)) := by
  let f : ℝ → ℂ := fun r => (((1+r^2)^(m+2):ℝ):ℂ)⁻¹
  have hr : IntegrableOn (fun r : ℝ => (r^(n-1+(n+1)*n)) • f r) (Ioi 0) := by
    have hbase := oddRadialKernel_integrable m (Q:=1) (c:=1) (by norm_num) (by norm_num)
    change Integrable (fun r : ℝ => (r:ℂ)^(2*m+1)/(1+1*(r:ℂ)^2)^(m+2)) at hbase
    simpa only [f,hdegree,Complex.real_smul,Complex.ofReal_pow,
      Complex.ofReal_add,Complex.ofReal_one,one_mul,div_eq_mul_inv] using
      hbase.integrableOn (s:=Ioi 0)
  have hc : Integrable (fun x : ShapeSpace n => (shapeMajorant (m+1) x:ℂ)) := by
    simpa only [shapeMajorant,f,Complex.real_smul,Complex.ofReal_div,
      div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,Nat.add_assoc] using
      integrable_shapeVandermonde_polar hn f hr
  simpa using hc.re

end IsingBulk.Anisotropic.RegularEdges
