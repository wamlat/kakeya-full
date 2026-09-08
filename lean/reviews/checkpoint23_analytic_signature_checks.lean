import LebesgueRealCap
import LebesgueMaximal
import BushIterationConsequences

namespace KakeyaFormal

example {k : ℕ} {m D C : ℝ}
    (h : SourceAnalyticInputs.TwoEnds (k+1) m D C) (hm : 0 ≤ m) (hD : 1 ≤ D) :
    LebesgueRealCap.LengthEstimate (k+1) m D (max D C) :=
  LebesgueRealCap.lengths_of_borel
    (MeasurableLengthEstimates.of_volume (h.globalize_measurable hm hD))

example {n : ℕ} (hn : 5 ≤ n) :
    LebesgueMaximal.Estimate n ((4*(n:ℝ)+4)/7) :=
  LebesgueMaximal.of_borel (BushIteration.bush_endpoint_maximal hn)

example {n : ℕ} (hn : 5 ≤ n) :
    LebesgueMaximal.Estimate n ((4*(n:ℝ)+3)/7) :=
  LebesgueMaximal.of_borel (BushIteration.weakened_bush_endpoint_maximal hn)

example {k : ℕ} (hn : 5 ≤ k+1) :
    LebesgueMaximal.LengthEstimate (k+1) ((4*((k+1:ℕ):ℝ)+4)/7) :=
  LebesgueMaximal.lengths_of_borel
    (MaximalLengths.of_unit (BushIteration.bush_endpoint_maximal hn))

example {k : ℕ} (hn : 5 ≤ k+1) :
    LebesgueMaximal.LengthEstimate (k+1) ((4*((k+1:ℕ):ℝ)+3)/7) :=
  LebesgueMaximal.lengths_of_borel
    (MaximalLengths.of_unit (BushIteration.weakened_bush_endpoint_maximal hn))

example {n : ℕ} {m : ℝ} (hm : 3 < m) (hn : 0 < n) (hdim : m ≤ (n:ℝ)-1) :
    LebesgueRealCap.VolumeEstimate n m (KakeyaScalar.limitProfile m)
      (max (KakeyaScalar.limitProfile m) 4) :=
  LebesgueRealCap.volume_of_borel
    (MeasurableEstimate.volume_form (MainEndpoint.real_cap_measurable hm n hn hdim))

end KakeyaFormal
