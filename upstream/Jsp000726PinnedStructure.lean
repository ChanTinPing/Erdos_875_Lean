module

public import Jsp000726.DyadicSixth
import ErdosProblems.Erdos587.HooleyDyadicModel

namespace Jsp000726.PublicStructure

open Filter

private def ofPlby (P : Erdos587.GeneralizedAP) : IntegerGAP where
  rank := P.rank
  base := P.base
  step := P.step
  length := P.length

public theorem dyadicSubsetStructure_from_plby : DyadicSubsetStructure := by
  obtain ⟨b, R, D, F, C, hb, hR, hD, hF, hC, hdyadic⟩ :=
    Erdos587.CFP.exists_delta_dyadic_full_width
  refine ⟨b, R, D, F, hb, hR, hD, hF, ?_⟩
  filter_upwards [hdyadic] with t ht
  intro A hA hcard
  obtain ⟨m, hm, hretain, _, P, hr, hrD, hproper, _, hsub, hlength, hsize, _⟩ :=
    ht A hA hcard
  exact ⟨m, hm, hretain, ofPlby P, hr, hrD, hproper, hsub, hlength, hsize⟩

end Jsp000726.PublicStructure
