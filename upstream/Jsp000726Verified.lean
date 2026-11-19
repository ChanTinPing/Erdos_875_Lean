module

public import Jsp000726.OriginalStatement
import Jsp000726.LowerRankTwoVerified
import Jsp000726PinnedStructure

namespace Jsp000726

open PublicStructure

/-- Erdős #875 with the gap cap required at every positive index. -/
public theorem erdos_875 :
    {c : ℝ | OriginalGapExponent c} = Set.Ici ((5 + Real.sqrt 17) / 2) :=
  (sharpOriginalGapStatements_of_dyadic dyadicSubsetStructure_from_plby).1

/-- The equivalent eventual version of Erdős #875 in Formal Conjectures. -/
public theorem erdos_875_eventual :
    {c : ℝ | OriginalEventualGapExponent c} = Set.Ici ((5 + Real.sqrt 17) / 2) :=
  (sharpOriginalGapStatements_of_dyadic dyadicSubsetStructure_from_plby).2

end Jsp000726

#print axioms Jsp000726.erdos_875
#print axioms Jsp000726.erdos_875_eventual
