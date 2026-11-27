# Projected and unprojected auxiliary processes

The manuscript's occupation argument uses
$H_{j,n}(x)=\mathbb E[H_j(x)\mid\mathcal F_n]$ and defines its potential
from this conditionally projected quantity. Its centered process must be
read with that definition.

In the formalisation, `Zpot` in
[VdriftTimeAssembly.lean](../Swarm/VdriftTimeAssembly.lean) is instead a raw
auxiliary potential evaluated in the full environment. The statement
`Swarming.Enl.not_stronglyMeasurable_ZJinc_zero` in
[QIncrementAdapted.lean](../Swarm/QIncrementAdapted.lean) concerns that raw
object. It is not a counterexample to the manuscript's projected process.
Moreover, it states failure of pointwise strong measurability; it does not
rule out a measurable version up to null sets.

The adapted formal route explicitly constructs `ProjLedger.Zproj` and its
centered process `ProjLedger.Qpl` in
[ProjOptionalLedger.lean](../Swarm/ProjOptionalLedger.lean). The theorem
`ProjLedger.martingale_Qpl` checks measurability, integrability, and conditional
centering. The projected strong law is then applied in
[ProjectedStrongLaw.lean](../Swarm/ProjectedStrongLaw.lean).

Checked against the current manuscript definitions preceding `Zdrift`,
`Vdrift`, and $Q_n$. The raw counterexample is not a manuscript erratum and
concerns a raw auxiliary statement, not a premise of either principal theorem.
This note does not assert a line-by-line identification of every auxiliary
proof object.
