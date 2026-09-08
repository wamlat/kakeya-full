---
title: "A six-dimensional Kakeya maximal estimate"
subtitle: 'The implication \(\mathsf M_6(4)\Rightarrow\mathsf M_6(33/8)\)'
date: "5 September 2026"
geometry: margin=24mm
fontsize: 11pt
---

**Research draft.** The maximal estimate stated here has not been independently verified.

## Abstract

We give an argument for a six-dimensional Kakeya maximal estimate with exponent \(33/8\), starting from Wolff's exponent \(4\). The transverse discrete estimate has set exponent \(33/8\) and density exponent \(15/4\). Its lifted input follows from a random projection of a cap-four family in \(\mathbb R^7\) to \(\mathbb R^5\), followed by Wolff's five-dimensional maximal theorem. Angular decomposition, sampling, and two-ends localization then give the arbitrary-density conclusion. The proof keeps sampled cell counts separate from the occupied cells before rescaling.

# 1. Statement and conventions

Put \(\delta=N^{-1}\), \(L=\log(2N)\). Consider unit \(\delta\)-tubes in a fixed bounded subset of \(\mathbb R^6\), with \(c\delta\)-separated unoriented directions. Write \(M\) for their number and \(S=\delta^5M\lesssim1\). Fixed changes of tube width, length, separation, and bounded-region normalization are permitted; a fixed-factor width adjustment permits a dyadic mesh \(\delta\). A discrete shading consists of cells of a common \(\delta\)-grid whose centers lie within \(C\delta\) of the tube. There are \(O(N)\) such cells per tube and \(O(1)\) in any longitudinal interval of length \(\delta\). Write \(E\) for the number of occupied cells. Its full-cell volume is \(\delta^6E\).

Let \(\mathsf M_6(a)\) mean that, for every \(\varepsilon>0\), arbitrary measurable shadings \(Y(T)\subset T\) with \(|Y(T)|\ge\lambda|T|\) satisfy
\[
 \left|\bigcup_TY(T)\right|
 \ge c_\varepsilon\delta^{6-a+\varepsilon}\lambda^aS,
 \qquad 0<\lambda\le1.
\tag{1}
\]
The constant is uniform in \(\delta,\lambda,M\). Families in arbitrary locations reduce to the bounded-region formulation by assigning each unit tube to one of the boundedly many unit cubes meeting a fixed fraction of its shading.

**Theorem 1.1.** Assuming \(\mathsf M_6(4)\), one has \(\mathsf M_6(33/8)\). Explicitly, the conclusion is
\[
 \left|\bigcup_TY(T)\right|
 \ge c_\varepsilon\delta^{15/8+\varepsilon}
       \lambda^{33/8}S.
\tag{2}
\]

Besides the assumed six-dimensional bound, the only external Kakeya input used below is Wolff's published five-dimensional maximal bound with exponent \(7/2\). The remaining arguments are included. The quantitative core has two-ends set exponent \(D=33/8\) and density exponent \(C=15/4\). The strict inequalities \(C<D<5\) are essential to its globalization.


The proof has four parts. Section 2 establishes the lifted input, and Section 3 records the angular decomposition and continuous comparison used after rescaling. Section 4 proves the transverse discrete estimate by pruning, a pivot construction, and an energy bound. Sections 5--7 remove angular concentration and two ends, then pass from discrete to measurable shadings.

A shading has two ends with fixed exponent \(\alpha>0\) and constant \(B\) if
\[
 |Y(T)\cap B(x,r)|\le Br^\alpha |Y(T)|,\qquad \delta\le r\le1.
\tag{3}
\]
For discrete shadings this means cell counts. All auxiliary positive exponents are fixed before \(N\) varies. An expression \(L^{O(1)}\) below has an exponent depending only on those fixed parameters, never on \(N,\lambda\). In particular it is absorbable in an arbitrarily small prescribed power of \(N\).

# 2. The cap-four lifted input from projection to \(\mathbb R^5\)

**Lemma 2.1 (lifted maximal input).** Let \(\mathcal L\) be \(M\) direction-separated unit \(\delta\)-tubes in \(\mathbb R^7\) satisfying
\[
 \#\{\ell:\operatorname{dir}\ell\in B(v,r)\}
 \le A(Nr)^4,\qquad \delta\le r\le1,\quad A\ge1.
\tag{4}
\]
For arbitrary discrete shadings, including empty shadings, with total incidence count at least \(sNM\), their union count satisfies
\[
 E_{\mathcal L}\ge c_eA^{-1}N^{-1/2-e}s^{7/2+e}M
\tag{5}
\]
for every \(e>0\). The constant is independent of \(A,N,s,M\).

**Proof.** First assume comparable nonzero shading counts \(sN\). Let \(P:\mathbb R^7\to\mathbb R^5\) be a standard Gaussian matrix. Choose a fixed large \(K\) and small \(c>0\). With probability bounded below, \(\|P\|\le K\) and at least \(M/2\) directions satisfy \(|Pv|\ge c\): use the operator-norm tail, the small-ball bound for \(Pv\), and Markov's inequality for the number of bad directions.

For two projective directions at angle \(\psi\), write \(v'=\cos\psi\,v+\sin\psi\,w\) with \(w\perp v\). The Gaussian vectors \(Pv,Pw\) are independent. Conditional on \(Pv\), the component of \(Pw\) perpendicular to it is a four-dimensional standard Gaussian. On \(\|P\|\le K\), projected angular distance at most \(C\delta\) forces that perpendicular component to have norm at most \(C_K\delta/\sin\psi\). Thus the collision probability is at most
\[
 C_K\min\{1,(\delta/\psi)^4\}.
\]
Summing in dyadic angular annuli and using (4) gives at most \(CAM L\) expected ordered collisions. Choosing the Markov cutoff sufficiently large simultaneously with the preceding positive-probability event gives one bounded \(P\), at least \(M/2\) good directions, and at most \(CAM L\) collisions.

The collision graph has an independent set of size at least \(cM/(AL)\). Indeed a graph with \(V\) vertices and \(e\) edges has an independent set of size at least \(V^2/(V+2e)\), by ordering the vertices randomly and keeping vertices earlier than all their neighbors, followed by Cauchy--Schwarz.

Each original cell has projected image covered by \(O_K(1)\) target \(\delta\)-cells. Hence projected occupied count \(E'\le CE_{\mathcal L}\). On a good tube, a target cell restricts the original longitudinal parameter to an \(O_{c,K}(\delta)\) interval, so only \(O_{c,K}(1)\) original shading cells collapse there. The selected projected tubes therefore retain comparable density \(s\), have lengths bounded above and below, and separated directions. Wolff's \(\mathbb R^5\) maximal theorem gives
\[
 E'\ge c_\eta N^{-1/2-\eta}s^{7/2}\frac{M}{AL}.
\tag{6}
\]
Fixed changes in projected length and width cost only constants.

For cumulative density, discard tubes with density below \(s/2\), losing at most half the mass. Among the \(O(L)\) dyadic bins of positive integer counts, some bin has size \(M_j\) and lower density \(s_j\) with
\[
 s_j\ge s/4,\qquad s_jM_j\ge csM/L.
\]
Consequently \(s_j^{7/2}M_j\ge cs^{7/2}M/L\). Apply (6) to that bin. Positive densities range from \(1/N\) to a fixed constant, so the number of bins remains \(O(L)\) even when \(s<1/N\). Density above one is normalized at fixed cost. Absorb both logarithms using \(\eta<e\), and weaken \(s^{7/2}\) to \(s^{7/2+e}\). This proves (5). \(\square\)

This proof uses the integer cap exponent four and actual ambient space \(\mathbb R^7\). It supplies the single lifted seed needed here; no assertion about noninteger cap exponents or subsequent iterations is involved.

# 3. Angular decomposition and a continuous two-ends comparison

The angular selection below adapts Wang–Zahl's vector-selection argument (Lemma 7.8), with the needed higher-dimensional counting written out. The continuous estimate below applies when angular rescaling produces sparse measurable shadings. Normalized measurable volume and occupied-cell count are tracked separately.

**Lemma 3.1 (angular pieces).** Fix \(0<\beta\le1\). A direction-separated shaded family admits a common angular scale \(\tau\in[\delta,1]\), disjoint assigned tube families, and restricted shadings \(Y_j(T)\), such that each piece lies in one \(O(\tau)\)-tube, has directions in one \(O(\tau)\)-cap, retains total incidence mass at least \(cL^{-3}\) of the input, and has union overlap at most \(C\tau^{-\beta}\). At every retained point,
\[
 \#\{T:x\in Y_j(T),\ \operatorname{dir}T\in B(v,r)\}
 \le K(r/\tau)^\beta m_j(x),\qquad \delta\le r\le\tau,
\tag{7}
\]
with fixed \(K\). For discrete input, all choices are constant on old cells.

**Proof.** For a finite incident direction set \(V\), on the remaining directions maximize \(r^{-\beta}\#(V_{\rm rem}\cap B(v,r))\). Keep the directions in that cap and delete those in its \(100\)-fold enlargement, until half the original directions have been deleted. Maximality gives internal broadness and bounds the deleted number by a fixed multiple of the kept number. Before the stopping step, the remainder has at least \(\#V/2\) elements; comparison with a fixed radius-one covering gives at least \(cr^\beta\#V\) retained directions at that step. One dyadic radius class retains \(c/L\) of all directions. Its subsets are disjoint and there are at most \(C\tau^{-\beta}\) of them.

Apply this selection pointwise after a multiplicity pigeonhole; choose one common radius globally. These refinements cost at most \(CL^3\) in total incidence mass. Fix a bounded-overlap global covering by \(3\tau\)-caps and assign each selected pointwise cap to one containing global cap. A direction belongs to only \(O(1)\) such global caps. Assign each tube to the cap retaining most of its shading. To restore broadness, retain only points where assigned directions constitute at least a sufficiently small fixed fraction of the former subset. Integrating the rejected proportional thresholds loses only a fixed fraction of retained mass; (7) deteriorates by a fixed constant.

For each cap, cover space by width-\(C\tau\) tubes with parallel axes on a \(2\tau\)-lattice. Assign each tube to one containing cover tube. Only \(O(1)\) covering tubes occur at a point. Repeat the same proportional-point reset. Each original tube is assigned once; at a point there are at most \(C\tau^{-\beta}\) pieces. All selections concern finite incidence sets, so the stated measurability and cellwise constancy follow. \(\square\)

**Preserving density and marked incidences.** Suppose input full densities are comparable to \(\sigma\) and have two ends with logarithmic constant. Let \(I\) be the original mass and \(W\ge cL^{-3}I\) the mass after Lemma 3.1. Delete tubes retaining less than \(a=c'L^{-3}\) of their input shade. Their deleted retained mass \(D_0\le aI\le W/8\). Surviving densities lie in \([\sigma L^{-O(1)},C\sigma]\), and two ends deteriorates only logarithmically.

At each point compare surviving multiplicity \(m^*\) to previous multiplicity \(m\). The surviving mass on \(m^*<m/2\) is at most \(D_0\), because \(m^*\le m-m^*\). Mark the complementary good set. It carries at least \(W-2D_0\) mass and satisfies (7) with doubled error. Finally retain pieces whose good mass is at least half their full mass. The rejected good mass is at most the total bad mass \(D_0\). Thus at least \(5W/8\) good mass survives, without changing the overlap bound. The full shade here remains the restricted shade in its assigned piece.

**Lemma 3.2 (continuous density-squared hairbrush in \(\mathbb R^6\)).** For fixed \(\alpha>0\), logarithmic two-ends constant, and comparable density \(\sigma\), arbitrary measurable shadings satisfy
\[
 \left|\bigcup_TY(T)\right|
 \ge cL^{-P}\delta^2\sigma^2(\delta^5M)
\tag{8}
\]
for some finite \(P\) depending only on the fixed parameters. Logarithmic density ratios are permitted.

**Proof.** First suppose there is a good marked set of mass \(W_G\ge\frac12\sum_T|Y(T)|\) with unit-scale angular broadness exponent \(\beta\) and error \(K\). Allow densities between \(\lambda\) and \(\Lambda\). Choose
\[
 \theta=(CK)^{-1/\beta},\qquad r_0=(CBL)^{-1/\alpha}.
\]
A dyadic multiplicity class \(\mu\) carries at least \(cW_G/L\), so \(V:=|\bigcup Y(T)|\ge cW_G/(L\mu)\). Restrict to that class and retain tubes keeping at least \(1/(CL)\) of their full shading. Reset to points with at least \(c\mu\) retained incidences. Averaging gives a stem whose retained shading has volume at least \(c\lambda\delta^5/L\). Broadness makes a fixed fraction of these incidences transverse at angle at least \(\theta\). Since two such tubes intersect in volume at most \(C\delta^6/\theta\), the stem meets at least
\[
 c\mu\lambda\theta/(\delta L)
\]
retained bristles.

On each bristle delete a radius-\(r_0\) ball about its chosen stem intersection. Two ends for the refined shade loses only \(CL\), so at least \(c\lambda\delta^5/L\) shading remains, at distance at least \(cr_0\theta\) from the stem. Partition bristles into \(\delta\)-separated plane bins through the stem. At distance \(s\) from it, the \(C\delta\)-thick plane neighborhoods overlap at most \(Cs^{-4}\) times. Within one plane bin, a \(\psi\)-cap contains \(O(\psi/\delta)\) directions. Summing pair intersections over angular annuli therefore gives at most \(CL\delta^5\) intersection volume per bristle. Cauchy--Schwarz in each bin yields union volume at least \(c\lambda^2\delta^5\#H_j/L^3\).

Sum the bins with overlap at most \(C(r_0\theta)^{-4}\), then use the bristle count. This gives
\[
 V\ge c(r_0\theta)^4\theta\,\mu\lambda^3\delta^4/L^4.
\]
Taking the geometric mean with \(V\ge cW_G/(L\mu)\) gives
\[
 V\ge c(r_0\theta)^{5/2}L^{-5/2}
          (W_G\lambda^3\delta^4)^{1/2}.
\tag{9}
\]
Direction packing gives \(M\lesssim\delta^{-5}\), hence \(W_G\lesssim\Lambda\) and
\[
 V\ge c(r_0\theta)^{5/2}L^{-5/2}
       \delta^2\lambda^{3/2}\Lambda^{-1/2}W_G.
\tag{10}
\]
These arguments use measurable intersection volume throughout. If \(r_0\theta<C\delta\) and \(B,K\) are logarithmic, then \(N\) is bounded by a fixed power of \(L\). Bounded direction count and \(V\ge W_G/M\) give (10) with a larger logarithmic loss.

For arbitrary angular concentration, apply Lemma 3.1 with, say, \(\beta=1/4\), and apply the density and mark refinement above. In each piece expand transverse coordinates by \(\tau^{-1}\). New width is \(\delta'=\delta/\tau\); directions are separated at that width, density is unchanged up to constants, and two ends survives because the inverse map is a contraction. Good mass and union volume have the same determinant \(\tau^{-5}\). Apply (10) in the new coordinates and cancel this determinant:
\[
 V_j\ge cL^{-P}\delta^2\tau^{-2}\sigma W_{G,j}.
\]
The overlap is at most \(C\tau^{-1/4}\), and retained good mass is at least \(cL^{-3}\sigma\delta^5M\). Summing gives (8), since \(\tau^{1/4-2}\ge1\). If the new eccentricity is only a fixed power of the original \(L\), use the preceding coarse-scale argument directly. \(\square\)

# 4. The transverse discrete pivot

**Lemma 4.1 (quantitative core).** Suppose full discrete shading counts are comparable to \(\lambda N\), obey (3), and have marked incidence mass at least \(\xi\lambda NM\). At every marked cell, each projective cap of radius \(\theta\) contains at most one tenth of the marks. Set
\[
 \kappa=c\min\{\theta,1/100,(c/B)^{1/\alpha}\}.
\]
For every fixed \(0<e<1\), if \(N\kappa^{20}\) is sufficiently large, then
\[
 E^4\ge c_e\kappa^{58}\xi^7L^{-8}
        N^{33/2-3e}\lambda^{15+2e}S^3.
\tag{11}
\]
Consequently logarithmic \(B,\xi^{-1},\theta^{-1}\) give, for every \(\eta>0\),
\[
 E\ge c_\eta N^{33/8-\eta}
          \lambda^{15/4+\eta}S^{3/4}.
\tag{12}
\]
The exponents in (12) are independent of \(\alpha\).

**Proof. Heavy-ball pruning.** The assumed \(\mathsf M_6(4)\), applied at every coarser scale, permits pruning with
\[
 F=C_eN^{2e}EN^{-4}\lambda^{-4}S^{-1}(L/\xi)^5
\tag{13}
\]
so the remaining occupied centers have at most \(CF(Nr)^4\) points in every radius-\(r\) ball. Here is the mass justification. At a dyadic scale \(r\), call a cube heavy if it originally contains more than \(F(Nr)^4\) occupied cells. If heavy cubes carry at least \(a\lambda NM\) incidences, where \(a=c\xi/L\), then at least \(caM\) tubes each meet at least \(ca\lambda/r\) heavy cubes. Coloring directions at separation \(r\) retains \(caM/(Nr)^5\) such tubes. The base estimate at scale \(r\) forces at least \(c_ea^5\lambda^4Sr^{-4+e}\) heavy cubes. Disjointness gives
\[
 E\ge c_eFa^5\lambda^4SN^4r^e,
\]
contradicting (13) for sufficiently large \(C_e\). Delete incidences in these original heavy cubes at all scales. Total deletion is at most \(\xi\lambda NM/100\). Delete tubes losing half their full shade, and then marks at cells losing half their original marked multiplicity. The inequality \(m'\le m-m'\) on the latter cells bounds this extra loss. A fixed fraction of marked mass survives, full two ends deteriorates by at most two, and each surviving cap has at most one fifth of the marks. The base input at the original scale also ensures \(F\ge1\).

Let \(\mathcal A\) be the ordered transverse angle triples \((x,T_1,T_2)\) at surviving marked cells. Cauchy--Schwarz gives
\[
 \#\mathcal A\ge c\xi^2\lambda^2S^2N^{12}/E.
\tag{14}
\]
Shift both axes by \(O(\delta)\) through the representative vertex \(x\), and project shading centers to them. Two ends supplies fixed mass fractions of triples, in translated coordinates,
\[
 i=s u_1,\quad y_1=b u_1,\quad y_2=c u_2,\qquad
 0<s<b\le4,\quad s,b-s,|c|\ge\kappa,\quad
 |u_1\wedge u_2|\ge\kappa.
\tag{15}
\]
Indeed choose one half of the first shade, remove the vertex neighborhood, and take first and last fixed mass fractions; failure of their separation would put a fixed fraction of shading in an \(O(\kappa)\)-ball. The second shade is chosen away from the vertex. There are at least \(c\lambda^3N^3\) triples per angle.

**Finite fibers and collisions.** Set
\[
 u=c(1-s/b),\qquad z=i+u u_2.
\]
Then \(z=(s/b)y_1+(1-s/b)y_2\);
\[
 |u|,|c-u|\ge c\kappa^2,\quad
 |z-y_1|,|z-y_2|,\operatorname{dist}(z,\mathbb Ru_1)
 \ge c\kappa^3.
\tag{16}
\]
Use the unique half-open grid cell containing \(z\) as its rounded label \(z_0\), and put \(f=(z_0,e_0)\), where \(e_0\) is the original label of \(i\). Fix the shifted axes, orientations, and sample subsets once per angle. Define its angle-output fiber \(\mathcal P(a,f)\) as the set of endpoint pairs \((e_1,e_2)\) in its admissible triples yielding \(f\).

For a fixed angle there are at most \(C\lambda N^2\) nonempty fibers: \(O(\lambda N)\) choices of \(e_0\), then \(O(N)\) pivot cells along a bounded segment. Fixing also \(e_1\) confines \(c\) to an \(O(\delta/\kappa)\) interval, so each fiber has at most \(C\kappa^{-1}N\) pairs. Delete fibers smaller than \(c_0\lambda^2N\), losing at most half the triples per angle. One dyadic integer bin \([h,2h)\) carries at least \(c/L\) of remaining triples. With \(\sigma=h/N\) and \(\Omega\) the set of its angle-output incidences,
\[
 \sigma\ge c\lambda^2,\qquad
 \#\Omega\ge c\lambda^3\sigma^{-1}N^2\#\mathcal A/L.
\tag{17}
\]

For fixed \(f\), every second direction lies within \(C\delta\kappa^{-2}\) of the projective direction \(z_0-\bar e_0\). At most \(C\kappa^{-10}\) original second tubes are possible. Retain the most frequent one, deleting whole angle-output incidences, and write \(m(f)\) for the remaining multiplicity. This retains at least \(c\kappa^{10}\#\Omega\) incidences.

For a fixed angle \(a\), another angle sharing \(f\) now shares its second tube. Its first axis passes within \(O(\delta)\) of \(e_0\), and its vertex lies within \(O(\delta)\) of that common second axis. The first direction therefore lies within \(C\delta/\kappa\) of the plane of \(a\). In the shell \(\phi\le\angle(T_1,T'_1)\le2\phi\), direction separation permits \(C\kappa^{-4}N\phi\) first tubes. For each there are \(C/\phi\) shared \(e_0\) labels, \(CN\) pivot cells per label, and \(C/\kappa\) possible vertices. Include the below-\(\delta\) shell at \(\phi=\delta\). Summing gives
\[
 \sum_fm(f)^2\le C\kappa^{-5}N^2L\#\mathcal A.
\]
Hence the number \(Q\) of surviving outputs satisfies
\[
 Q\ge c\kappa^{25}\lambda^6\sigma^{-2}N^2
             \#\mathcal A\,L^{-3}.
\tag{18}
\]
Only now select one surviving angle \(a(f)\) per output and exactly \(h\) pairs in its intact fiber. No samples are combined across different angles.

**Exact lifts.** For each output choose one of these pairs and its exact pivot parameter \(u_f\). All selected pairs have \(|u-u_f|\le C\delta\). Define the graph line in \(\mathbb R^7\)
\[
 \ell_f(t)=(x+t u_f u_2,t).
\]
The pair with second endpoint \(x+c u_2\) supplies the exact point \(\ell_f(c/u_f)\). Here \(1+c\kappa\le c/u_f\le C/\kappa\), by (15) and \(\delta\ll\kappa^{20}\). If pairs land in one lifted cell, their \(c\)'s lie in an \(O(\delta)\) interval. The formula \(b=cs/(c-u)\), with (16), confines \(b\) to an \(O(\kappa^{-4}\delta)\) interval. Thus at most \(C\kappa^{-4}\) pairs land in one cell.

There are consequently at least \(c\kappa^4h\) distinct lifted cells per output, in at most \(C/\kappa\) unit vertical slabs. Choose a fullest slab and retain exactly
\[
 K=\max\{1,\lfloor c_1\kappa^6h\rfloor\},\qquad
 \rho=K/N\ge c\kappa^6\sigma
\tag{19}
\]
cells in it. Fix one original pair assigned to each retained cell. The initial incidence mass is exactly \(I_0=KQ=\rho NQ\); overlapping cells on different lines do not reduce it.

At fixed \(z_0\), graph slopes differ from \(z_0-\bar e_0\) by \(O(\delta)\) and are uniformly bounded. A radius-\(r\) direction cap therefore confines \(e_0\) to an \(O(r)\)-ball, giving cap count \(CF(Nr)^4\). A \(C\delta\)-cap contains only \(O(1)\) grid labels \(e_0\). Bounded-degree coloring yields a fixed number of separated direction families, keeping every output in one color.

Group by \(g=(z_0,j_f)\), where \(j_f\) is the chosen unit slab; let \(M_g\) be its line count, so \(\sum_gM_g=Q\). Translate each slab to \([0,1]\). The selected horizontal points are close to bounded original endpoints, and slopes are bounded, so this normalization uses fixed geometric constants even when the original slab index is large. Boundary cells remain within \(C\delta\) of the unit segment.

**Grouped pruning.** Lemma 2.1 applies with coefficient \(CF\) to every group and direction color, including arbitrary high-multiplicity restrictions. Let \(m_g(v)\) count all colors. Delete incidences at cells where
\[
 m_g(v)>H,\qquad
 H=C_eF\rho^{-5/2-e}N^{3/2+e}.
\tag{20}
\]
At least \(I_0/2\) mass remains. To see this, let \(I_{g,c}\) be high-cell incidence mass, \(s_{g,c}=I_{g,c}/(NM_{g,c})\), and \(I_{\rm high}=\sum I_{g,c}\). Lemma 2.1 and weighted convexity give
\[
 \sum_{g,c}\#U_{g,c}\ge
 c_eF^{-1}N^{-1/2-e}Q
       \left(\frac{I_{\rm high}}{NQ}\right)^{7/2+e}.
\]
The same sum is at most \(J_0I_{\rm high}/H\le J_0I_0/H\), where \(J_0\) is the fixed color number. If \(I_{\rm high}\ge I_0/2\), these inequalities contradict (20) for large \(C_e\). Retained incidence mass \(I\ge I_0/2\) has grouped energy at most \(HI\).

**Endpoint energy.** Every retained incidence has its assigned original triple \((e_1,e_2,z_0)\). There are at most \(CNE^2\) such triples, since the pair's own pivot lies within \(C\delta\) of the segment between the two original endpoint centers. The line parameter \(t=c/u_f\) obeys the exact identity
\[
 tz-y_2-(t-1)y_1
 =(u-u_f)(-b u_1/u_f+t u_2).
\]
After replacing points by cell centers,
\[
 \bar e_2-\bar e_1=t(z_0-\bar e_1)+O(\kappa^{-2}\delta).
\tag{21}
\]
Since \(|z_0-\bar e_1|\ge c\kappa^3\), a fixed triple restricts \(t\) to an interval of length \(C\kappa^{-5}\delta\). Its lifted horizontal coordinate is within \(C\delta\) of \(\bar e_2\). Thus each triple permits at most \(C\kappa^{-6}\) lifted cells. The slab index is determined by the lifted cell center and adds no choice.

The support of grouped energy therefore has at most \(C\kappa^{-6}NE^2\) targets. Cauchy--Schwarz, without any injectivity assertion, gives
\[
 HI\ge\operatorname{Energy}
 \ge c\kappa^6I^2/(NE^2).
\]
Using \(I\ge c\rho NQ\) and (20),
\[
 E^2\ge c_e\kappa^6F^{-1}
                \rho^{7/2+e}N^{-3/2-e}Q.
\tag{22}
\]
Insert (18)--(19). The remaining fiber factor is
\[
 \lambda^6\sigma^{3/2+e}
 \ge c\lambda^{9+2e}.
\]
Equation (14) supplies \(\lambda^2\), and \(F^{-1}\) supplies \(\lambda^4\), giving \(\lambda^{15+2e}\). Their scale powers sum to \(33/2-3e\), their mass factor is \(\xi^7S^3L^{-8}\), and their conditioning factor is \(\kappa^{52+6e}\ge\kappa^{58}\). The two inverse occurrences of \(E\) move to the left. This proves (11).

For fixed \(\alpha\), logarithmic input conditioning makes \(\kappa^{-1}\) a fixed power of \(L\). Fourth roots and logarithmic absorption give (12). The bounded range before \(N\kappa^{20}\) is large follows from one nonempty shade with a changed constant. \(\square\)

# 5. Sampling the transformed measurable shadings

**Lemma 5.1 (sampling).** At scale \(h=1/R\) in \(\mathbb R^6\), let separated tubes have measurable full shadings \(F_T\) of comparable density \(\lambda>R^{-1/4}\), two ends with fixed \(0<\alpha\le1/4\) and logarithmic constant, and marks \(G_T\subset F_T\) of total normalized mass
\[
 W_g=h^{-6}\sum_T|G_T|\ge \xi\lambda RM.
\]
Assume \(\xi^{-1}\) is logarithmic and marked directions satisfy
\[
 \sum_{\operatorname{dir}T\in B(v,r)}1_{G_T}(x)
 \le Kr^\beta\sum_T1_{G_T}(x),\qquad h\le r\le1,
\tag{23}
\]
with logarithmic \(K\) and fixed \(\beta>0\). Let \(\mathcal Q\) be the cells with positive full intersection. Either
\[
 \#\mathcal Q\ge cW_g/\log(2R),
\tag{24}
\]
or there are full discrete shadings on the same tubes, supported in \(\mathcal Q\), with comparable density \(\lambda\), logarithmic two-ends constant, at least \(cW_g\) marked incidences, and marked cap radius at least an inverse logarithmic power satisfying Lemma 4.1's one-tenth condition.

**Proof.** Put
\[
 p_{TQ}=h^{-6}|F_T\cap Q|,\quad
 p^g_{TQ}=h^{-6}|G_T\cap Q|,\quad
 \mu_g(Q)=\sum_Tp^g_{TQ}.
\]
These are probabilities with \(p^g_{TQ}\le p_{TQ}\). Call cells with \(\mu_g(Q)<a_0\log(2R)\) low. If they carry half the marked mass, division by this per-cell upper bound gives (24).

Otherwise sample each tube-cell pair independently by one uniform random variable \(U_{TQ}\), selecting its full incidence when \(U_{TQ}\le p_{TQ}\) and its mark when \(U_{TQ}\le p^g_{TQ}\). Keep marks only in high cells. For each tube the full count has mean comparable to \(\lambda R\ge R^{3/4}\). Chernoff gives failure probability \(2\exp(-cR^{3/4})\) for comparable density.

Test two ends on the \(h\)-lattice of centers and dyadic radii \(r\ge h\). Cells whose centers lie in a test ball are contained in its \(O(h)\)-enlargement. Their expected count is at most \(CB r^\alpha\lambda R\). Choose an upper threshold four times this bound. The exponential Markov inequality gives failure probability at most \(\exp(-cB r^\alpha\lambda R)\), and the threshold is at least \(cR^{1/2}\). There are only \(O(R^{11}\log R)\) tube-ball tests. Their failures and density failures therefore have total probability tending to zero. Fixed enlargements of these balls control every ball of radius at least \(h\); no sub-\(h\) hypothesis is needed.

Integrate (23) over each cell. Choose
\[
 \theta=\min\{1/100,\tfrac12(1000K)^{-1/\beta}\}.
\]
Every radius-\(\theta\) cap is contained in a radius-\(2\theta\) net cap. Each such cap has expected marked count at most \(\mu_g(Q)/1000\). At a high cell, Chernoff bounds the probability that total marked count is below \(\mu_g(Q)/2\), or a net cap count exceeds \(\mu_g(Q)/20\), by \(2e^{-c\mu_g(Q)}\). There are \(O(R^6)\) cells and logarithmically many net caps. Taking the fixed \(a_0\) sufficiently large makes their total failure probability less than \(1/4\). For large \(R\), \(2\theta\ge h\), so the integrated hypothesis applies.

A union bound gives a simultaneous realization. Its marked mass is at least half the high expected mass, hence at least \(W_g/4\), and every cap contains at most one tenth of the actual marks. Every selected center lies within \(Ch\) of its tube, with bounded longitudinal multiplicity. All directions are unchanged. The union count is at most \(\#\mathcal Q\), regardless of whether filled cells extend outside the measurable union. \(\square\)

# 6. Removing angular concentration

**Lemma 6.1 (global two-ends estimate).** For every fixed \(\alpha>0\), logarithmic two-ends constant, and \(\eta>0\), arbitrary-angular discrete shadings of comparable density \(\lambda\) satisfy
\[
 E\ge c_\eta N^{D-\eta}\lambda^CS,\qquad
 D=33/8,\quad C=15/4.
\tag{25}
\]

**Proof.** Weaken \(\alpha\) to \(\min\{\alpha,1/4\}\). Apply Lemma 3.1 with \(\beta=1/4\), followed by the density and mark refinement of Section 3. Pigeonhole surviving tube densities by good marked mass. There are \(O(L)\) bins, so one retains at least \(\lambda NM L^{-A}\) marked incidences, with common density \(\lambda_1\) satisfying
\[
 \lambda L^{-A}\le\lambda_1\le C_0\lambda.
\tag{26}
\]
Reset marks at points where this class retains less than \(L^{-A'}\) of previous marked multiplicity. Integrating the threshold shows that, for fixed sufficiently large \(A'\), the loss is at most one quarter of selected marked mass. Broadness now has logarithmic error. Retain pieces with marked fraction at least \(L^{-A''}\), increasing \(A''\) to lose at most another quarter. Thus
\[
 \sum_jM_j\ge ML^{-A}
\tag{27}
\]
after enlarging \(A\), and every piece has comparable full density \(\lambda_1\), logarithmic full two ends, logarithmic marked broadness, and inverse logarithmic marked fraction.

For each piece \(j\), let \(\mathcal E_j\) be the set of original \(\delta\)-grid cells occupied by its restricted full shadings, and set \(E_j=\#\mathcal E_j\). Thus \(\mathcal E_j\) uses the restrictions produced by the preceding selections. Lemma 3.1 gives
\[
 \sum_jE_j\le C\tau^{-1/4}E.
\tag{28}
\]


Translate the containing \(O(\tau)\)-tube to the origin and expand its transverse coordinates by \(\tau^{-1}\). Put \(R=N\tau\), new width \(h=R^{-1}\), and \(S'=M_j/R^5\lesssim1\). In a projective chart old slopes are multiplied by \(\tau^{-1}\), so new directions are separated at scale \(h\). Density and marks transform with a common determinant; two ends survives because the inverse map is a contraction.

Write \(\Phi_j\) for this affine rescaling and \(\widetilde F_j(T)\) for the image of the full-cell shading assigned to \(T\). Define
\[
 \mathcal Q_j=\bigl\{Q:\ Q\text{ is an }h\text{-grid cell and }
 |Q\cap\textstyle\bigcup_T\widetilde F_j(T)|>0\bigr\}.
\]
Each \(\Phi_j(Q_0)\), for \(Q_0\in\mathcal E_j\), has diameter \(O(h)\) and therefore intersects only \(O(1)\) new cells in positive volume. It follows that
\[
 \#\mathcal Q_j\le CE_j.
\tag{29}
\]
The normalized measurable volume of the transformed union is comparable to \(\tau E_j\): the transverse determinant is \(\tau^{-5}\), while the new cell volume is \(h^6=\delta^6\tau^{-6}\).

If \(R\le N^{1/12}\), one old tube gives \(E_j\gtrsim\lambda_1N\), which dominates \(R^D\lambda_1^CS'\), because \(D<6\), \(C>1\), and \(S'\lesssim1\). Hence assume \(R>N^{1/12}\); logarithmic losses in \(N\) are then logarithmic losses in \(R\).

If \(\lambda_1\le R^{-1/4}\), apply the continuous Lemma 3.2 to the transformed full shade. Undoing normalized volume gives
\[
 E_j\ge cL^{-A}\tau^{-1}R^4\lambda_1^2S'.
\]
Its ratio to \(R^D\lambda_1^CS'\) is at least
\[
 cL^{-A}\tau^{-1}R^{4-D+(C-2)/4}
 =cL^{-A}\tau^{-1}R^{5/16}.
\]
This positive power absorbs all logarithms.

For \(\lambda_1>R^{-1/4}\), apply Lemma 5.1. In its counting branch, (29) gives
\[
 E_j\ge cL^{-A}\lambda_1RM_j.
\]
The ratio to \(R^D\lambda_1^CS'\) contains \(R^{6-D}\lambda_1^{1-C}\), so again absorbs logarithms.

In the sampling branch, let \(F_j^{\rm s}(T)\subset\mathcal Q_j\) be the discrete full shading selected in Lemma 5.1, and define
\[
 E_j^{\rm s}=\#\bigcup_T F_j^{\rm s}(T).
\]
Lemma 4.1 applies to these sampled full shades and high-cell marks. Since \(S'\lesssim1\), it gives, for arbitrarily small \(e>0\),
\[
 E_j^{\rm s}\ge c_eR^{D-e}\lambda_1^{C+e}(S')^{3/4}
 \ge c'_eR^{D-e}\lambda_1^{C+e}S'.
\]
Every selected cell belongs to \(\mathcal Q_j\), so
\[
 E_j^{\rm s}\le\#\mathcal Q_j\le CE_j.
\]
This comparison transfers the estimate to the original cell count \(E_j\). The density threshold gives \(\lambda_1^e>R^{-e/4}\), so every branch yields
\[
 E_j\ge c_\eta R^{D-\eta}\lambda_1^CS'
\tag{30}
\]
with arbitrarily small prescribed scale loss. Parameter-dependent bounded scales follow from one old tube.

Finally sum old counts using (28):
\[
 \begin{aligned}
 E&\ge c_\eta\tau^{1/4}\sum_j
       (N\tau)^{D-\eta}\lambda_1^C
              \frac{M_j}{(N\tau)^5}\\
 &\ge c_\eta N^{D-\eta}\lambda_1^C
       \tau^{-5/8-\eta}\sum_j\frac{M_j}{N^5}.
 \end{aligned}
\]
The \(\tau\)-factor is at least one. Equations (26)--(27) and logarithmic absorption prove (25).

The sampling branch uses the cell-count comparison (29). The factor \(\tau^{-1}\) available in the continuous branch does not enter its estimate; the summation is controlled by \(D<5\). \(\square\)

# 7. Removing two ends and recovering measurable shadings

**Lemma 7.1 (two-ends localization).** For fixed \(0<\alpha<1/2\), comparable discrete density \(\lambda\) admits a subfamily of size at least \(cM/L^2\), a common dyadic radius \(\rho\), and localized restrictions of comparable original density \(\nu\), with
\[
 \nu\gtrsim\rho^\alpha\lambda,\qquad \nu\lesssim\rho.
\tag{31}
\]
Each restriction lies in a \(\rho\)-ball and has two ends relative to that radius with fixed constant.

**Proof.** For each tube choose the smallest dyadic \(r_T\ge\delta\) for which some ball contains at least \(r_T^\alpha\) of its original shading. A fixed top-scale enlargement guarantees existence. Restrict to such a ball. At smaller radii, minimality bounds the restricted mass by \(C(r/r_T)^\alpha\) times its total; larger relative radii are trivial. Tube geometry bounds its original density by \(Cr_T\). Pigeonhole radius and retained density, each with \(O(L)\) classes. Restriction to one of the boundedly many \(\rho\)-grid cubes meeting its ball keeps a fixed fraction and preserves relative two ends. \(\square\)

**Proof of Theorem 1.1 for discrete shadings.** If \(\lambda\lesssim\delta\), one shade already dominates the target (2), since \(S\lesssim1\) and
\[
 \frac{\lambda\delta^5}{\delta^{6-D}\lambda^D}
 =(\delta/\lambda)^{D-1}.
\]
Otherwise trim initially to comparable counts. Apply Lemma 7.1 with \(\alpha>0\) to be chosen after the final error is prescribed. Use aligned dyadic grids so each chosen \(\rho\)-cube is a union of old cells. Assign each tube to one such cube containing a fixed fraction of its localized shade. Different spatial groups have disjoint shade unions.

In a group, the direction-conflict graph at separation \(C\delta/\rho\) has degree \(O(\rho^{-5})\). Keep a largest color, retaining at least \(c\rho^5\) of its tubes. Rescale isotropically by \((H\rho)^{-1}\) with fixed large \(H\), and extend the short tube segments to unit tubes. The exact new grid has mesh \(\delta/(H\rho)\), and shading density is comparable to \(\nu/\rho\). Relative two ends gives unit two ends for small rescaled balls; larger balls are trivial with a fixed constant.

Apply Lemma 6.1 at this scale. Undoing the similarity and the direction thinning gives, for original group tube mass \(S_Q\),
\[
 V_Q\ge c(\delta/\rho)^e\delta^{6-D}
             \nu^C\rho^{D-C}S_Q.
\tag{32}
\]
The retained fraction \(\rho^5\) cancels the inverse factor in rescaled normalized tube mass. This explains why no spatial multiplicity assumption is used in (32).

Here \(C=15/4<D=33/8\) and \(\rho\gtrsim\nu\), so \(\nu^C\rho^{D-C}\gtrsim\nu^D\). Also \((\delta/\rho)^e\ge\delta^e\) and \(\nu\gtrsim\delta^\alpha\lambda\). Summing disjoint groups yields
\[
 V\ge c\delta^{6-D+e+\alpha D}\lambda^DS/L^2.
\]
Given \(\varepsilon>0\), first fix \(\alpha,e\) with \(\alpha D+e<\varepsilon/2\), and only then absorb all fixed logarithmic losses. The powers \(D,C\) in Lemma 4.1 do not depend on this choice of \(\alpha\). No limit \(\alpha\to0\) is taken while holding a constant fixed. This proves (2) for discrete shadings.

**Measurable conversion.** Let \(U=\bigcup_TY(T)\) be the original measurable union and put \(w_Q=|U\cap Q|/\delta^6\). The range \(\lambda\lesssim\delta\) is again elementary. Cells with \(w_Q<c\lambda\) contain at most half the mass of any shade, since a tube meets \(O(N)\) cells. Partition the remaining cells into \(O(L)\) dyadic classes \(w\le w_Q<2w\). Assign every tube to a class contributing at least \(c\lambda|T|/L\) of its shade; retain one common class with at least \(cS/L\) tube mass.

Its full cells supply discrete density at least \(c\lambda/(wL)\) on every retained tube, because each cell contains at most \(2w\delta^6\) original shading volume. Their full-cell union \(U_w\) satisfies \(|U|\ge w|U_w|\). Apply the unrestricted discrete estimate with half the permitted error:
\[
 \begin{aligned}
 |U|&\ge c_\varepsilon w\delta^{6-D+\varepsilon/2}
             \left(\frac{\lambda}{wL}\right)^D\frac SL\\
 &=c_\varepsilon\delta^{6-D+\varepsilon/2}\lambda^DS
                   \frac{w^{1-D}}{L^{D+1}}\\
 &\ge c_\varepsilon\delta^{6-D+\varepsilon}\lambda^DS.
 \end{aligned}
\]
The last step uses \(w\le1\) and \(D>1\). No two-ends inheritance is required after this measurable density decomposition. This completes the argument for Theorem 1.1. \(\square\)

# References

1. T. H. Wolff, *An improved bound for Kakeya type maximal functions*, Revista Matemática Iberoamericana **11** (1995), 651–674, [DOI 10.4171/RMI/188](https://ems.press/content/serial-article-files/37888). Theorem 1 supplies the \(\mathbb R^5\) exponent \(7/2\) used in Lemma 2.1; its six-dimensional specialization supplies the assumed exponent \(4\).
2. N. H. Katz and T. Tao, *New bounds for Kakeya problems*, Journal d'Analyse Mathématique **87** (2002), 231–263; [arXiv:math/0102135](https://arxiv.org/pdf/math/0102135). Section 6 supplies the historical pivot, collision, lift, and energy architecture. Its saturated statement is not invoked as a proof of the arbitrary-density core here.

3. H. Wang and J. Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, [arXiv:2502.17655v1](https://arxiv.org/pdf/2502.17655v1), Lemma 7.8. The pointwise vector selection is adapted in Lemma 3.1 above.

