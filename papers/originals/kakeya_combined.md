---
title: "Kakeya maximal estimates via the Katz–Tao pivot argument"
date: "5 September 2026"
geometry: margin=24mm
fontsize: 11pt
---

\begin{center}\small Research draft\end{center}

## Abstract

We obtain Kakeya maximal estimates for arbitrary-density shadings by tracking the density loss in the Katz–Tao pivot argument. A six-dimensional model gives the implication \(\mathsf M_6(4)\Rightarrow\mathsf M_6(33/8)\); its lifted input follows from a Gaussian projection of a cap-four family in \(\mathbb R^7\) to \(\mathbb R^5\) and Wolff's maximal theorem. For a real direction-cap parameter \(m\), the common pivot estimate has set exponent \(D=(2m+3+d')/4\) and density exponent \(C=(p+2q+4)/4\). Angular normalization, sampling, and two-ends localization give the unrestricted estimate with density power \(\max(D,C)\). The envelope \(p_j(m)=\max\{d_j(m),4\}\) closes the real-cap recursion and yields the maximal exponent \(3+(2-\sqrt2)(n-4)\) for every integer \(n\ge6\), with an arbitrarily small scale loss. The set-exponent recursion and its limit are due to Katz and Tao; the estimates here retain explicit dependence on arbitrary shading density and tube number.

\tableofcontents
\clearpage

# 1. Statements and conventions

## 1.1. Maximal estimates and the main conclusions

A unit \(\delta\)-tube in \(\mathbb R^n\) is the \(\delta\)-neighborhood of a unit line segment. Tube directions are unoriented and \(c\delta\)-separated, with a fixed \(c>0\). Fixed changes in length, width, direction separation, and bounded-region normalization change only constants. Write \(\mathsf M_n(a)\) for the following assertion: for every \(\varepsilon>0\), every such family \(\mathcal T\), and all measurable shadings \(Y(T)\subset T\) with \(|Y(T)|\ge\lambda|T|\),
\[
 \left|\bigcup_{T\in\mathcal T}Y(T)\right|
 \ge c_\varepsilon\delta^{n-a+\varepsilon}\lambda^a
                   \sum_{T\in\mathcal T}|T|,
 \qquad 0<\delta,\lambda\le1.                         \tag{1.1}
\]
The constant is uniform in \(\delta,\lambda\), tube count, and tube positions. The arguments may be carried out in a fixed bounded region: assign each tube to one of the boundedly many unit spatial cubes meeting a fixed fraction of its shading, restrict to that fraction, and sum using bounded overlap. This reduction uses the linear dependence on tube number.

**Theorem 1.1.** For each integer \(n\ge6\), \(\mathsf M_n(D_n)\) holds, where
\[
 D_n=3+(2-\sqrt2)(n-4).
 \qquad
 D_6=7-2\sqrt2,\quad D_8=11-4\sqrt2.                 \tag{1.2}
\]
In particular, it gives the diagonal limits \(\mathsf M_6(29/7)\) and \(\mathsf M_8(37/7)\). All of these assertions have the quantifier “for every \(\varepsilon>0\)” in (1.1).

The proof begins with the six-dimensional transition
\(\mathsf M_6(4)\Rightarrow\mathsf M_6(33/8)\) in Section 2. Its lifted estimate is obtained by projection and uses only Wolff's five-dimensional maximal theorem. The shared geometric and localization arguments are proved in Sections 3–8. Diagonal iteration with the fractional Wolff input converges to \((4n+5)/7\) in the dimensions treated in Section 9.1. The real-cap iteration in Section 9.2 uses the preceding stage as its lifted input and gives (1.2). The projection argument supplies the first six-dimensional transition; the later stages require the real-cap estimates proved in Section 4.

Katz and Tao's survey [KT00, p. 14] already records \((4n+5)/7\) as a Hausdorff bound. Their real direction-cap framework, pivot construction, and scalar recursion in [KT02, Section 6] give the limiting set exponent in (1.2). The distinction here is the dependence on arbitrary shading density and on tube number. In one pivot invocation the density power is \((p+2q+4)/4\); the exponent \(q\) includes all costs in the chosen lifted input. The recursive argument must therefore bound this power at every stage. Section 9.2 does so with the envelope \(p_j(m)=\max\{d_j(m),4\}\).

Appendix B compares (1.2) with the specific maximal bounds of Hickman–Rogers–Zhang and Zahl. In dimension eight the first value \(21/4\) equals their benchmark. The numerical limit in (1.2) exceeds those benchmarks in some dimensions and falls below them in others.

## 1.2. A real cap parameter in an integer ambient space

Let \(k\) be the actual integer ambient dimension, let \(m>3\) be real with \(m\le k-1\), and put \(\delta=N^{-1}\). In finitely many fixed projective direction charts assume
\[
 \#\{T:\operatorname{dir}(T)\in B(v,r)\}
 \le A(Nr)^m,\qquad \delta\le r\le1,
 \qquad A\ge1.                                      \tag{1.3}
\]
Directions are also \(c\delta\)-separated in the actual ambient direction sphere. Condition (1.3) does not require them to lie on an \(m\)-dimensional submanifold. Every ambient space used below has integer dimension; the lift from \(\mathbb R^k\) lies in \(\mathbb R^{k+1}\).

A discrete shading is a set of cells in a common \(\delta\)-grid, with centers within \(C\delta\) of its tube. Each tube has at most \(C_*N\) admissible cells and at most a fixed number in any longitudinal interval of length \(\delta\). We permit fixed grid and tube enlargements. By a fixed-factor adjustment of width, take \(\delta=2^{-J}\) and use aligned dyadic spatial grids. Localization radii are then dyadic multiples of \(\delta\), so each localization cube is a union of original cells. After rescaling, a further fixed-factor normalization restores this convention when needed. Write
\[
 M=\#\mathcal T,\qquad E=\#\bigcup_TY(T),\qquad
 L=\log(2N).
\]
We use cardinality for discrete unions and Lebesgue measure for measurable unions, specifying the normalization when both occur. A full shading \(Y(T)\) may contain a smaller marked shading \(G(T)\); density and two ends refer to the full shading unless specified otherwise.

A full shading has two ends with exponent \(\alpha>0\) and constant \(B\) if
\[
 |Y(T)\cap B(x,r)|\le Br^\alpha|Y(T)|,
 \qquad \delta\le r\le1.
\]
For a discrete shading this inequality counts cell centers. Auxiliary positive exponents are fixed before \(N\) varies. Powers denoted by \(L^{O(1)}\) depend only on these fixed parameters and may be absorbed into an arbitrarily small prescribed power of \(N\).


For \(3<d<m\) and \(p\ge d\), let \(K(m,d,p)\) mean that, in every fixed integer ambient dimension \(k\ge m+1\), for every \(\varepsilon>0\), discrete shadings of comparable nonzero cardinality \(\lambda N\) obey
\[
 E\ge c_{k,m,d,p,\varepsilon}
       A^{-1}N^{d-m-\varepsilon}\lambda^pM.           \tag{1.4}
\]
The constants may depend on the fixed geometric normalizations; they are independent of \(A,N,\lambda,M\), and positions. For nonempty discrete shadings, \(\lambda\gtrsim N^{-1}\). An arbitrarily small extra density power can therefore be absorbed into an arbitrarily small scale loss. Densities above one and bounded by a fixed constant are normalized at fixed cost.

Multiplication by cell volume, followed by the measurable conversion of Section 8.1, gives the corresponding volume assertion
\[
 \left|\bigcup_TY(T)\right|
 \ge c_\varepsilon A^{-1}\delta^{m+1-d+\varepsilon}
       \lambda^p\sum_T|T|.                          \tag{1.5}
\]
Indeed, \(\sum_T|T|\asymp\delta^{k-1}M\) and \(\delta^kN^{d-m}=\delta^{m+k-d}\). Thus the formal parameter \(m+1\), rather than \(k\), appears in the scale loss in (1.5). For \(m=n-1\), \(k=n\), and \(p=d\), this is (1.1).

The unchanged-scale thinning in Section 4 retains at least \(cA^{-1}M\) whole tubes with an absolute cap coefficient. Apply it before imposing marks or broadness. It suffices thereafter to work with
\[
 S=M/N^m\lesssim1,
\]
and to restore the single factor \(A^{-1}\) at the end. The linear inverse coefficient matters when it grows with \(N\), as the example in Section 4.4 shows.

## 1.3. Cumulative density

**Corollary 1.1 (cumulative-density form).** Suppose an arbitrary-shading estimate, valid for every family satisfying a fixed cap condition with coefficient \(A\), has the form
\[
 \#U\ge cA^{-1}N^{b-m-\eta}\lambda^rM,
 \qquad r\ge1,
\]
for comparable nonzero discrete shading densities \(\lambda\). Then arbitrary shadings, including empty ones, of total incidence mass at least \(sNM\) satisfy
\[
 \#U\ge c_rcA^{-1}N^{b-m-\eta}
            \frac{s^rM}{\log(2N)}.                  \tag{1.6}
\]
If the comparable-density assertion holds with every positive scale loss and fixed \(r\), so does the cumulative-density assertion, with the same density power and no displayed logarithm.

**Proof.** Put \(\lambda_T=\#Y(T)/N\). Positive densities belong to \([1/N,C_*]\), where \(C_*\) is fixed. Delete tubes with \(\lambda_T<s/2\); they account for at most \(sNM/2\) incidences. Partition the remaining positive integer counts into bins \([2^j,2^{j+1})\). There are \(O(\log(2N))\) bins, and one bin, of size \(M_j\) and lower density \(\lambda_j=2^j/N\), satisfies
\[
 \lambda_j\ge s/4,
 \qquad \lambda_jM_j\ge\frac{c_*sM}{\log(2N)}.
\]
The first inequality follows from \(2\lambda_j>\lambda_T\ge s/2\). Consequently
\[
 \lambda_j^rM_j
 =\lambda_j^{r-1}(\lambda_jM_j)
 \ge\frac{c_rs^rM}{\log(2N)}.
\]
Apply the comparable-density estimate to this subfamily. Restriction preserves every cap bound, and its union is contained in the original union. If \(\lambda_j>1\), use the input at density one; since \(\lambda_j\le C_*\), this costs only a fixed constant. The proof also covers \(0<s<N^{-1}\): the number of bins is controlled by positive integer counts, independently of \(\log(1/s)\). Finally, use half the requested scale loss in the input and absorb the fixed logarithm into the other half. \(\square\)

In particular, \(K(m,d,p)\) implies
\[
 \#U\ge c_\varepsilon A^{-1}N^{d-m-\varepsilon}s^pM
 \quad\text{if}\quad \sum_T\#Y(T)\ge sNM.
\]
Applied to \(K(d,d',q)\), this supplies the lifted input after high-multiplicity restriction. It does not require comparable densities or two ends on the restricted lifted lines.

## 1.4. The recursive implication and proof structure

Theorem 5.1 is stated directly in terms of analytic base and lifted estimates. This allows inputs outside the narrower domain used to define \(K\), including the bush comparison in Appendix A. Within that domain, Corollary 8.2 gives
\[
 \begin{gathered}
 K(m,d,p),\quad K(d,d',q),\qquad
 3<d'<d<m,\quad p\ge d,\quad q\ge d',\\
 \Longrightarrow\quad K\bigl(m,D,\max(D,C)\bigr),\\
 D=\frac{2m+3+d'}4,
 \qquad C=\frac{p+2q+4}4.                           \tag{1.7}
 \end{gathered}
\]

Section 2 proves the projection estimate and explains the six-dimensional specialization of the common argument. Section 3 gives localization and angular decomposition, including the density and mark refinements. Section 4 proves the continuous hairbrush estimate and cap-preserving selection, then obtains the unrestricted cumulative seed. Section 5 contains the finite pivot, collision estimate, exact lifts, and energy argument. Sections 6–8 handle sampling, angular normalization, and removal of two ends. Section 9 applies the recursive implication and derives the maximal-operator estimates. Appendix A gives the bush comparison, and Appendix B compares the resulting exponents with the cited maximal bounds.

# 2. The six-dimensional model case

The six-dimensional argument uses one lifted estimate and one application of the pivot construction. Its lifted input follows directly from Wolff's five-dimensional maximal theorem by Gaussian projection. This gives a model for the density accounting in the general argument before introducing a real cap parameter.

Throughout this section, put \(\delta=N^{-1}\) and \(L=\log(2N)\). For a direction-separated family of \(M\) unit tubes in \(\mathbb R^6\), write \(S=M/N^5\lesssim1\). The estimates are uniform under the fixed geometric normalizations of Section 1.

## 2.1. The cap-four lifted input

**Lemma 2.1 (projection to five dimensions).** Let \(\mathcal L\) be a family of \(M\) direction-separated unit \(\delta\)-tubes in \(\mathbb R^7\) satisfying
\[
 \#\{\ell\in\mathcal L:\operatorname{dir}\ell\in B(v,r)\}
 \le A(Nr)^4,
 \qquad \delta\le r\le1,\quad A\ge1.
 \tag{2.1}
\]
For arbitrary discrete shadings, including empty shadings, with total incidence count at least \(sNM\), the union count satisfies, for every \(e>0\),
\[
 E_{\mathcal L}
 \ge c_e A^{-1}N^{-1/2-e}s^{7/2+e}M.
 \tag{2.2}
\]
The constant is independent of \(A,N,s,M\).

**Proof.** First suppose that every shading has cardinality comparable to \(sN>0\). Let \(P:\mathbb R^7\to\mathbb R^5\) be a standard Gaussian matrix. Choose a fixed large \(K\) and a fixed small \(c>0\). With probability bounded below, \(\|P\|\le K\) and at least \(M/2\) of the unit direction vectors satisfy \(|Pv|\ge c\). This follows from the operator-norm tail, the small-ball estimate for \(Pv\), and Markov's inequality applied to the number of directions with \(|Pv|<c\).

For projective directions at angle \(\psi\), choose representatives with
\[
 v'=\cos\psi\,v+\sin\psi\,w,\qquad w\perp v.
\]
The vectors \(Pv\) and \(Pw\) are independent standard Gaussian vectors in \(\mathbb R^5\). Conditional on \(Pv\), the component of \(Pw\) perpendicular to \(Pv\) is a four-dimensional standard Gaussian. On the event \(\|P\|\le K\), projected angular distance at most \(C\delta\) forces the norm of this component to be at most \(C_K\delta/\sin\psi\). Thus the probability of this collision together with \(\|P\|\le K\) is bounded by
\[
 C_K\min\{1,(\delta/\psi)^4\}.
 \tag{2.3}
\]
Summing over dyadic angular annuli and using (2.1), the expected number of ordered collisions is at most \(CAM L\). A sufficiently large Markov cutoff can be imposed simultaneously with the preceding positive-probability event. We therefore obtain a bounded map \(P\), at least \(M/2\) good directions, and at most \(CAM L\) collisions.

The collision graph on the good directions has an independent set of size at least \(cM/(AL)\). To see this, a graph with \(V\) vertices and \(e\) edges has an independent set of size at least \(V^2/(V+2e)\): randomly order the vertices, keep those preceding all their neighbors, and apply Cauchy--Schwarz to the expected size \(\sum_v(\deg(v)+1)^{-1}\). The independent set gives projected directions separated at scale \(\delta\).

Each original cell has image covered by \(O_K(1)\) target \(\delta\)-cells, so the projected union count \(E'\) is at most \(CE_{\mathcal L}\). On a good tube, a target cell restricts the original longitudinal parameter to an interval of length \(O_{c,K}(\delta)\). Hence only \(O_{c,K}(1)\) original shading cells can collapse to one target cell. The selected projected tubes retain density comparable to \(s\); their lengths are bounded above and below by fixed positive constants. Wolff's five-dimensional maximal estimate [W95, Theorem 1] therefore gives
\[
 E'\ge c_\eta N^{-1/2-\eta}s^{7/2}\frac{M}{AL}.
 \tag{2.4}
\]
Fixed changes in projected tube length and width affect only the constant.

For cumulative density, discard tubes with density below \(s/2\), losing at most half the total incidence mass. Among the \(O(L)\) dyadic bins of positive integer shading counts, one has size \(M_j\) and lower density \(s_j\) satisfying
\[
 s_j\ge s/4,
 \qquad s_jM_j\ge csM/L.
\]
It follows that \(s_j^{7/2}M_j\ge cs^{7/2}M/L\). Apply (2.4) to this bin. Positive densities range from \(1/N\) to a fixed constant, so the bin count is still \(O(L)\) when \(s<1/N\). Densities above one are normalized at fixed cost. Absorb both logarithms by choosing \(\eta<e\), and weaken \(s^{7/2}\) to \(s^{7/2+e}\). This proves (2.2). \(\square\)

The projection uses the integer cap exponent four in the actual ambient space \(\mathbb R^7\). It supplies all the lifted input needed for the model case.

## 2.2. The transverse estimate and its globalization

**Theorem 2.2 (six-dimensional model).** The implication
\[
 \mathsf M_6(4)\quad\Longrightarrow\quad\mathsf M_6(33/8)
 \tag{2.5}
\]
holds. In particular, Wolff's six-dimensional estimate gives, for arbitrary measurable shadings of density at least \(\lambda\),
\[
 \left|\bigcup_TY(T)\right|
 \ge c_\varepsilon\delta^{15/8+\varepsilon}
       \lambda^{33/8}S.
 \tag{2.6}
\]

**Proof.** We specialize the common pivot theorem and reductions proved in Sections 5--8. The parameter choices are
\[
 k=6,\qquad m=5,\qquad d=p=4,
 \qquad d'=q=\frac72.
 \tag{2.7}
\]
We use Theorem 5.1 in its fixed-ambient analytic form. Its base input (5.4) is \(\mathsf M_6(4)\), applied in \(\mathbb R^6\) to full-cell shadings at every coarser scale. Lemma 2.1 supplies the cumulative lifted input (5.5) in \(\mathbb R^7\), with its linear inverse cap coefficient. In particular, the six-dimensional base estimate is not being used as an all-ambient assertion \(K(5,4,4)\).

To state the quantitative specialization, let full discrete shades have comparable cardinality \(\lambda N\) and two ends with exponent \(0<\alpha\le1\) and constant \(B\). Suppose their marked incidence mass is at least \(\xi\lambda NM\), and each projective cap of radius \(\theta\) contains at most one tenth of the marks at every marked cell. With
\[
 \kappa=c\min\{\theta,1/100,(c/B)^{1/\alpha}\},
\]
Theorem 5.1 gives, for \(0<e<1\) and sufficiently large \(N\kappa^{20}\),
\[
 E^4\ge c_e\kappa^{58}\xi^7L^{-8}
       N^{33/2-3e}\lambda^{15+2e}S^3.
 \tag{2.8}
\]
Indeed, its conditioning exponent is
\[
 H_6=5(6-1)+6(7/2)+12=58.
\]
The scale and density exponents after taking fourth roots are
\[
 D=\frac{2m+3+d'}4=\frac{33}{8},
 \qquad C=\frac{p+2q+4}4=\frac{15}{4}.
 \tag{2.9}
\]
For fixed \(\alpha\) and \(B,\xi^{-1},\theta^{-1}\) bounded by fixed powers of \(L\), (2.8) consequently implies, for every \(\eta>0\),
\[
 E\ge c_\eta N^{33/8-\eta}
       \lambda^{15/4+\eta}S^{3/4}.
 \tag{2.10}
\]
The exponents are independent of the fixed choice of \(\alpha\).

The density gain in this specialization can be read directly from the proof of the common core. A selected angle-output fiber has normalized size \(\sigma\gtrsim\lambda^2\). The collision and lifted-energy estimates leave the factor
\[
 \lambda^6\sigma^{q+e-2}
 =\lambda^6\sigma^{3/2+e}
 \gtrsim\lambda^{9+2e}.
\]
The angle count supplies \(\lambda^2\), while the inverse pruning coefficient supplies \(\lambda^4\). Together they give \(\lambda^{15+2e}\) in (2.8).

We next remove angular concentration. The full-direction continuous hairbrush (4.23), proved before the fractional thinning argument, specializes at \(k=6,m=5\) to
\[
 \left|\bigcup_T Z(T)\right|
 \ge cL^{-P_0}\delta^2\sigma^2
       \bigl(\delta^5\#\mathcal T\bigr)
\]
for some fixed logarithmic exponent \(P_0\). It has set parameter \(w=(m+3)/2=4\) and density power two. The hypotheses of Proposition 7.1 hold because
\[
 1<D<5,\qquad C>2,\qquad
 w-D+\frac{C-2}{3}
 =-\frac18+\frac{7}{12}=\frac{11}{24}>0.
 \tag{2.11}
\]
Thus arbitrary-angular discrete shadings with fixed two ends satisfy
\[
 E\ge c_\eta N^{33/8-\eta}\lambda^{15/4}S.
 \tag{2.12}
\]

Here is the angular-scale accounting in this case. Choose broadness exponent \(\beta=1/4\). For a piece of angular radius \(\tau\), put \(R=N\tau\) and \(S'=M_j/R^5\). If \(E_j\) denotes its occupied-cell count in the original grid and \(E_j^{\mathrm s}\) the count produced by sampling after transverse rescaling, then
\[
 E_j^{\mathrm s}\le\#\mathcal Q_j\le CE_j,
\]
where \(\mathcal Q_j\) is the set of new cells meeting the transformed full shading. The transformed normalized measurable volume is instead comparable to \(\tau E_j\). These comparisons are proved in Section 7. Its low-density branch has the favorable scale margin \(11/24\) in (2.11), while its sampling branch transfers (2.10) to the original count through the displayed cell-count inequality. Since \(S'\lesssim1\), the factor \((S')^{3/4}\) may be weakened to a constant times \(S'\). Summing original piece counts with their overlap \(O(\tau^{-1/4})\) leaves the factor
\[
 \tau^{D-5+1/4-\eta}=\tau^{-5/8-\eta}\ge1.
 \tag{2.13}
\]
This explains the strict condition \(D<5\) in the angular step.

Finally apply Proposition 8.1. The localized old density \(\nu\) and radius \(\rho\) satisfy \(\nu\lesssim\rho\) and \(\nu\gtrsim L^{-A}\rho^\alpha\lambda\). Since
\[
 D-C=\frac38>0,
 \qquad \nu^C\rho^{D-C}\gtrsim\nu^D,
\]
localization changes the density exponent from \(C=15/4\) to \(D=33/8\). Choose \(\alpha\) after fixing the final scale-loss budget, then absorb the fixed logarithmic losses. Proposition 8.1 also performs the occupancy decomposition for arbitrary measurable shadings; its density factor \(w^{1-D}\) is at least one for \(0<w\le1\). Multiplying the resulting discrete count by \(\delta^6\) proves (2.6). The initial input \(\mathsf M_6(4)\) follows from [W95, Theorem 1]. \(\square\)

For this model, the coarse direction selections in Sections 5 and 8 can be made by ordinary coloring in \(\mathbb R^6\). At direction scale \(r\ge\delta\), the conflict graph has degree \(O((Nr)^5)\); a largest color retains \(\gtrsim M/(Nr)^5\) tubes, and its \(r\)-separation automatically gives the full cap bound \(O((u/r)^5)\) for \(u\ge r\). After localization to radius \(\rho\), the corresponding degree is \(O(\rho^{-5})\), so one color retains \(\gtrsim\rho^5\) of the tubes. These choices replace the general cap-preserving thinning steps; the original full-direction cap coefficient is already absolute. Thus the model uses the full-direction hairbrush and the projection input of Lemma 2.1, without requiring a fractional lifted seed. The following sections prove the shared construction in the more general form needed for iteration.

# 3. Localization and angular decomposition

Throughout this section the ambient space is $\mathbb R^k$, $\delta=N^{-1}$, and $L=\log(2N)$.

## 3.1. Smallest-scale localization

**Lemma 3.1 (Wolff two-ends localization).** For a discrete shading of density comparable to $\lambda$ and a fixed $0<\alpha<1/2$, there is a subfamily retaining a fraction $cL^{-2}$ of the tubes, a common dyadic radius $\rho$, and restrictions $Y_1(T)$ of common original density $\nu$, such that $$\nu\gtrsim\rho^\alpha\lambda,\qquad
 \nu\lesssim\rho,
 \tag{3.1}$$ and each restriction is supported in a $\rho$-ball and obeys two ends relative to that radius with a fixed constant. The same assertion holds for measurable shadings at scales at least $\delta$.

**Proof.** For each tube choose the smallest dyadic $r_T\in[\delta,1]$ for which some ball contains at least $r_T^\alpha$ of its shading. A fixed enlargement of the top scale guarantees existence. Restrict to such a ball. At every smaller radius $r<r_T/2$, minimality and dyadic rounding give $$|Y_1(T)\cap B(x,r)|
 \le 2^\alpha(r/r_T)^\alpha |Y_1(T)|.$$ For $r_T/2\le r\le r_T$ the estimate is trivial with a fixed constant. Tube geometry gives $|Y_1(T)|\lesssim r_T\delta^{k-1}$, while the defining lower bound gives $|Y_1(T)|\gtrsim r_T^\alpha\lambda\delta^{k-1}$. Pigeonhole first the radius, then the retained density; each has $O(L)$ possible classes. This proves the lemma. Restriction to one of the boundedly many $\rho$-grid cubes meeting the chosen ball retains a fixed fraction and preserves the relative two-ends inequality. $\square$

## 3.2. A broadness decomposition with adjustable overlap

The following angular decomposition extends the vector-selection argument of Wang--Zahl, Lemma 7.8, and their restricted-shading decomposition in dimension three, Corollary 7.10.

A finite direction set $V$ in a cap of radius $\tau$ is broad with exponent $\beta>0$ and error $K$ if $$\#(V\cap B(v,r))\le K(r/\tau)^\beta\#V,
 \qquad \delta\le r\le\tau.
 \tag{3.2}$$ At larger radii the inequality is interpreted with a harmless constant. Directions may be treated in finitely many fixed projective charts.

**Lemma 3.2 (angular decomposition).** Fix $0<\beta\le1$. For direction-separated tubes with arbitrary shadings there are a common angular scale $\tau\in[\delta,1]$, disjoint assigned tube families $\mathcal T_j$, and restricted shadings $Y_j(T)$, with the following properties. Each family lies inside one $O(\tau)$-tube and has directions in an $O(\tau)$-cap. The retained incidence mass is at least $cL^{-3}$ of the original mass. The unions $U_j$ have pointwise overlap at most $C\tau^{-\beta}$. At every point of each $U_j$, the retained directions there obey (3.2) with a fixed error. For discrete input all choices can be made constant on every original cell.

**Proof.** First consider a finite direction set $V$. On the remaining set greedily maximize $r^{-\beta}\#(V_{\rm rem}\cap B(v,r))$, with $\delta\le r\le1$. Retain the subset $W$ in the maximizing cap, delete the remaining directions in its $100$-fold enlargement, and stop after deleting at least half of the original directions. Maximality gives internal broadness, and comparison with a fixed radius-one covering of the direction sphere gives $$\#W\ge c_k r^\beta\#V.$$ The number deleted at that step is at most $C_k100^\beta\#W\le C_k100\#W$, using the same maximizing property, or a radius-one cover when $100r>1$. Thus the total retained size before radius pigeonholing is at least $c_k\#V$. One dyadic radius class retains at least $c_kL^{-1}\#V$. Enlarge its radii by at most two. The selected subsets remain disjoint, are broad with fixed error in radius-$\tau$ caps, and each has size at least $c_k\tau^\beta\#V$. Consequently at most $C_k\tau^{-\beta}$ such subsets occur. Geometric disjointness of the enlarged caps is unnecessary.

Apply this construction to the directions incident at each point. First pigeonhole the original incidence multiplicity, retaining $c_k/L$ of total incidence mass. Pointwise radius pigeonholing retains a further $c_k/L$, and choosing one common radius globally costs a further $O(L)$. The retained mass is therefore at least $c_kL^{-3}$ of the original mass. All choices are deterministic functions of the finite incidence set, so they are measurable and constant on grid cells for discrete input.

Choose a bounded-overlap global covering by caps of radius $3\tau$, assigning each pointwise cap to one containing global cap. At a point, the direction subsets assigned to different global caps remain disjoint. Unions of subsets broad at the same scale remain broad, by summing (3.2). Each direction belongs to at most $C_k$ global caps. Assign every tube to the cap retaining the largest portion of its shading; this loses at most $C_k$ in total mass. This assignment can spoil pointwise broadness. In each cap retain only points where the assigned subset contains at least $1/(4C_k)$ of the former subset. The discarded mass is at most one quarter of the post-assignment mass, by summing that proportional threshold. The retained directions are broad with a changed fixed error.

For a cap centered at $v$, use parallel covering tubes whose axes form a $2\tau$-lattice in $v^\perp$, with width $C_k\tau$. Every original tube assigned to the cap is contained in one covering tube; assign it to one such cover. At any fixed point, at most $C_k$ assigned cover tubes can occur, since their lattice axes lie within $C_k\tau$ of the line through that point parallel to $v$. As before, retain a point in a spatial piece only when its incidence subset is at least $1/(4C_k)$ of the parent cap subset. This loses at most one quarter of the remaining mass and preserves broadness with a fixed error. Each tube is now assigned once.

At a point at most $C_k\tau^{-\beta}$ original pointwise cap subsets could occur. Each gives at most $C_k$ spatial covering pieces. This proves the asserted overlap, with no power of $\delta$ beyond $\tau^{-\beta}$. $\square$

## 3.3. Restoring density and a marked broad set

Assume the input shadings satisfy $c_0\sigma\delta^{k-1}\le |Y^{\mathrm{in}}(T)|\le C_0\sigma\delta^{k-1}$, with two-ends constant $B_0L^b$. Apply Lemma 3.2 with fixed $0<\beta\le1$. Its output consists of a common angular radius $\tau$, disjoint assigned tube families $\mathcal T_j$, caps and containing tubes at scale $\tau$, and restricted shadings $Y_j(T)\subset Y^{\mathrm{in}}(T)$. In this subsection only, write $Y(T)=Y_j(T)$ for a tube assigned to piece $j$. These restricted shadings satisfy

$$W:=\sum_j\sum_{T\in\mathcal T_j}|Y(T)|
 \ge\kappa I,
 \qquad I:=\sum_T|Y^{\mathrm{in}}(T)|,
 \qquad \kappa=cL^{-3}.
\tag{3.3}$$

The unions $U_j=\bigcup_{T\in\mathcal T_j}Y(T)$ have pointwise overlap at most $C\tau^{-\beta}$. If

$$m_j(x)=\#\{T\in\mathcal T_j:x\in Y(T)\},$$

then their directions obey

$$\#\{T\in\mathcal T_j:x\in Y(T),\ \operatorname{dir}(T)\in B(v,r)\}
 \le K_0(r/\tau)^\beta m_j(x)
\tag{3.4}$$

at scales $\delta\le r\lesssim\tau$, with dimensional $K_0$; larger radii are trivial after changing $K_0$. We refine these pieces to retain density on every surviving tube and broadness on a marked subset.

**Step 1: discard tubes with too little retained density.** Put $a=\kappa/8$. Delete $T$ if $|Y(T)|<a|Y^{\mathrm{in}}(T)|$. Let $\mathcal T_j^*$ be the surviving family in piece $j$. Its total deleted incidence mass $D$ obeys

$$D\le aI\le W/8.
\tag{3.5}$$

Every surviving tube obeys

$$ac_0\sigma\delta^{k-1}\le |Y(T)|\le C_0\sigma\delta^{k-1}.
\tag{3.6}$$

Its two-ends inequality has constant at most $a^{-1}B_0L^b$, because

$$|Y(T)\cap B(x,r)|\le |Y^{\mathrm{in}}(T)\cap B(x,r)|
 \le B_0L^b r^\alpha |Y^{\mathrm{in}}(T)|
 \le a^{-1}B_0L^b r^\alpha |Y(T)|.
\tag{3.7}$$

These losses are powers of $L$ only.

**Step 2: reset the good set after this deletion.** Write

$$m_j^*(x)=\#\{T\in\mathcal T_j^*:x\in Y(T)\},
 \qquad G_j=\{x:m_j^*(x)\ge m_j(x)/2\}.$$

Outside $G_j$, one has $m_j^*\le m_j-m_j^*$. Consequently the total surviving incidence mass outside these good sets is

$$R:=\sum_j\int_{G_j^c}m_j^*(x)\,dx
 \le\sum_j\int(m_j-m_j^*)\,dx=D.
\tag{3.8}$$

Let $I_j^*=\int m_j^*$ and $W_j^*=\int_{G_j}m_j^*$. Then

$$\sum_j W_j^*\ge W-D-R\ge W-2D\ge3W/4.
\tag{3.9}$$

At a good point the surviving direction set contains at least half the original directions, so (3.4) holds there with $2K_0$ in place of $K_0$.

**Step 3: retain pieces with a substantial good mass.** Keep pieces with $W_j^*\ge I_j^*/2$. On a rejected piece, $W_j^*<I_j^*-W_j^*$, so the sum of its good mass is at most $R$. Hence

$$\sum_{j\text{ retained}}W_j^*
 \ge W-2D-R\ge W-3D\ge5W/8.
\tag{3.10}$$

Each retained piece has good mass at least half its surviving incidence mass, has the per-tube density range (3.6), has the two-ends bound (3.7), and is broad on its good set with constant $2K_0$. Its union remains inside $U_j$, so the original overlap bound is preserved.

The hairbrush proof in Section 4 allows a density interval $[\lambda,\Lambda]$ with $\Lambda/\lambda\lesssim L^3$, so it applies directly to (3.6). When comparable densities are required, select a density class by marked mass and repeat the proportional-point restriction above. The retained marked fraction is then an inverse power of $L$. Section 7 carries out this additional refinement before applying the sampling lemma.

# 4. A fractional direction-cap hairbrush

## 4.1. Cap conditions and the continuous two-ends statement

Fix an integer ambient dimension $k\ge3$, a real $1<m\le k-1$, a direction separation constant, and fixed upper and lower tube length constants. Put $\delta=N^{-1}$, $L=\log(2N)$. A family of unit $\delta$-tubes satisfies the $m$-dimensional cap condition with constant $A\ge1$ if

$$\#\{T:\operatorname{dir}(T)\in B(v,r)\}\le A(Nr)^m,
 \qquad \delta\le r\le1.
\tag{4.1}$$

Fixed changes in $A$, $\delta$, and the direction separation constant are permitted. For measurable shadings, normalized volume means physical volume divided by $\delta^k$. It agrees with occupied-cell cardinality when the shading is a union of full grid cells.

We first prove a continuous estimate under unit two ends. For every fixed $\alpha>0$, $b\ge0$, $B_0\ge1$, and comparable-density constant $C_0$, there exist $c>0$ and finite $P\ge0$ such that, whenever

$$c_0\sigma\delta^{k-1}\le |Z(T)|\le C_0\sigma\delta^{k-1},
 \qquad 0<\sigma\le1,
\tag{4.2}$$

and

$$|Z(T)\cap B(x,r)|\le B_0L^b r^\alpha |Z(T)|,
 \qquad \delta\le r\le1,
\tag{4.3}$$

one has

$$\frac{|\bigcup_T Z(T)|}{\delta^k}
 \ge cL^{-P}A^{-1/2}N^{(3-m)/2}\sigma^2\#\mathcal T.
\tag{4.4}$$

The constants $c,P$ may depend on $k,m,\alpha,b,B_0,c_0,C_0$ and the fixed geometric constants. They do not depend on $N,\sigma,A$, the number of tubes, or their positions. The powers $(3-m)/2$ and $2$ are independent of $\alpha$; no boundedness of the constants as $\alpha\downarrow0$ is needed.

The same conclusion allows upper/lower density ratios bounded by a fixed power of $L$; this changes $P$ only. Tubes may first be placed in finitely enlarged unit cubes and the resulting estimates summed with bounded overlap. Thus it suffices to prove everything in one fixed ball.

## 4.2. Proof of the continuous broad hairbrush

Consider $\delta$-tubes with $\delta$-separated directions in a fixed ball, and shadings $Y(T)$ satisfying

$$\lambda\delta^{k-1}\le |Y(T)|\le\Lambda\delta^{k-1},
 \qquad |Y(T)\cap B(x,r)|\le B r^\alpha |Y(T)|.
\tag{4.5}$$

Assume there is a measurable $G$ carrying good mass

$$W_G:=\sum_T|Y(T)\cap G|\ge\frac12\sum_T|Y(T)|,
\tag{4.6}$$

and that, on $G$, the directions through $x$ have broadness constant $K$ and exponent $\beta$ at unit angular scale. Set

$$\theta=(C K)^{-1/\beta},\qquad
 r_0=(C B L)^{-1/\alpha},
\tag{4.7}$$

where $C$ is a sufficiently large dimensional constant. We prove

$$|U|\ge c(r_0\theta)^{(k-1)/2}L^{-5/2}
 \bigl(W_G\lambda^3\delta^{k-2}\bigr)^{1/2},
 \qquad U=\bigcup_TY(T).
\tag{4.8}$$

First assume $r_0\theta\ge C\delta$. The complementary range when $B,K$ are logarithmic is handled at the end of this section. In the nondegenerate range $\theta\ge\delta$, and the broadness inequality for a $\theta$-cap centered at any one of the marked directions forces the multiplicity at that point to be at least C. Taking $C$ large at the outset makes all multiplicities used below larger than $100$.

**Multiplicity and a stem.** Direction separation bounds the full multiplicity by $C\delta^{-(k-1)}$. Select a dyadic $\mu$ and a set

$$X=\{x\in G:\mu\le m(x)<2\mu\}$$

carrying at least $cW_G/L$ incidences. Thus

$$|U|\ge cW_G/(L\mu).
\tag{4.9}$$

Put $Y_1(T)=Y(T)\cap X$, and retain tubes with $|Y_1(T)|\ge |Y(T)|/(CL)$. Choosing $C$ large enough, the deleted $Y_1$-mass is at most half the mass on $X$, by (4.6). Let $X'$ consist of points of $X$ lying in at least $c\mu$ retained tubes. Discarding $X\setminus X'$ costs at most another fixed fraction. Averaging over retained tubes gives a stem $T_0$ such that

$$|Y_1(T_0)\cap X'|\ge c|Y_1(T_0)|
 \ge c\lambda\delta^{k-1}/L.
\tag{4.10}$$

At each such point the original broadness bound makes at most $\mu/100$ directions lie within angle $\theta$ of the stem; retained multiplicity is at least $c\mu$, with constants chosen in that order. Hence transverse stem--bristle incidences have total volume at least $c\mu\lambda\delta^{k-1}/L$. Two $\delta$-tubes meeting at angle $\psi$ have intersection volume at most $C\delta^k/\max\{\psi,\delta\}$. Dividing by this bound for $\psi\ge\theta$ gives a family $H$ of bristles satisfying

$$\#H\ge c\mu\lambda\theta/(\delta L).
\tag{4.11}$$

**Remove the part near the stem.** Choose $p_T\in Y_1(T)\cap Y_1(T_0)\cap X'$. The refinement from $Y$ to $Y_1$ increases the two-ends constant by at most $CL$. Thus, by (4.7), deletion of $B(p_T,r_0)$ removes at most a fixed small fraction of $Y_1(T)$. The remaining shading $Y_2(T)$ has volume at least $c\lambda\delta^{k-1}/L$ and distance at least $cr_0\theta$ from the stem axis. The assumption $r_0\theta\ge C\delta$ absorbs the tube-axis errors.

**Partition into plane bins.** A bristle meeting $T_0$ lies within $C\delta$ of the plane through the stem axis parallel to its direction. Such planes are parametrized by a projective $(k-2)$-sphere. Choose a $\delta$-separated net, assign each bristle to its nearest plane, and thicken that plane by $C\delta$ inside the fixed ball. At a point of distance $s\ge cr_0\theta$ from the stem, the number of these planks is at most $Cs^{-(k-2)}\le C(r_0\theta)^{-(k-2)}$. Therefore

$$\left|\bigcup_{T\in H}Y_2(T)\right|
 \ge c(r_0\theta)^{k-2}\sum_j|U_j|,
\tag{4.12}$$

where $U_j$ is the union in plane bin $j$.

**The planar intersection sum.** Directions in one bin lie within $C\delta$ of a fixed great circle. Within a cap of radius $\psi\ge\delta$, a $\delta$-separated subset of this thickened circle contains at most $C\psi/\delta$ directions. Indeed the relevant part is covered by $O(\psi/\delta)$ spherical $\delta$-balls; its transverse thickness is $C\delta$ in each of the $k-2$ normal directions. Thus, for each bristle $T$ in a fixed bin,

$$\sum_{T'\text{ in the bin}}|T\cap T'|
 \le C\delta^{k-1}
 +\sum_{\psi\text{ dyadic}}C(\psi/\delta)(\delta^k/\psi)
 \le C L\delta^{k-1}.
\tag{4.13}$$

Cauchy--Schwarz and $|Y_2(T)|\ge c\lambda\delta^{k-1}/L$ yield

$$|U_j|\ge c\lambda^2\delta^{k-1}\#H_j/L^3.
\tag{4.14}$$

The transverse packing costs a dimensional constant: its angular thickness at this stage is $O(\delta)$.

**Combine the two estimates.** Summing (4.14), using (4.11)--(4.12), gives

$$|U|\ge c(r_0\theta)^{k-2}\theta
 \mu\lambda^3\delta^{k-2}/L^4.
\tag{4.15}$$

Take the geometric mean with (4.9). The resulting factor is $(r_0\theta)^{(k-2)/2}\theta^{1/2}$, which is at least $(r_0\theta)^{(k-1)/2}$ since $r_0\le1$. This proves (4.8).

Now impose the cap condition (4.1). Its radius-one case gives $\#\mathcal T\le CA\delta^{-m}$. Since $W_G\le C\Lambda\delta^{k-1}\#\mathcal T$, one has

$$W_G^{1/2}\ge cA^{-1/2}\Lambda^{-1/2}
 \delta^{(m-k+1)/2}W_G.$$

Consequently (4.8) gives the linear estimate in the marked incidence mass

$$|U|\ge c(r_0\theta)^{(k-1)/2}L^{-5/2}
 A^{-1/2}\delta^{(m-1)/2}
 \lambda^{3/2}\Lambda^{-1/2}W_G.
\tag{4.16}$$

We sum (4.16) over the refined pieces from Section 3.3.

**Logarithmic dependence and coarse scales.** If $B\le B_1L^b$ and $K\le K_1L^q$, then

$$(r_0\theta)^{(k-1)/2}L^{-5/2}
 \ge c L^{-P_0},
 \quad
 P_0=\frac{k-1}{2}\left(\frac{b+1}{\alpha}+\frac q\beta\right)+\frac52.
\tag{4.17}$$

Here $c$ can depend on $\alpha,\beta,B_1,K_1$. If $\lambda=\sigma L^{-u}$, that adds $3u/2$ to the logarithmic exponent in (4.16); a retained mass loss $L^{-v}$ adds $v$. The choices of $r_0,\theta$ are independent of the density.

If $r_0\theta<C\delta$, these logarithmic bounds force $N$ to be bounded by a fixed power of $L$, with constants depending on the fixed parameters. Direction separation then bounds $\#\mathcal T$ by a fixed power of $L$. The elementary inequality $|U|\ge W_G/\#\mathcal T$ proves (4.16) with a larger logarithmic loss, since $A^{-1/2}\delta^{(m-1)/2}\lambda^{3/2}\Lambda^{-1/2}\lesssim1$. This also covers a coarse eccentricity $N'$ bounded by a fixed power of the original $L$, including when $\log(2N')$ is much smaller than $L$.

## 4.3. Continuous angular normalization

Choose

$$0<\beta<\min\{1,(m-1)/2\},
\tag{4.18}$$

for example $\beta=\min\{1/2,(m-1)/4\}$. Apply Lemma 3.2 and Section 3.3. In a retained piece, dilate the coordinates perpendicular to the cap center by $\tau^{-1}$. A fixed final normalization changes only constants. The new width is $\delta'\asymp\delta/\tau$, and directions are separated at that scale. In the gnomonic chart of the original cap the map is multiplication by $\tau^{-1}$; this chart and radial projection on the bounded image chart are uniformly bi-Lipschitz. A new cap of radius $r$ thus pulls back into a cap of radius $C\tau r$, giving

$$\#\{T':\operatorname{dir}(T')\in B(v,r)\}
 \le C A(N\tau r)^m.
\tag{4.19}$$

The cap coefficient is $O(A)$. The spatial determinant is $\tau^{-(k-1)}$. Tube length changes by a bounded factor, and tube and shading volumes acquire that common determinant up to fixed factors. Hence the density interval remains $[c\kappa\sigma,C\sigma]$. The inverse map is a contraction, so a new radius-$r$ ball pulls back inside an old radius-$r$ ball. Since $r\ge\delta'\gtrsim\delta$, two ends applies with $B'\le C\kappa^{-1}B_0L^b$. Marked mass and angular broadness also survive, with fixed constants after normalization.

Let $V_j,W_j$ be old physical union volume and good incidence volume, and $V_j',W_j'$ the transformed quantities. Apply (4.16), using the original $L$ to bound all smaller multiplicity logarithms. It gives

$$V_j'\ge cL^{-P} A^{-1/2}(\delta/\tau)^{(m-1)/2}
 \sigma W_j'.
\tag{4.20}$$

The factor $\kappa^{3/2}$ from $\lambda^{3/2}\Lambda^{-1/2}$ is included in $L^{-P}$. If $N\tau$ is below the parameter-dependent logarithmic threshold, the coarse-scale argument of Section 4.2 gives the same conclusion with a larger $P$. Thus no lower comparison between $\log(2N\tau)$ and $\log(2N)$ is needed.

Undo the common determinant in $V_j'$ and $W_j'$:

$$V_j\ge cL^{-P} A^{-1/2}\delta^{(m-1)/2}
 \tau^{-(m-1)/2}\sigma W_j.
\tag{4.21}$$

Use the union overlap at most $C\tau^{-\beta}$, and sum (4.21). By (3.3), (3.10), and the original density lower bound,

$$\begin{aligned}
 |\bigcup_T Z(T)|
 &\ge c\tau^\beta\sum_{j\text{ retained}}V_j\\
 &\ge cL^{-P} A^{-1/2}\delta^{(m-1)/2}
 \tau^{\beta-(m-1)/2}\sigma\sum_jW_j\\
 &\ge cL^{-P-3} A^{-1/2}
 \delta^{(m-1)/2+k-1}\sigma^2\#\mathcal T.
 \end{aligned}
\tag{4.22}$$

The $\tau$-factor is at least one by (4.18). Dividing by $\delta^k$ proves (4.4).

Equivalently, normalized volume changes by $E'\asymp\tau E$, since the grid-volume normalization changes by $\tau^{-k}$. The local linear normalized bound acquires the factor $\tau^{(1-m)/2}$, consistently with (4.21). The argument uses continuous volumes throughout this rescaling.

For the specialization $m=k-1$ and $A=O(1)$, (4.4) is precisely the continuous all-angle unit-two-ends hairbrush

$$|\bigcup_T Z(T)|
 \ge cL^{-P}\delta^{(k-2)/2}\sigma^2
 \bigl(\delta^{k-1}\#\mathcal T\bigr).
\tag{4.23}$$

Section 7 uses the general estimate (4.4), including its logarithmic two-ends constants; (4.23) is its full-direction specialization.

## 4.4. Deterministic thinning and the fractional-direction estimate

**Lemma 4.1 (fractional-direction estimate).** Under the cap condition (4.1), arbitrary discrete shadings of cumulative density $\sigma$ satisfy (4.29). The constants are uniform for $A\ge1$.

**Lemma 4.2 (finite laminar selection).** Let a finite rooted tree partition a finite set $X$ at its leaves. Write $X_v$ for the elements below node $v$, and give every node an integer capacity $b_v\ge0$. If weights $0\le w_x\le1$ satisfy $$\sum_{x\in X_v}w_x\le b_v\qquad\text{for every node }v,$$ there is a subset $J\subset X$ with $\#(J\cap X_v)\le b_v$ at every node and $\#J\ge\sum_{x\in X}w_x$.

**Proof.** Define integers recursively by $$R_v=\min\{b_v,\#X_v\}\quad\text{at a leaf},\qquad
 R_v=\min\left\{b_v,\sum_{u\text{ child of }v}R_u\right\}
 \quad\text{at an internal node}.$$ Inductively construct a subset $J_v\subset X_v$ of exactly $R_v$ elements satisfying every capacity in that subtree. At a leaf this is immediate. At a parent, take the union of the already constructed child subsets and delete arbitrary elements until exactly $R_v$ remain. Deletion cannot violate a descendant's upper capacity, and the definition of $R_v$ enforces the parent's capacity.

For any feasible weight vector, its mass $W_v=\sum_{x\in X_v}w_x$ is at most $R_v$. At a leaf use both $W_v\le b_v$ and $W_v\le\#X_v$. At a parent use $W_v\le b_v$ and, by the child induction, $W_v=\sum_uW_u\le\sum_uR_u$. The root subset therefore has cardinality $R_{\rm root}\ge W_{\rm root}$. $\square$

**Proof of Lemma 4.1.** Fix $\rho\in[\delta,1]$ and choose a dyadic resolution $r_*\asymp\delta/\rho$. Work in one fixed angular chart retaining a fixed fraction of all directions. The tree has terminal cubes of side exactly $r_*$, so each terminal capacity below is exactly one. On this tree impose the integer capacity

$$b(Q)=\lfloor(\ell(Q)/r_*)^m\rfloor
 \ge\tfrac12(\ell(Q)/r_*)^m.
\tag{4.24}$$

The uniform fractional weight $p=cA^{-1}(Nr_*)^{-m}\asymp cA^{-1}\rho^m$ on every original direction respects every capacity, by (4.1). It also satisfies $p\le1$. Apply Lemma 4.2 to these weights. It gives a subset retaining at least $p$ times the original cardinality and satisfying every dyadic capacity. In particular, at most one selected direction lies in each terminal cube. Coloring leaf cubes by coordinates modulo 3 and choosing a largest color ensures separation comparable to $r_*$ at a dimensional constant cost. A cap of radius $r\ge r_*$ meets $O(1)$ dyadic cubes of side comparable to $r$, which proves

$$\#\mathcal T_\rho\ge cA^{-1}\rho^m\#\mathcal T,
 \qquad
 \#\{T\in\mathcal T_\rho:\operatorname{dir}(T)\in B(v,r)\}
 \le C(N\rho r)^m.
\tag{4.25}$$

No integrality of $m$ is used; the floor bound in (4.24) is sufficient. A fixed number of angular charts, grid colorings, and comparable-radius changes alter $c,C$ only.

Now apply Lemma 3.1 (smallest-scale two-ends localization) with an auxiliary exponent $a\in(0,1/2)$ to comparable-density discrete shadings of density $\sigma$. This $a$ is chosen by the requested output error; it need not equal an earlier two-ends exponent. Pigeonholing the localization radius and the retained density, at logarithmic cost in the tube count, gives a common $\rho$ and $\sigma_1$ with

$$\sigma_1\ge c\rho^a\sigma,
 \quad \sigma_1\le C\rho,
 \quad \rho\ge c\sigma^{1/(1-a)}.
\tag{4.26}$$

Group localization centers into $\rho$-cubes, whose fixed enlargements have bounded overlap. Apply (4.25) in each spatial group before isotropic rescaling. The transformed eccentricity is $N\rho$, density is $\sigma_1/\rho$, and cap coefficient is $O(1)$. Formula (4.4), applied with the fixed two-ends exponent $a$ and a fixed two-ends constant, gives after undoing the scaling and summing

$$E\ge cL^{-P_a} A^{-1}
 N^{(3-m)/2}\sigma_1^2\rho^{(m-1)/2}\#\mathcal T.
\tag{4.27}$$

Here $E$ is normalized original volume, or original occupied-cell cardinality for full grid cells. The sole $A$ factor is the retained fraction $A^{-1}\rho^m$ in (4.25); the hairbrush was invoked with a constant cap coefficient.

Put $q=(m+3)/2$. Since $q-2>0$, (4.26) yields

$$\sigma_1^2\rho^{(m-1)/2}
 \ge c\sigma^2\rho^{q-2+2a}
 \ge c\sigma^{q/(1-a)}.
\tag{4.28}$$

Given $\varepsilon>0$, choose $a>0$ so small that $q/(1-a)\le q+\varepsilon/2$. The logarithmic power $P_a$ is finite for that fixed $a$. Absorb it into $N^{-\varepsilon}$, reserving part of the error for the density pigeonholes. The resulting fractional-direction estimate is

$$E\ge c_\varepsilon A^{-1}N^{(3-m)/2-\varepsilon}
 \sigma^{(m+3)/2+\varepsilon}\#\mathcal T.
\tag{4.29}$$

This proves the comparable-density form of (4.29).

**Remark (why the unrestricted cap coefficient is linear).** Formula (4.4) has $A^{-1/2}$ under unit two ends. To obtain (4.27), the actual calculation at localization radius $r$ is $$\begin{aligned}
E&\gtrsim (Nr)^{(3-m)/2}(\sigma_1/r)^2
                (A^{-1}r^mM)\\
 &=A^{-1}N^{(3-m)/2}\sigma_1^2r^{(m-1)/2}M.
\end{aligned}$$ The cap coefficient of the rescaled retained family is fixed; its square-root coefficient is therefore a fixed constant. The original $A$ enters through the retained whole-tube fraction $A^{-1}r^m$. Fixed logarithmic factors are as in (4.27).

The stronger unrestricted replacement of $A^{-1}$ by $A^{-1/2}$ is false. Fix $1<m<k-1$, take $M\asymp N^{k-1}$ separated radial tubes through one common grid cell, and shade each by that cell. Then $$E\asymp1,\quad \sigma\asymp N^{-1},\quad
A\asymp N^{k-1-m},\quad M\asymp A N^m.$$ The cap condition holds because $(Nr)^{k-1}\le N^{k-1-m}(Nr)^m$. With $q=(m+3)/2$, an unrestricted bound $E\gtrsim A^{-\gamma}N^{(3-m)/2}\sigma^qM$ would require $1\gtrsim A^{1-\gamma}$. Thus uniformity for growing $A$ forces $\gamma\ge1$. Even with errors $N^{-e}\sigma^e$, the proposed square-root bound would force $1\gtrsim N^{(k-1-m)/2-2e}$, which fails for sufficiently small fixed $e>0$. This pencil has no fixed unit two ends and does not contradict (4.4).

**Corollary 4.3 (the cumulative-density seed).** Suppose the $M$ tubes satisfy (4.1), and let their discrete shadings, including any empty shadings, have total incidence count at least $\sigma NM$. Then, for every $\varepsilon>0$,

$$
 \#\bigcup_TY(T)
 \ge c_\varepsilon A^{-1}N^{(3-m)/2-\varepsilon}
       \sigma^{(m+3)/2+\varepsilon}M.
$$

**Proof.** Apply the comparable-density estimate (4.29) with scale and density errors $\varepsilon/2$. Weaken its density exponent to $(m+3)/2+\varepsilon$ and apply Corollary 1.1. Its single logarithmic loss is absorbed into the remaining scale error. This also proves the cumulative-density assertion of Lemma 4.1. $\square$

**Corollary 4.4 (coarsening the directions).** Let $M$ directions satisfy (4.1), and let $\delta\le h\le1$. There is a subset $V_h$ with pairwise separation at least $h$ such that

$$
 \#V_h\ge cA^{-1}(\delta/h)^mM,
 \qquad
 \#\bigl(V_h\cap B(v,r)\bigr)\le C(r/h)^m
 \quad (h\le r\le1).
\tag{4.30}
$$

The constants depend only on the fixed geometric parameters and on $k,m$.

**Proof.** Use the selection construction (4.24)--(4.25) in the proof of Lemma 4.1 with $\rho=\delta/h$. Its terminal angular resolution is comparable to $h$, its retained fraction is at least $cA^{-1}(\delta/h)^m$, and its cap bound is $C(r/h)^m$. A bounded coloring of the terminal cells makes the selected directions $h$-separated, changing only $c,C$. The case $h$ comparable to one follows by selecting one direction after restricting to a fixed angular chart. $\square$

In the lift from $\mathbb R^k$ to $\mathbb R^{k+1}$, we use $m=d$. Formula (4.29) then gives the lifted input $d'=q=(d+3)/2$, with cap dependence $A^{-1}$.

# 5. The transverse pivot estimate

## 5.1. Statement and analytic inputs

Fix an integer \(k\) and real parameters
\[
 1<d<m\le k-1,\qquad d'>0,\qquad p>0,\qquad q\ge2.
\]
Assume the two analytic estimates (5.4) and (5.5) below, with every positive scale loss and the stated uniformity. The base estimate is in \(\mathbb R^k\), and the lifted estimate is in \(\mathbb R^{k+1}\). The cap exponents \(m,d\) need not be integers. The recursive applications use the narrower range \(3<d'<d<m\), \(p\ge d\), and \(q\ge d'\); the finite construction itself only needs the range displayed here.

Let \(N\ge2\), \(\delta=N^{-1}\), \(L=\log(2N)\), and let \(\mathcal T\) consist of \(M\ge1\) unit \(\delta\)-tubes in a fixed bounded region of \(\mathbb R^k\), with one tube per \(c\delta\)-separated projective direction. Assume the absolute cap bound
\[
 \#\{T:\operatorname{dir}(T)\in B(v,r)\}
 \le C_0(Nr)^m \quad(\delta\le r\le1),
 \qquad S=M/N^m\le C_0.                           \tag{5.1}
\]
Full discrete shadings \(Y(T)\) have cardinalities between fixed positive multiples of \(\lambda N\), where \(0<\lambda\le1\). Marks \(G(T)\subset Y(T)\) have total mass at least \(\xi\lambda NM\). At every marked cell, each projective angular cap of radius \(\theta\) contains at most one tenth of the marked directions. The full shadings satisfy
\[
 \#(Y(T)\cap B(x,r))\le B r^\alpha\#Y(T),
 \qquad \delta\le r\le1,\quad 0<\alpha\le1.       \tag{5.2}
\]
We normalize \(0<\xi\le1\), \(0<\theta\le1\), and \(B\ge1\); bounded changes of these parameters are absorbed in the fixed constants. The empty-family case is trivial and has been omitted. Here and below a ball condition on a discrete shading counts its cell centers; fixed enlargements of cells and tubes change only the geometric normalization constants. Let
\[
 E=\#\bigcup_TY(T),\qquad
 \kappa=c_k\min\{\theta,1/100,(c_k/B)^{1/\alpha}\}.
\]

**Theorem 5.1 (real-cap transverse pivot).** For each fixed \(0<e<1\), provided \(N\kappa^{20}\) is sufficiently large,
\[
 \boxed{
 E^4\ge c_e\kappa^{H_k}\xi^{p+3}L^{-(p+4)}
 N^{2m+3+d'-3e}\lambda^{p+2q+4+2e}S^3,
 \qquad H_k=5(k-1)+6q+12.}                       \tag{5.3}
\]
The constants may depend on \(k,m,d,d',p,q,e\) and the fixed normalization constants; they do not depend on \(N,\lambda,M,\xi,B,\theta\). The \(k\)-dependence in \(H_k\) is actual ambient direction-packing dependence. Every scale power involving the cap parameter is displayed with \(m\) or \(d\).

The base input, at every eccentricity \(R\ge2\), is
\[
 E_R\ge c_e R^{d-m-e}\nu^p\#\mathcal U.             \tag{5.4}
\]
It holds for discrete shadings of comparable density \(\nu\) on separated tube families in \(\mathbb R^k\) with an absolute \(m\)-cap constant. The lifted input is
\[
 E_{\rm lift}\ge c_e A^{-1}N^{d'-d-e}
 s^{q+e}\#\mathcal L.                              \tag{5.5}
\]
It holds for every \(A\ge1\) and every separated tube family in \(\mathbb R^{k+1}\) with cap bound \(A(Nr)^d\), for arbitrary shadings of total incidence mass at least \(sN\#\mathcal L\). Empty line shadings are allowed. Its constant is uniform in \(A,N,s\), line count, and positions, subject to fixed geometric normalizations. In particular, the inverse cap coefficient is linear even when \(A\) depends on \(N\).

When the inputs come from \(K(m,d,p)\) and \(K(d,d',q)\), the base assertion gives (5.4), and Corollary 1.1 gives (5.5). Choose the corollary's scale loss smaller than \(e\) and weaken \(s^q\) to \(s^{q+e}\), changing only a fixed constant if \(s\) has a fixed upper bound larger than one. Endpoint normalizations with eccentricity near one are absorbed in the constants.

## 5.2. Heavy cubes and cap-preserving coarsening

Define
\[
 F=C_eN^{2e}\frac{E}{N^d}\lambda^{-p}S^{-1}
       (L/\xi)^{p+1}.                            \tag{5.6}
\]
The base input implies \(F\ge1\) after increasing \(C_e\). At each dyadic side length \(r\in[\delta,1]\), call an original grid cube heavy if it contains more than \(F(Nr)^d\) cells of the original occupied union. Use finitely many shifted dyadic grids so that every ball of radius \(r\) is contained in a bounded number of cubes with side comparable to \(r\). The multiplicity of this collection of grids is a fixed constant.

We claim that the full incidence mass in the heavy cubes of one grid and one scale is at most \(a\lambda NM\), where \(a=c\xi/L\). Suppose otherwise. Since each tube carries at most \(C\lambda N\) incidences, at least \(caM\) tubes each carry at least \(ca\lambda N\) incidences in those heavy cubes. A tube has at most \(CNr\) old cells in a cube of side \(r\ge\delta\), so every such tube meets at least \(ca\lambda/r\) heavy cubes.

Apply Corollary 4.4 at terminal direction scale \(r\) to this selected subfamily. Its original absolute \(m\)-cap bound is inherited from (5.1). The lemma retains at least
\[
 c\frac{aM}{(Nr)^m}
\]
tubes whose directions are \(cr\)-separated and satisfy
\[
 \#\{T:\operatorname{dir}(T)\in B(v,u)\}
 \le C(u/r)^m\qquad(r\le u\le1).                 \tag{5.7}
\]
This is the full cap condition at the new scale. Pairwise \(r\)-separation alone would not prove (5.7).

At width \(r\), shade each retained tube by its encountered heavy cubes. After fixed grid and tube enlargements these are admissible coarse shadings, each with density at least \(ca\lambda\). If a displayed lower cardinality is less than one, use the nonempty coarse shading; its actual density is then larger than the required lower bound. Trim larger shadings to comparable cardinalities. The base estimate (5.4), at eccentricity \(r^{-1}\), forces at least
\[
 c_e(a\lambda)^p r^{m-d+e}
      \frac{aM}{(Nr)^m}
 =c_e a^{p+1}\lambda^p S r^{-d+e}                \tag{5.8}
\]
distinct heavy cubes. Since cubes of this grid and scale are disjoint,
\[
 E\ge c_e F a^{p+1}\lambda^pSN^dr^e.
\]
Substituting (5.6) and \(r\ge N^{-1}\) contradicts this inequality for a sufficiently large choice of \(C_e\). Thus the claim holds.

Delete all incidences in all heavy cubes. Summing the \(O(L)\) scales and the fixed number of grids, choose \(c\) so that the deleted full incidence mass is at most
\[
 R\le\xi\lambda NM/100.
\]
Let \(E'\) denote the surviving occupied cell set. A surviving cell lies in no heavy cube of any selected grid; consequently the bounded cube coverings give
\[
 \#(E'\cap B(x,r))\le C F(Nr)^d
 \qquad(\delta\le r\le1).                        \tag{5.9}
\]
For a ball whose fixed enlargement has radius bigger than one, the same estimate follows by a bounded covering at unit scale. This proof uses real \(m\) only through the explicitly retained cap estimate (5.7).

Delete tubes that have lost more than half of their original full shadings. Their original full incidence mass is at most \(2R\). The total removed full mass is therefore at most \(3R\). Write \(m_0(x)\) and \(m_1(x)\) for the original and now surviving marked multiplicities. Discard the surviving marks at cells where \(m_1(x)<m_0(x)/2\). At such cells the number of marks being discarded is at most the number already removed. Hence at least \(W-6R\ge c\xi\lambda NM\) marked incidences remain, where \(W\ge\xi\lambda NM\) was the original marked mass.

Every retained tube still has comparable full density and two-ends constant at most \(2B\). At a retained marked cell each radius-\(\theta\) cap contains at most one fifth of the marks. Therefore a fixed proportion of ordered marked pairs at that cell have projective angle at least \(\theta\). Let \(\mathcal A\) be the set of these ordered angles \(a=(x,T_1,T_2)\), with \(x\) an occupied cell label. Cauchy–Schwarz over at most \(E\) cells gives
\[
 |\mathcal A|\ge c\frac{\xi^2\lambda^2N^2M^2}{E}
 =c\frac{\xi^2\lambda^2S^2N^{2m+2}}{E}.           \tag{5.10}
\]
From now on use only retained full shadings and retained marks. The symbols \(M,S,E\) still denote their original comparison values; no later step assumes that all the original tubes survived.

## 5.3. Legal samples and finite angle-output fibers

Fix an angle \(a=(x,T_1,T_2)\). Shift the two axes by \(O_k(\delta)\) through the representative of \(x\), and choose unit vectors \(u_1,u_2\) along them. For each surviving shaded-cell label on either tube, choose its projection to the corresponding shifted axis, once and for all for this angle. A longitudinal interval of length \(\delta\) receives at most \(C_k\) labels.

The choice of \(\kappa\), with \(c_k\) small enough for the factor-two two-ends deterioration, ensures that no ball of radius \(C\kappa\) contains a fixed small positive fraction of either shade. On one half of the first axis choose an early and a late fixed mass fraction, separated from the vertex and from each other by at least \(\kappa\). If they could not be so separated, the intervening fixed mass fraction would lie in a ball of radius \(C\kappa\), contradicting two ends. On the second axis choose a fixed mass fraction outside the vertex's \(\kappa\)-ball. After reversing \(u_1\) if needed, use coordinates based at \(x\); the resulting samples have the form
\[
 i=x+a_0u_1,\quad y_1=x+b u_1,\quad y_2=x+c u_2,
 \quad 0<a_0<b\le C,
 \quad a_0,b-a_0,|c|\ge\kappa,
 \quad |u_1\wedge u_2|\ge\kappa.                 \tag{5.11}
\]
There are at least \(c\lambda^3N^3\) ordered triples of occupied-cell labels with these properties. Denote their finite set by \(\mathcal P_a\). The letter \(a_0\) in (5.11) is a scalar coordinate and is distinct from the angle label \(a\).

For a sample \(P\in\mathcal P_a\), define its exact pivot
\[
 u(P)=c(1-a_0/b),\qquad
 z(P)=x+a_0u_1+u(P)u_2,
\]
and its output
\[
 f(P)=(z_0,i_0),
\]
where \(z_0\) is the cell label of the \(\delta\)-cube containing \(z(P)\), and \(i_0\) is the original occupied-cell label whose chosen projection is \(i\). Use a fixed tie-breaking rule on grid boundaries. Define the **angle-output fiber**
\[
 \mathcal P(a,f)=\{P\in\mathcal P_a:f(P)=f\}.       \tag{5.12}
\]
For fixed \(a,f\), \(i_0\) and its projected point \(i\) are fixed, so (5.12) may equivalently be viewed as a finite set of ordered endpoint-label pairs \((e_1,e_2)\). A fiber is never a union of samples from different angles.

For fixed \(i_0\), the pivots lie on a bounded segment parallel to \(u_2\), which meets at most \(CN\) grid cells. Thus an angle has at most \(C\lambda N^2\) outputs. For fixed \(a,f,b\), the output condition confines \(u(P)\) to an interval of length \(C\delta\). Since \(1-a_0/b\ge c\kappa\), it confines \(c\) to an interval of length \(C\delta/\kappa\), containing at most \(C\kappa^{-1}\) endpoint labels. There are at most \(CN\) choices of \(b\). Consequently
\[
 |\mathcal P(a,f)|\le C\kappa^{-1}N.              \tag{5.13}
\]

Delete fibers with fewer than \(c\lambda^2N\) samples. Because of the output bound, these account for at most a small fraction of the \(c\lambda^3N^3\) samples per angle. Partition the remaining nonempty fibers by dyadic integer sizes. The number of bins is \(O(L)\): by (5.13) the largest size is \(C\kappa^{-1}N\), and \(N\kappa^{20}\gg1\) implies \(\log(\kappa^{-1})\le C\log N\). Choose one bin carrying at least a \(c/L\) fraction of the total remaining sample mass. Let \(h\ge1\) be its integer lower endpoint and put \(\sigma=h/N\). Define
\[
 \Omega=\{(a,f):h\le|\mathcal P(a,f)|<2h
             \text{ and the fiber survived deletion}\}.
\]
The elements of \(\Omega\) are edges \((a,f)\), not individual endpoint pairs. Dividing the selected sample mass by \(2h\) gives
\[
 \sigma\ge c\lambda^2,\qquad \sigma\le C\kappa^{-1},
 \qquad
 |\Omega|\ge c\lambda^3\sigma^{-1}N^2
                    |\mathcal A|/L.             \tag{5.14}
\]

## 5.4. Collisions on the actual ambient sphere

For every sample satisfying (5.11), the identities
\[
 u=c(b-a_0)/b,\qquad c-u=ca_0/b
\]
give
\[
 |u|,|c-u|\ge c\kappa^2,
 \quad |z-i|\ge c\kappa^2,
 \quad \operatorname{dist}(z,x+\mathbb Ru_1)\ge c\kappa^3,
 \quad |z-y_1|,|z-y_2|\ge c\kappa^3.              \tag{5.15}
\]
Indeed, the first two quantities have magnitude at least \(c\kappa^2\). Projection perpendicular to \(u_1\), followed by \(|u_1\wedge u_2|\ge\kappa\), gives the distance bound and the two endpoint bounds. All lengths have fixed upper bounds. For fixed output \(f=(z_0,i_0)\), the vector from the center of \(i_0\) to the center of \(z_0\) therefore determines the projective direction of \(T_2\) within \(C\delta\kappa^{-2}\). Packing \(\delta\)-separated directions in the actual \((k-1)\)-dimensional projective sphere gives at most \(C\kappa^{-2(k-1)}\) possibilities for \(T_2\). The one-tube-per-direction hypothesis is used here.

For each \(f\), choose a most frequent \(T_2\) among its incident edges in \(\Omega\), and retain those edges. Write \(\Omega^*\) for the result and \(\Omega_f^*=\{a:(a,f)\in\Omega^*\}\). Then
\[
 |\Omega^*|\ge c\kappa^{2(k-1)}|\Omega|.           \tag{5.16}
\]
This selection keeps or deletes whole angle-output edges; it does not shorten any surviving fiber.

We bound collisions \(\sum_f|\Omega_f^*|^2\). Fix \(a=(x,T_1,T_2)\). If \(a'=(x',T'_1,T_2)\) shares an output \(f\) with \(a\) in \(\Omega^*\), then \(i_0\) lies within \(C\delta\) of both \(T_1\) and \(T'_1\), while \(x'\) lies within \(C\delta\) of \(T_2\). Also the longitudinal separation of \(x'\) from \(i_0\) on \(T'_1\) is at least \(\kappa\). The shifted axes of \(T_1,T_2\) determine a two-plane. Subtracting the perpendicular components of the two endpoints of the segment from \(x'\) to \(i_0\) shows that the direction of \(T'_1\) is within \(C\delta/\kappa\) of this plane.

In a dyadic shell \(\phi\le\angle(T_1,T'_1)\le2\phi\), with \(\delta\le\phi\le1\), the allowed great-circle arc has length \(O(\phi)\). Covering its tangential coordinate at spacing \(\delta\), and the \(k-2\) perpendicular coordinates at spacing \(\delta\) in a strip of width \(C\delta/\kappa\), gives at most
\[
 C\kappa^{-(k-2)}N\phi                           \tag{5.17}
\]
possible directions. The shell below \(\delta\) is counted using \(\phi=\delta\). This is ambient packing, not an assertion that the directions live on an \(m\)-dimensional surface.

For each such \(T'_1\), its intersection with \(T_1\) supplies at most \(C/\phi\) common labels \(i_0\). With \(i_0\) fixed, at most \(CN\) rounded pivots \(z_0\) occur. Finally, \(x'\in T'_1\cap T_2\) has at most \(C\kappa^{-1}\) possibilities because that angle is at least \(\kappa\). Thus the number of colliding pairs \((a',f)\) for this fixed \(a\), in one shell, is at most
\[
 C\kappa^{-(k-2)}(N\phi)\phi^{-1}N\kappa^{-1}
 =C\kappa^{-(k-1)}N^2.
\]
Summing the \(O(L)\) shells and then \(a\) proves
\[
 \sum_f|\Omega_f^*|^2
 \le C\kappa^{-(k-1)}N^2L|\mathcal A|.             \tag{5.18}
\]
In particular the count \(CN\) of pivots is for fixed \(i_0\); together with the \(C/\phi\) intersection labels it is the same \(CN/\phi\) grouping as in the saturated collision argument.

Let
\[
 \mathcal F=\{f:\Omega_f^*\ne\varnothing\},\qquad Q=|\mathcal F|.
\]
Cauchy–Schwarz, (5.14), (5.16), and (5.18) yield
\[
 Q\ge\frac{|\Omega^*|^2}{\sum_f|\Omega_f^*|^2}
 \ge c\kappa^{5(k-1)}\lambda^6\sigma^{-2}
                 N^2|\mathcal A|L^{-3}.          \tag{5.19}
\]
For each \(f\in\mathcal F\), select one angle \(a(f)\in\Omega_f^*\), and select exactly \(h\) pairs from its fiber \(\mathcal P(a(f),f)\). Use any fixed ordering to make both choices deterministic. Denote this chosen set of endpoint-label pairs by \(R_f\subset\mathcal P(a(f),f)\); by construction \(|R_f|=h=\sigma N\). The selected fiber consists entirely of legal samples from one angle. No ratio involving \(\#\Omega_f^*\), and hence no further density or scale loss, is paid. These \(Q\) selected fibers, one per distinct output, are the inputs to the lift.

## 5.5. Exact lifts, common integer mass, and the real-\(d\) cap condition

For \(f\in\mathcal F\), retain the notation \(x,u_1,u_2,i=x+a_0u_1\) of its selected angle. Choose one pair in its selected \(h\)-pair fiber and call its exact pivot \(z_*=i+u_*u_2\). Define one graph line
\[
 \ell_f(t)=(x+t u_*u_2,t)\subset\mathbb R^{k+1}.  \tag{5.20}
\]
For every selected pair \((e_1,e_2)\), whose second representative is \(y_2=x+c u_2\), its lifted point is
\[
 v_f(e_1,e_2)=(y_2,c/u_*)\in\ell_f.
\]
All exact pivots in this fiber round to the same \(z_0\), and its point \(i\) is fixed. Thus \(|u-u_*|\le C\delta\). The original value \(c/u=(1-a_0/b)^{-1}\), together with (5.11), (5.15), and \(\delta\ll\kappa^{20}\), gives
\[
 1+c\kappa\le t=c/u_*\le C\kappa^{-1}.           \tag{5.21}
\]
This holds for every selected pair, although \(u_*\) was fixed from only one pair.

If two such points lie in the same lifted \(\delta\)-cell, their horizontal coordinates \(y_2\) differ by \(O(\delta)\). Bounded longitudinal multiplicity permits \(O(1)\) second endpoint labels in that cell. For a fixed such label, the identity
\[
 b=\frac{a_0c}{c-u},\qquad |c-u|\ge c\kappa^2,
\]
shows that an \(O(\delta)\) variation of \(c,u\) changes \(b\) by at most \(C\kappa^{-4}\delta\). Hence there are at most \(C\kappa^{-4}\) first endpoint labels. Each lifted cell receives at most \(C\kappa^{-4}\) selected pairs. The \(h\) pairs therefore give at least \(c\kappa^4h\) distinct lifted cells.

By (5.21), these cells lie in at most \(C\kappa^{-1}\) integer unit slabs in the last coordinate. Assign a boundary cell to a slab by its center. Choose a fullest slab separately for each line. It contains at least \(c\kappa^5h\) cells and, in all cases, at least one cell. Choose the common integer
\[
 K=\max\{1,\lfloor c\kappa^6h\rfloor\},\qquad
 \rho=K/N,                                         \tag{5.22}
\]
where the fixed constant is sufficiently small. Every chosen slab contains at least \(K\) cells. Trim it to exactly \(K\) cells, denote this set by \(V_f^0\) with \(|V_f^0|=K\), and attach one original pair from \(R_f\) to each cell in \(V_f^0\). Since \(h\ge1\), the elementary floor estimate, with the separate case \(c\kappa^6h<1\), gives
\[
 \rho\ge c\kappa^6\sigma,\qquad 0<\rho\le C.
\]
Define the finite initial incidence set \(\mathscr I_0=\{(f,v):f\in\mathcal F,\ v\in V_f^0\}\). Its mass over all \(Q\) lines satisfies the identity
\[
 I_0=|\mathscr I_0|=KQ=\rho NQ.                                  \tag{5.23}
\]
This mass comes from the one chosen angle-fiber per output. Neither averaging over angles nor assigning a union of different angle-fibers to a line is involved. The use of \(K\ge1\) handles the case \(\kappa^6\sigma N<1\); no extra assumption \(\lambda^2N\gg1\) is imposed.

We now verify every hypothesis of the lifted input. The horizontal slopes \(v_f=u_*u_2\) are bounded by a fixed constant. Thus \(v\mapsto(v,1)/\sqrt{1+|v|^2}\) is uniformly bi-Lipschitz on this slope range. For each fixed pivot label \(z_0\),
\[
 v_f=\bar z_0-\bar i_0+O_k(\delta),               \tag{5.24}
\]
where bars denote cell centers. Distinct outputs with this fixed \(z_0\) have distinct labels \(i_0\). Consequently, an \(O(\delta)\)-ball in slope space contains only \(O_k(1)\) such outputs, because their \(i_0\) labels lie in an \(O(\delta)\)-ball of the original grid. The bounded-degree graph joining pairs of slopes within \(c\delta\) therefore admits a bounded number \(J_0\) of colors. Retain all colors; each color is a separated direction family. This coloring discards no lines or incidences.

More generally, a graph-direction cap of radius \(r\ge\delta\) confines the labels \(i_0\) to a ball of radius \(C_kr\), by (5.24) and the graph chart. Every such label lies in \(E'\). The pruned bound (5.9) therefore gives
\[
 \#\{f:\text{fixed }z_0,\ \operatorname{dir}(\ell_f)\in B(w,r)\}
 \le C F(Nr)^d.                                   \tag{5.25}
\]
There is no multiplicity of selected angles over one \(i_0\): the selection after (5.19) made the output unique. This is precisely where that selection is needed for the cap assertion. The coefficient in (5.25) is \(CF\), with no power of \(\kappa^{-1}\).

Group the lines by \(g=(z_0,j)\), where \(j\) is their chosen unit slab, and write \(M_g\) for the line count in a group. Translate its last coordinate by \(j\) before applying the lifted estimate. A retained point has horizontal coordinate \(y_2\) in the original bounded region. Since slopes are bounded, the entire unit graph segment containing it lies in a fixed enlarged bounded region after this translation. Its length lies between fixed positive constants. A cell assigned by its center to slab \([j,j+1]\) can have its exact lifted point just outside that interval, but by at most \(C\delta\) in the last coordinate. Since slopes are bounded, that cell still lies within \(C_k\delta\) of the unit segment; a fixed tube-width enlargement therefore handles all such boundary cells. Thus every group and every direction color has exactly the geometric normalizations allowed in (5.5), and \(\sum_gM_g=Q\). There are no \(\kappa\)-dependent input geometry constants hidden in the slab index.

## 5.6. Grouped arbitrary-density pruning

Set \(r_*=q+e>1\). Apply (5.5) to restrictions of the incidence set in each group and each direction color, using the actual cumulative density of that restriction. Define the uncolored multiplicity \(m_g(v)\) in each group and the cutoff
\[
 H_{\rm cut}=C_eF\rho^{1-q-e}N^{d-d'+1+e}.        \tag{5.26}
\]
Delete incidences at cells for which \(m_g(v)>H_{\rm cut}\). We prove that at least \(I_0/2\) survive.

Let \(I_{g,c}\) be the incidence mass of the deleted-cell restriction in group \(g\), color \(c\), and let \(M_{g,c}\) be the original number of lines of that color. Set \(s_{g,c}=I_{g,c}/(NM_{g,c})\) when \(M_{g,c}>0\), and omit empty colors. The shadings on many of these lines may be empty; this is why the cumulative-density corollary is necessary. The lower bound (5.5), followed by weighted convexity, gives
\[
 \begin{aligned}
 \sum_{g,c}\#U_{g,c}
 &\ge c_eF^{-1}N^{d'-d-e}\sum_{g,c}M_{g,c}s_{g,c}^{r_*}\\
 &\ge c_eF^{-1}N^{d'-d-e}Q
          \left(\frac{I_{\rm high}}{NQ}\right)^{r_*},
 \end{aligned}                                    \tag{5.27}
\]
where \(I_{\rm high}=\sum_{g,c}I_{g,c}\). On the other hand, each group has at most \(I_{g,\rm high}/H_{\rm cut}\) high cells, and each such cell belongs to at most \(J_0\) colored unions. Hence
\[
 \sum_{g,c}\#U_{g,c}
 \le J_0 I_{\rm high}/H_{\rm cut}
 \le J_0 I_0/H_{\rm cut}.                         \tag{5.28}
\]
If \(I_{\rm high}\ge I_0/2=\rho NQ/2\), substituting (5.26) into (5.27)–(5.28) gives a contradiction for sufficiently large \(C_e\). Therefore the retained incidence mass \(I\) and its energy satisfy
\[
 I\ge I_0/2=\rho NQ/2,\qquad
 \mathcal E:=\sum_g\sum_v m_g(v)^2\le H_{\rm cut}I,
                                                               \tag{5.29}
\]
where multiplicities in the last expression count only retained incidences. The weights in (5.27) sum to \(Q\), so the number of pivot/slab groups causes no loss. Original slab labels are kept when counting energy, even though each slab was translated to apply the analytic input.

## 5.7. Endpoint-pivot triples and the closing energy inequality

Each retained lifted incidence carries its attached endpoint labels \((e_1,e_2)\) and its pivot label \(z_0\). Since its original exact pivot obeyed
\[
 z=\frac{a_0}{b}y_1+\left(1-\frac{a_0}{b}\right)y_2,
\]
with both coefficients positive, the center of \(z_0\) lies within \(C\delta\) of the segment joining the centers of \(e_1,e_2\). A bounded-length segment in \(\mathbb R^k\) meets at most \(C_kN\) grid cells after a fixed \(\delta\)-enlargement. Thus at most
\[
 C_kNE^2                                             \tag{5.30}
\]
triples \((e_1,e_2,z_0)\) can occur.

It remains to control how many energy cells a fixed triple can represent. Its exact lift parameter is \(t=c/u_*\), whereas its original pair has pivot coefficient \(u\). In translated coordinates, direct algebra gives
\[
 tz-y_2-(t-1)y_1
 =(u-u_*)\left(-\frac{b}{u_*}u_1+t u_2\right).
\]
By (5.15), (5.21), and \(|u-u_*|\le C\delta\), the norm is at most \(C\kappa^{-2}\delta\). Replacing endpoints and pivot by their cell centers adds at most \(C\kappa^{-1}\delta\). Therefore
\[
 \bar e_2-\bar e_1
 =t(\bar z_0-\bar e_1)+O(\kappa^{-2}\delta).        \tag{5.31}
\]
Also \(|\bar z_0-\bar e_1|\ge c\kappa^3\), by (5.15) and the scale assumption. For a fixed triple, subtracting (5.31) for two possible parameters shows that all \(t\)'s lie in an interval of length \(C\kappa^{-5}\delta\). The lifted horizontal coordinate is \(y_2\), which is within \(C\delta\) of \(\bar e_2\). Hence the triple can occur in at most \(C\kappa^{-5}\), and in particular at most \(C\kappa^{-6}\), lifted cells.

This count includes the group index: the triple fixes \(z_0\), and the lifted cell fixes its assigned integer slab. Group translations are undone for this count. Thus, among all \(g,v\), a fixed triple occupies at most \(C\kappa^{-6}\) distinct energy positions.

Apply Cauchy–Schwarz to incidences grouped by the pair consisting of their triple and their energy position. There are at most \(C\kappa^{-6}NE^2\) such positions by (5.30). For each fixed energy position, the sum of the squares of its triple multiplicities is at most its total multiplicity squared. Consequently
\[
 \mathcal E\ge \frac{c\kappa^6 I^2}{NE^2}.         \tag{5.32}
\]
Together with (5.26) and (5.29), this gives
\[
 E^2\ge c_e\kappa^6F^{-1}\rho^{q+e}
                         N^{d'-d-1-e}Q.           \tag{5.33}
\]

**Lemma 5.2 (density accounting for one lift).** Assume (5.19) and (5.33), together with \(\rho\ge c\kappa^6\sigma\), \(\sigma\ge c\lambda^2\), and \(q\ge2\). Then
\[
 E^2\ge c_e\kappa^{5(k-1)+6(q+e)+6}
 F^{-1}N^{d'-d+1-e}\lambda^{2q+2+2e}
                         |\mathcal A|L^{-3}.      \tag{5.34}
\]

**Proof.** Substitute \(\rho\ge c\kappa^6\sigma\) and (5.19) into (5.33). The density factor is \(\lambda^6\sigma^{q+e-2}\). Since \(q+e-2\ge0\) and \(\sigma\ge c\lambda^2\),
\[
 \lambda^6\sigma^{q+e-2}
 \ge c_e\lambda^6(\lambda^2)^{q+e-2}
 =c_e\lambda^{2q+2+2e}.
\]
This proves the displayed conclusion. \(\square\)

This substitution accounts for the density cost of the present lift; the exponent \(q\) already contains any losses from earlier recursive stages.

**Completion of the proof of Theorem 5.1.** Substitute (5.6) and (5.10). The \(N\)-exponent is exactly
\[
 (d'-d+1-e)+(d-2e)+(2m+2)=2m+3+d'-3e;
\]
the density exponent is \(p+2q+4+2e\), and the remaining factors are \(\xi^{p+3}S^3L^{-(p+4)}\). Moving the two additional inverse factors of \(E\) to the left proves (5.3), because \(e<1\) and \(0<\kappa<1\) imply
\[
 \kappa^{5(k-1)+6(q+e)+6}\ge\kappa^{5(k-1)+6q+12}.
\]
This completes the proof. \(\square\)

## 5.8. Consequence and fixed-parameter dependence

Suppose \(B\le B_0L^A\), \(\xi\ge\xi_0L^{-A}\), and \(\theta\ge\theta_0L^{-A}\), with fixed \(\alpha>0\). Then
\[
 \kappa\ge c_{k,\alpha,B_0,\theta_0}
 L^{-A\max\{1,1/\alpha\}}.
\]
All the conditioning factors in (5.3) are fixed powers of \(L\). After choosing the input error \(e\) and absorbing those logarithms into an arbitrarily small scale loss, taking fourth roots gives
\[
 E\ge c_\varepsilon N^{D-\varepsilon}
 \lambda^{C+\varepsilon}S^{3/4}
 \ge c'_\varepsilon N^{D-\varepsilon}
 \lambda^{C+\varepsilon}S,
 \quad
 D=\frac{2m+3+d'}4,\qquad C=\frac{p+2q+4}4.         \tag{5.35}
\]
The second inequality uses \(S\le C_0\). The bounded scale range is absorbed into the constant; a nonempty shaded tube supplies \(E\ge1\). Neither \(D\) nor \(C\) depends on \(\alpha\), although the constants and scale threshold may do so.

Theorem 5.1 concerns transverse unit-two-ends shadings. Section 7 removes the angular restriction, and Section 8 removes two ends. Each application uses the lifted estimate in the actual ambient dimension \(k+1\). Constants may depend on the fixed parameters and on the finite recursion depth; no uniformity as \(m\downarrow3\) is required.

# 6. Sampling restricted shadings

The following dichotomy either counts cells carrying low marked multiplicity or discretizes the restricted shadings on the same tube family. In the second alternative, every selected cell meets the original full shading with positive measure. This support property will allow comparison with the cells before angular rescaling in Section 7.

**Lemma 6.1 (count or discretize).** Fix an integer $k\ge2$, fixed positive geometric constants, $0<s<1$, $0<\alpha<1-s$, $\beta>0$, and $A\ge0$. Put $h=N^{-1}$ and $L=\log(2N)$. Let $\mathcal T$ be $M\ge1$ tubes of length comparable to one and width comparable to $h$, contained in a fixed bounded region of $\mathbb R^k$, with one tube per $ch$-separated projective direction. In particular, $M\le C_kN^{k-1}$.

For each $T$, let $F_T\subset T$ be a measurable **restricted full shading** and $G_T\subset F_T$ its measurable marked subset. Assume the following conditions, with constants independent of $N$ and $\lambda$:

1.  Comparable full density: $$c_0\lambda h^{k-1}\le |F_T|\le C_0\lambda h^{k-1},
      \qquad N^{-s}<\lambda\le1.
      \tag{6.1}$$

2.  Full two ends: $$|F_T\cap B(x,r)|\le B r^\alpha |F_T|,
      \qquad h\le r\le1,
      \qquad 1\le B\le B_0L^A.
      \tag{6.2}$$

3.  Total marked mass: $$W_g:=h^{-k}\sum_T|G_T|\ge\xi\lambda NM,
      \qquad \xi\ge\xi_0L^{-A}>0.
      \tag{6.3}$$

4.  Pointwise marked angular broadness: for almost every $x$, every projective cap $\omega(v,r)$, and $h\le r\le1$, $$\sum_{T:\,\operatorname{dir}(T)\in\omega(v,r)}1_{G_T}(x)
      \le K r^\beta\sum_T1_{G_T}(x),
      \qquad 1\le K\le K_0L^A.
      \tag{6.4}$$

Let $\mathcal Q$ be the $h$-grid cells intersecting $\bigcup_TF_T$, and let $\Omega=\bigcup_{Q\in\mathcal Q}Q$. It is enough to include cells with positive intersection measure; using all intersecting cells only enlarges the available support. Define $$p_{TQ}=h^{-k}|F_T\cap Q|,\qquad
 p^g_{TQ}=h^{-k}|G_T\cap Q|,\qquad
 \mu_g(Q)=\sum_Tp^g_{TQ}.
 \tag{6.5}$$ Both probabilities lie in $[0,1]$, and $p^g_{TQ}\le p_{TQ}$.

There are $N_0$ depending only on the fixed parameters above and a dimensional threshold $a_0>0$ such that, for $N\ge N_0$, at least one of the following alternatives holds.

**(i) Low-cell count.** The cells with $0<\mu_g(Q)<a_0L$ carry at least $W_g/2$ of the expected marked mass and satisfy $$\#\{Q:0<\mu_g(Q)<a_0L\}
 \ge\frac{W_g}{2a_0L}.
 \tag{6.6}$$

**(ii) A discrete configuration with the required geometric hypotheses.** There are full discrete shadings $Y_T\subset\mathcal Q$ and marked shadings $H_T\subset Y_T$, on the **same tube family**, such that $$\frac{c_0}{2}\lambda N\le\#Y_T\le2C_0\lambda N,
 \tag{6.7}$$ $$\#\{Q\in Y_T:q_Q\in B(x,r)\}
 \le C B r^\alpha\#Y_T
 \qquad(h\le r\le1),
 \tag{6.8}$$ and $$\sum_T\#H_T\ge W_g/4
 \ge\frac{\xi}{8C_0}\sum_T\#Y_T.
 \tag{6.9}$$ Here $q_Q$ denotes a cell center. At every marked cell every projective cap of radius $$\theta=\min\left\{\frac1{100},\frac12(1000K)^{-1/\beta}\right\}
 \tag{6.10}$$ contains at most one tenth of the marked tube directions there. In particular, $\theta\ge cL^{-A/\beta}$. All cell centers in $Y_T$ lie within $C_kh$ of $T$, and each longitudinal interval of length $h$ contains only $O_k(1)$ such centers. The tube directions and their separation are unchanged. If the input directions additionally satisfy a real direction-cap bound $\#\{T:\operatorname{dir}(T)\in\omega(v,r)\}\le A_{\rm cap}(Nr)^m$, the same bound, with the same $A_{\rm cap}$ and $m$, holds for the output: no tube is removed or added. This extra cap hypothesis is not needed for the sampling proof.

The output satisfies $$\bigcup_T\bigcup_{Q\in Y_T}Q\subset\Omega,
 \qquad
 \#\bigcup_TY_T\le\#\mathcal Q.
 \tag{6.11}$$ Here $\Omega$ is the union of the available grid cells; those cells may extend beyond the measurable union $\bigcup_TF_T$.

**Proof.** The numbers $\mu_g(Q)$ and the low/high partition are deterministic. Call $Q$ low if $\mu_g(Q)<a_0L$, and high otherwise. If $$\sum_{Q\text{ low}}\mu_g(Q)\ge W_g/2,$$ then, omitting zero-mass cells, $$\frac{W_g}{2}
 \le\sum_{Q\text{ low}}\mu_g(Q)
 \le a_0L\,\#\{Q:0<\mu_g(Q)<a_0L\}.
 \tag{6.12}$$ This proves (i).

Otherwise $$W_{\rm high}:=\sum_{Q\text{ high}}\mu_g(Q)>W_g/2.
 \tag{6.13}$$ Choose independent uniform random variables $U_{TQ}$ on $[0,1]$, indexed by all tube-cell pairs with positive full mass. Select the full incidence $(T,Q)$ if $U_{TQ}\le p_{TQ}$, and select its mark if $U_{TQ}\le p^g_{TQ}$. The latter event implies the former, by the inequality in (6.5). Across different pairs all the random variables are independent. Retain only marks in high cells; do not delete any selected full incidences.

We show that full density, two ends, and angular control have a simultaneous realization.

**Full density.** Write $X_T$ for the selected full count. Its mean is $$\mu_T=\sum_Qp_{TQ}=h^{-k}|F_T|\in[c_0\lambda N,C_0\lambda N].$$ The Poisson-binomial Chernoff estimates give $$\Pr\{X_T\notin[\mu_T/2,2\mu_T]\}
 \le2\exp(-\mu_T/12)
 \le2\exp(-cN^{1-s}).
 \tag{6.14}$$ There are at most $C_kN^{k-1}$ tubes, so all the bounds in (6.7) hold except on an event of probability tending to zero faster than any inverse power of $N$.

**Full two ends.** Use radii $r$ from the dyadic list $h,2h,4h,\ldots$, ending with a radius comparable to one, and centers $z$ on an $h$-lattice in a fixed enlarged bounded region. There are $O_k(N^kL)$ center-radius tests. Every ball of radius $t\in[h,1]$ is contained in one test ball with radius between $t$ and $C_kt$. This finite family, with fixed enlargements, suffices for the required arbitrary-ball estimates.

For a test ball of radius $r$, the sum of the means of selected cells whose centers it contains is at most $$h^{-k}|F_T\cap B(z,r+\sqrt{k}h)|
 \le C_k B r^\alpha\mu_T
 \le C_k C_0B r^\alpha\lambda N.
 \tag{6.15}$$ For an enlarged radius exceeding one, use total mass instead; since the tested radius is then bounded below by a dimensional constant, the same upper bound holds after increasing $C_k$. Thus no sub-$h$ two-ends assumption is used.

Choose the upper threshold $t_r=C_*B r^\alpha\lambda N$, where $C_*$ is large enough that $t_r\ge4\mathbb E X_{T,z,r}$. The elementary upper-tail estimate $$\Pr\{X\ge t\}\le(e\mathbb EX/t)^t
 \qquad(t>\mathbb EX)$$ then bounds the failure probability by $\exp(-c t_r)$. Its threshold satisfies $$t_r\ge c\lambda N h^\alpha
 >cN^{1-s-\alpha}.
 \tag{6.16}$$ Since $1-s-\alpha>0$, this threshold grows as a fixed positive power of $N$. Union-bounding over at most $C_kN^{2k-1}L$ tube-ball pairs proves all the upper bounds simultaneously, outside an event of probability $o(1)$. Divide by the lower count $X_T\ge c_0\lambda N/2$, and use the fixed geometric enlargement from test balls to arbitrary balls. This gives (6.8). The constants in this step are independent of $N$, $\lambda$, and the particular shadings.

**High-cell angular control.** Integrating (6.4) over a cell gives $$\sum_{T:\,\operatorname{dir}(T)\in\omega(v,r)}p^g_{TQ}
 \le Kr^\beta\mu_g(Q).
 \tag{6.17}$$ For $N\ge N_0$, the radius $2\theta$ in (6.10) is at least $h$. A $\theta$-net on projective direction space has at most $C_k\theta^{-(k-1)}$ elements. Every cap of radius $\theta$ lies in a net cap of radius $2\theta$. The expected number of marks in such a net cap is at most $\mu_g(Q)/1000$, by (6.10) and (6.17).

At a high cell $Q$, let $Z_Q$ be its actual marked multiplicity and $Z_{Q,\omega}$ its marked multiplicity in a net cap. Chernoff and the preceding elementary tail estimate give $$\Pr\{Z_Q<\mu_g(Q)/2\}\le e^{-\mu_g(Q)/8},$$ $$\Pr\{Z_{Q,\omega}>\mu_g(Q)/20\}
 \le(e/50)^{\mu_g(Q)/20}
 \le e^{-\mu_g(Q)/8}.
 \tag{6.18}$$ The exponential Markov bound applies to these real thresholds. On the complementary events each radius-$\theta$ cap has at most $$\mu_g(Q)/20\le Z_Q/10$$ actual marks.

There are $O_k(N^k)$ cells. Since $\theta^{-1}$ is a fixed power of $L$, increasing $N_0$ ensures that the total number of high-cell and net-cap tests is at most $N^{k+2}$. One may take, for example, $a_0=64(k+4)$. Since high cells have $\mu_g(Q)\ge a_0L$, the sum of their failure probabilities is at most $$N^{k+2}e^{-a_0L/8}<1/8.
 \tag{6.19}$$ The density and two-ends failure probabilities in (6.14)--(6.16) sum to less than $1/8$ after another increase in $N_0$. The union bound gives a probability greater than $3/4$ that every required event holds.

Choose one such realization. By (6.13) and the high-cell lower multiplicity estimates, $$\sum_T\#H_T
 =\sum_{Q\text{ high}}Z_Q
 \ge\frac12W_{\rm high}>\frac14W_g.$$ Moreover $\sum_T\#Y_T\le2C_0\lambda NM$, so (6.3) implies (6.9). Sampling changes no axes and retains no cell without a positive full intersection, so separation, bounded support, distance to the tube, and the bounded number of cells in a longitudinal $h$-interval follow directly from the original geometry. This proves (ii). $\square$

# 7. Angular normalization

**Proposition 7.1.** Let the parameters and analytic inputs be as in Section 5.1. Put
\[
 D=\frac{2m+3+d'}4,\qquad C=\frac{p+2q+4}4,
 \qquad w=\frac{m+3}2,
\]
and suppose
\[
 1<D<m,\qquad C>2,\qquad
 \eta:=w-D+\frac{C-2}{3}>0.
\]
For every fixed two-ends exponent \(\alpha>0\), the all-angle unit-two-ends estimate is
\[
 E\ge c_\varepsilon N^{D-m-\varepsilon}\lambda^C M
\]
for absolute \(m\)-cap families in \(\mathbb R^k\). The constant may depend on the fixed two-ends constant and on \(\alpha\).

The hypotheses hold in the recursive range
\[
 3<d'<d<m\le k-1,\qquad p\ge d,\qquad q\ge d'.
\]
Indeed, \(D>3\), \(C>2\), and
\[
 m-D=\frac{2m-3-d'}4>0.
\]
The positivity of \(\eta\) in this range is recorded in (7.2).

**Proof.** We may weaken \(\alpha\) to \(\min\{\alpha,1/4\}\). Fix
\[
 0<\beta<\min\{1,m-D\}.
\]
Apply the angular decomposition and density and mark refinements of Section 3. Use one common angular radius \(\tau\), and choose the comparable density class by marked incidence mass. If its common density is \(\lambda_1\), the retained pieces satisfy, with \(L=\log(2N)\),
\[
 \lambda L^{-A}\le\lambda_1\le C\lambda,
 \qquad \sum_jM_j\ge ML^{-A}.
\]
At each marked point discard marks if their multiplicity in the selected class is less than an inverse logarithmic fraction of its previous marked multiplicity. Choose that fraction small enough that this discards at most one quarter of the selected mass. Next retain pieces in which the remaining marked mass is at least an inverse logarithmic fraction of full mass. The same total-mass comparison bounds this second loss by one quarter. Thus each retained piece has comparable full densities and logarithmic two-ends and broadness constants, and its marks carry at least an inverse logarithmic fraction of its full incidence mass.

On a piece write \(F_j(T)=Y_j(T)\) for the restricted full shading and \(G_j(T)\subset F_j(T)\) for its final marks. These are restrictions of the old grid shadings. Denoting the input union by \(U_0\), the overlap bound is
\[
 \sum_j1_{\bigcup_TF_j(T)}\le C\tau^{-\beta}1_{U_0}.
\]
Translate the containing \(O(\tau)\)-tube to the origin and stretch transverse coordinates by \(\tau^{-1}\), followed by a fixed normalization. Call the map \(A_j\), put \(N'=N\tau\), and write \(E_j=\#\bigcup_TF_j(T)\) for the old-cell count. In a bounded projective chart the stretch sends a slope \(s\) to \(s/\tau\). It preserves one tube per separated direction at scale \((N')^{-1}\); a new radius-\(r\) cap pulls back into an old cap of radius \(C\tau r\). Hence
\[
 \#\{T':\operatorname{dir}(T')\in B(v,r)\}
 \le C(N'r)^m,\qquad
 S':=M_j/(N')^m\le C_k.
\]
The transformed shadings have density comparable to \(\lambda_1\). Two ends is preserved because the inverse stretch is a contraction; the transformed marks satisfy the broadness condition of Section 3 with logarithmic constants. The required estimate in old-cell cardinality is

\[
E_j\gtrsim (N')^{D-\epsilon}\lambda_1^C
\frac{M_j}{(N')^m}.                                   \tag{7.1}
\]

Whenever the high-cell sampling alternative is used, denote its full sampled shadings by \(F_j^{\mathrm s}(T)\) and define
\[
 E_j^{\mathrm s}:=\#\bigcup_TF_j^{\mathrm s}(T).
\]
Let \(\mathcal Q_j\) be the new grid cells meeting \(A_j\bigcup_TF_j(T)\). Since \(S'\le C_k\), the core factor \((S')^{3/4}\) is explicitly weakened to \(C_k^{-1/4}S'\) before summation. The core is applied to \(E_j^{\mathrm s}\), while \(E_j\) continues to denote the original restricted piece count. Every transformed old cube meets only a bounded number of new cubes. Therefore the sampled union count is at most the transformed occupied-cell count, which is at most a constant times \(E_j\). Here \(E_j\) counts the union of restricted full shadings in the original grid. Only these original piece counts are summed with the overlap bound; no overlap is asserted for pullbacks of sampled coarse cubes. It is not identified with transformed normalized volume, which equals \(\tau E_j\) up to fixed factors.

A bound for transformed normalized volume would give an additional factor \(\tau^{-1}\) when returned to old-cell counts. A continuous core would return \(E_j\gtrsim\tau^{-1}(N\tau)^{D-e}\lambda_1^CS'\), while sampling only gives the same expression without \(\tau^{-1}\). The corresponding angular factors are \(\tau^{D-m-1+\beta-e}\) and \(\tau^{D-m+\beta-e}\), respectively. This explains why the sampled route requires \(D<m\).

Summing (7.1) over the angular pieces with overlap \(\lesssim\tau^{-\beta}\) produces

\[
\tau^{D-m+\beta-\epsilon}.
\]

By the choice of \(\beta\), the exponent is negative. Thus this factor is at least one, and summing the piece estimates proves the proposition after absorbing logarithmic losses. It remains to establish (7.1) in the following four cases.

1. If \(N'\le N^{1/(2k)}\), the old shade of one tube contains \(\gtrsim\lambda_1N\) cells, whereas the right side of (7.1) is at most \(C(N')^D\lambda_1\lesssim N^{1/2}\lambda_1\). We used \(D<m+1\le k\), \(C>1\), and \(M_j/(N')^m\lesssim1\). Thus the estimate is immediate. In the complementary range \(\log N\le2k\log N'\).

2. For \(\lambda_1\le(N')^{-1/3}\), use the continuous all-angle fractional unit-two-ends hairbrush, whose set parameter is \(w=(m+3)/2\) and density power is 2. The ratio of that estimate to (7.1) contains the favorable power
   \[
   (N')^{(C-2)/3-(D-w)}.
   \]
   The exponent equals \(\eta>0\) by hypothesis. In the recursive range \(p\ge d\) and \(q\ge d'\), it can also be written as
   \[
   \frac{C-2}{3}-(D-w)
   =\frac{p+2q-3d'+5}{12}
   \ge\frac{d-d'+5}{12}>0.                        \tag{7.2}
   \]
   Choose the hairbrush's scale loss smaller than the fixed positive margin \(\eta\). It absorbs all logarithmic conditioning losses. The normalized-volume identity contributes an additional favorable \(\tau^{-1}\) in returning to old cell counts.

3. For \(\lambda_1>(N')^{-1/3}\), apply Lemma 6.1 with cutoff \(s=1/3\), ambient dimension \(k\), and fixed two-ends exponent weakened to at most \(1/4\). Its hypotheses hold for the transformed restricted shadings: comparable per-tube density, total marked fraction at least an inverse logarithmic power, pointwise cap broadness, a bounded ambient region, and one tube per separated direction. The cap pullback above gives the full \(m\)-cap condition at scale \(N'\). Sampling preserves that condition because it changes only incidences.

   In the high-cell alternative, the minimum full two-ends threshold is
   \[
   c\lambda_1(N')^{1-\alpha}>c(N')^{5/12}.
   \]
   The lemma controls simultaneously all \(O_k((N')^{2k-1}\log N')\) tube-ball tests and the high-cell angular-net tests. Its output has the full hypotheses of the transverse core, with fixed logarithmic conditioning. Applying the core to its sampled union gives
   \[
   E_j^{\mathrm s}\ge c_e(N')^{D-e}\lambda_1^{C+e}
                 \frac{M_j}{(N')^m}.
   \]
   Now use \(E_j^{\mathrm s}\le\#\mathcal Q_j\le C_kE_j\) to obtain the lower bound for \(E_j\). Since \(\lambda_1>(N')^{-1/3}\), the extra density factor costs at most \((N')^{-e/3}\); an arbitrarily small scale-error budget proves (7.1). The actual ambient sphere supplies these test counts, regardless of the real value of \(m\).

   The fiber weight also gives \(\sigma N'\gtrsim\lambda_1^2N'>(N')^{1/3}\), up to fixed factors. The actual trimmed lifted mass is \(\rho_{\rm lift}N'Q\), where \(\rho_{\rm lift}\ge c\kappa^6\sigma\); its lower bound is the one established in (5.22)–(5.23). The integer trimming convention and the one-tube bound handle the remaining bounded scale range.

4. In the low-cell alternative of the same lemma, let \(W_g\) be the total expected marked count and put \(L'=\log(2N')\). The precise calculation is
   \[
   \frac{W_g}{2}\le\sum_{Q\text{ low}}\mu_g(Q)
   \le a_0L'\,\#\mathcal Q_{\rm low},
   \qquad W_g\ge cL^{-A}\lambda_1N'M_j.
   \]
   Hence \(\#\mathcal Q_{\rm low}\ge cL^{-A}\lambda_1N'M_j/L'\). Since \(\#\mathcal Q_{\rm low}\le\#\mathcal Q_j\le C_kE_j\), dividing the resulting lower bound for \(E_j\) by the target in (7.1) gives
   \[
   cL^{-A}\frac{(N')^{m+1-D}\lambda_1^{1-C}}{L'}.
   \]
   The positive scale power \(m+1-D>0\), together with \(C>1\), absorbs both logarithmic losses. This proves (7.1) without requiring a random realization in this alternative.

These cases prove (7.1). Summing over the original restricted pieces as above gives the asserted all-angle estimate, with the exponents in (5.35). \(\square\)

# 8. Removal of two ends and measurable shadings

**Proposition 8.1.** Fix \(1<D<m\) and \(C>0\). Suppose that, for each fixed two-ends exponent \(\alpha>0\), the all-angle unit-two-ends estimate
\[
 E\ge c_eN^{D-m-e}\lambda^C M
\]
holds for every absolute \(m\)-cap family, with every positive scale loss. Then arbitrary discrete shadings of comparable density satisfy
\[
 E\ge c_\varepsilon A^{-1}N^{D-m-\varepsilon}
       \lambda^P M,\qquad P=\max(D,C),
\]
under the cap condition with coefficient \(A\). The same assertion holds for measurable shadings after multiplication by the cell volume.

**Proof for discrete shadings.** Apply the unchanged-scale thinning of Section 4 first, retaining \(cA^{-1}M\) whole tubes with an absolute cap constant. It suffices to prove the remaining estimate with that constant. Choose the two-ends exponent \(\alpha>0\) later, in terms of the final scale-loss budget.

The shortest-scale localization of Section 3 selects a common radius \(\rho\in[\delta,1]\) and refined old density \(\nu\), with
\[
 \nu\gtrsim L^{-A_0}\rho^\alpha\lambda,
 \qquad \nu\lesssim\rho,
 \qquad L=\log(2N).
\]
Here \(A_0\) is fixed once \(\alpha\) and the normalization constants have been fixed. A common dyadic class of these parameters retains at least an inverse logarithmic fraction of the tubes. Restrict each localized shading to one cube of a common aligned \(\rho\)-grid carrying a fixed fraction of its localized cells. A localization ball meets only a bounded number of such cubes. This restriction preserves relative two ends up to a fixed constant. Each cube is a union of old cells, distinct spatial groups have disjoint restricted unions, and every retained tube is assigned to one group.

Let \(M_Q\) be the tube count in a group. Apply Corollary 4.4 with terminal direction scale \(h\asymp\delta/\rho\). It retains at least \(c\rho^mM_Q\) tubes, with separated directions and every-scale cap bound at resolution \(\delta/\rho\). Rescale the spatial group isotropically by \(\rho^{-1}\). Its eccentricity is \(N_\rho\asymp N\rho\), and its density is comparable to \(\nu/\rho\). The image grid is a similarity of the old grid, so cell cardinality is unchanged. The all-angle estimate therefore gives
\[
 \begin{aligned}
 E_Q
 &\ge c_e(N\rho)^{D-m-e}(\nu/\rho)^C\rho^mM_Q\\
 &=c_eN^{D-m-e}\nu^C\rho^{D-C-e}M_Q\\
 &\ge c_eN^{D-m-e}\nu^C\rho^{D-C}M_Q.
 \end{aligned}
\]
The last inequality uses \(\rho\le1\). Eccentricities bounded near one are absorbed into the normalization constants. Summing the disjoint old-cell unions and absorbing the logarithmic tube-count loss gives
\[
 E\ge c_eN^{D-m-e}\nu^C\rho^{D-C}M.                \tag{8.1}
\]
There is no extra ambient-dimension power: the retained fraction is \(\rho^m\), supplied by the complete cap condition.

If \(C\le D\), the bound \(\nu\lesssim\rho\) gives \(\nu^C\rho^{D-C}\gtrsim\nu^D\). If \(C>D\), then \(\rho\le1\) gives \(\nu^C\rho^{D-C}\ge\nu^C\). Thus in both cases
\[
 \nu^C\rho^{D-C}\gtrsim\nu^P
 \gtrsim L^{-A_0P}\delta^{\alpha P}\lambda^P,
 \qquad P=\max(D,C).
\]
Choose \(\alpha P\) smaller than one third of the final scale-loss budget; then fix \(\alpha\), choose the input loss \(e\), and absorb all fixed logarithmic factors into the remaining budget. This proves the discrete estimate. Its constants may depend on \(\alpha\), but its exponents do not. \(\square\)

**Corollary 8.2 (recursive implication).** For
\(3<d'<d<m\), \(p\ge d\), and \(q\ge d'\),
\[
 K(m,d,p),\ K(d,d',q)
 \quad\Longrightarrow\quad
 K\left(m,\frac{2m+3+d'}4,
 \max\left\{\frac{2m+3+d'}4,\frac{p+2q+4}4\right\}\right).
                                                               \tag{8.2}
\]

**Proof.** Corollary 1.1 supplies the cumulative lifted input of Theorem 5.1. The parameter inequalities in Proposition 7.1, including the margin in (7.2), hold throughout the stated range. Apply Proposition 7.1 and then Proposition 8.1. \(\square\)

## 8.1. Passage to measurable shadings

We prove the measurable part of Proposition 8.1. Shrink each input shading, if necessary, to volume comparable to \(\lambda|T|\). Its target is
\[
 \left|\bigcup_TY(T)\right|
 \ge c_\varepsilon A^{-1}\delta^{m+1-D+\varepsilon}
              \lambda^P\sum_T|T|,
 \qquad P=\max(D,C)>1.
\]
If \(\lambda\le\delta\), the cap condition gives \(M\lesssim A\delta^{-m}\). The target without its favorable \(\delta^\varepsilon\) factor is then at most a constant times \(\delta^{k-D}\lambda^P\). One tube supplies volume at least \(c\lambda\delta^{k-1}\), whose ratio to this upper bound is
\[
 \delta^{D-1}\lambda^{1-P}
 \ge\delta^{D-P}\ge1.
\]
Thus it remains to consider \(\lambda>\delta\).

Let \(U=\bigcup_TY(T)\). For each old grid cube \(Q\), put \(w_Q=|U\cap Q|/|Q|\). Since a unit tube meets at most \(C N\) cubes, cubes with \(w_Q<c\lambda\) contain at most a small fixed fraction of any tube's required shaded mass, when \(c\) is sufficiently small. Remove their incidences and partition the remaining cubes into dyadic occupancy classes. Because \(\lambda>\delta\), there are \(O(L)\) classes, with \(L=\log(2N)\).

Choose a class by its tube-incidence mass. It carries at least \(c\lambda NML^{-1}\delta^k\). The per-tube mass in this class is at most \(C\lambda N\delta^k\). After discarding tubes contributing less than a sufficiently small multiple of \(\lambda N\delta^k/L\) and choosing a dyadic per-tube mass class, retain at least \(M/L^{A_1}\) tubes, each contributing at least \(c\lambda N\delta^k/L^{A_1}\), for a fixed \(A_1\). Direction separation and every cap bound are preserved.

Write \(w\) for the common occupancy scale. Replace a retained tube's positive incidences in this class by full cubes, and then trim to comparable integer counts. As each cube has occupancy at most \(2w\), the resulting discrete density is at least
\[
 c\lambda/(wL^{A_1}).
\]
The discrete union stays inside the selected occupancy class, whose cubes have occupancy at least \(w\). Applying the unrestricted discrete estimate and multiplying by \(w\delta^k\) gives the density factor
\[
 w\left(\frac{c\lambda}{wL^{A_1}}\right)^P
 =c^P\lambda^PL^{-A_1P}w^{1-P}
 \ge c^P\lambda^PL^{-A_1P}.
\]
All other conditioning losses are fixed powers of \(L\) and are absorbed into an arbitrarily small scale loss. Finally,
\[
 \delta^kN^{D-m}\lambda^PM
 =\delta^{m+1-D}\lambda^P\sum_T|T|
\]
up to fixed tube-volume constants. This proves the measurable assertion. \(\square\)

# 9. Iteration and maximal consequences

## 9.1. Diagonal iteration with the Wolff lifted input

The unrestricted fractional hairbrush in Section 4 supplies
\[
 K\left(m,\frac{m+3}{2},\frac{m+3}{2}\right)
 \qquad(m>3).
\]
Its extra arbitrarily small density power is absorbed using \(\lambda\gtrsim N^{-1}\). The measurable conclusion follows from Section 8.1. In particular the full-direction seed in \(\mathbb R^n\) is \(\mathsf M_n((n+2)/2)\).

Suppose \(\mathsf M_n(d)\) is available. In the direct analytic formulation of Theorem 5.1 take
\[
 m=n-1,\qquad p=d,\qquad d'=q=\frac{d+3}{2}.
\]
The base input is the given \(n\)-dimensional assertion; the cumulative lifted input is Corollary 4.3 in actual ambient space \(\mathbb R^{n+1}\), with cap exponent \(d\). Thus
\[
 D=\frac{4n+d+5}{8},\qquad C=\frac{2d+7}{4}.
                                                               \tag{9.1}
\]
If \(D<n-1\) and \(C\le D\), Propositions 7.1 and 8.1 give \(\mathsf M_n(D)\). The one-third density cutoff used in Section 7 has margin
\[
 \frac{n+2}{2}-D+\frac{C-2}{3}
 =\frac{d+7}{24}>0.                               \tag{9.2}
\]

Start at \(d_0=4\) in dimension six and \(d_0=5\) in dimension eight. The recurrence and its exact solutions are
\[
 \begin{gathered}
 d_{j+1}=\frac{4n+5+d_j}{8},\\
 d_j^{(6)}=\frac{29}{7}-\frac{1}{7\cdot8^j},\qquad
 d_j^{(8)}=\frac{37}{7}-\frac{2}{7\cdot8^j}.
                                                               \tag{9.3}
 \end{gathered}
\]
Throughout \(4\le d\le29/7\) for \(n=6\), and \(5\le d\le37/7\) for \(n=8\), one has
\[
 D-C=\frac{4n-3d-9}{8}>0,
 \qquad D<n-1.
\]
Together with (9.2), these verify the global hypotheses at every finite stage.

| Dimension | Seed | First two iterates | Limit |
|---:|---:|---:|---:|
| \(6\) | \(4\) | \(33/8,\ 265/64\) | \(29/7\) |
| \(8\) | \(5\) | \(21/4,\ 169/32\) | \(37/7\) |

The value \(21/4\) is also a published maximal exponent [HRZ19, Z19]. Using that theorem as the eight-dimensional base input starts this application one stage later. The numerical coincidence is separate from the proof of the present transition.

For a prescribed \(\varepsilon>0\), choose a finite \(j\) such that \(d_\infty-d_j\le\varepsilon/2\), where \(d_\infty=(4n+5)/7\). The stage-\(j\) estimate with loss \(\varepsilon/2\) implies the limiting assertion because
\[
 \delta^{n-d_j+\varepsilon/2}\lambda^{d_j}
 \ge\delta^{n-d_\infty+\varepsilon}\lambda^{d_\infty}.
\]
Its constant may depend on this finite \(j\), and hence on \(\varepsilon\), as allowed in \(\mathsf M_n(d_\infty)\).

## 9.2. The real-cap density envelope

Define
\[
 a_0=\frac12,\qquad a_{j+1}=\frac{2+a_j^2}{4},
 \qquad d_j(m)=3+a_j(m-3),
 \qquad p_j(m)=\max\{d_j(m),4\}.                    \tag{9.4}
\]
We prove \(K(m,d_j(m),p_j(m))\) for each fixed \(m>3\), every finite \(j\), and every adequate fixed integer ambient dimension. The scalar recurrence and its limiting set exponent are those of [KT02, Section 6].

The fractional Wolff seed is \(d_0(m)=(m+3)/2\). Increasing its density exponent to \(p_0(m)\) proves the initial assertion. Suppose the assertion is available at depth \(j\) for every fixed real cap parameter above three. Use it both at \(m\) and at \(d=d_j(m)\). The second invocation is in the lifted integer ambient dimension, and gives
\[
 d'=d_j(d_j(m))=3+a_j^2(m-3),
 \quad p=p_j(m),\quad q=p_j(d_j(m)).
\]
The transition in Corollary 8.2 has set exponent
\[
 D=\frac{2m+3+d'}4=d_{j+1}(m).
\]
The sequence \(a_j\) increases from \(1/2\) and remains below \(2-\sqrt2<1\), so
\[
 3<d'<d\le D<m.
\]
Put \(P=\max(D,4)\). Since \(p,q\le P\),
\[
 C=\frac{p+2q+4}{4}
 \le\frac{3P+4}{4}\le P.                          \tag{9.5}
\]
Corollary 8.2 first gives density exponent \(\max(D,C)\le P\). Increasing it to \(P=p_{j+1}(m)\) proves the induction step. The allowance of density power four when the set exponent is below four is necessary for this closure near \(m=3\).

Each invocation quantifies over a fixed real cap parameter. At a finite depth the nested parameters form a finite collection strictly greater than three. Constants may depend on them; no uniformity as \(m\downarrow3\) is required.

The increasing slopes converge to the smaller fixed point of \(a=(2+a^2)/4\). Hence
\[
 a_\infty=2-\sqrt2,\qquad
 d_\infty(m)=3+(2-\sqrt2)(m-3).                    \tag{9.6}
\]
Given a final scale loss \(\varepsilon\), choose a finite depth with \(d_\infty(m)-d_j(m)<\varepsilon/2\). Use the depth-\(j\) theorem with the remaining loss and the inequality
\[
 \lambda^{p_j(m)}\ge
 \lambda^{\max\{d_\infty(m),4\}}.
\]
This gives the limiting cap assertion with density exponent \(\max\{d_\infty(m),4\}\). For \(m=n-1\), \(n\ge6\), one has \(d_\infty(m)>4\). The final assertion is therefore diagonal, and Section 8.1 proves Theorem 1.1.

| Depth | Slope \(a_j\) | Dimension 6: \(d_j(5)\) | Dimension 8: \(d_j(7)\) |
|---:|---:|---:|---:|
| \(0\) | \(1/2\) | \(4\) | \(5\) |
| \(1\) | \(9/16\) | \(33/8\) | \(21/4\) |
| \(2\) | \(593/1024\) | \(2129/512\) | \(1361/256\) |
| \(3\) | \(2448801/4194304\) | \(8740257/2097152\) | \(5594529/1048576\) |
| Limit | \(2-\sqrt2\) | \(7-2\sqrt2\) | \(11-4\sqrt2\) |

The diagonal and real-cap iterations agree at their first step, then use different lifted inputs. The latter recursion gives the stronger limits. Both arguments use a sufficiently deep finite iteration for each prescribed scale loss.

## 9.3. The associated maximal operator

Define
\[
 K_\delta f(v)=\sup_{T\parallel v}\frac1{|T|}\int_T|f(x)|\,dx.
\]
The shaded-union assertion \(\mathsf M_n(a)\) implies a restricted weak bound. Choose separated directions in a level set of \(K_\delta1_E\), with one witnessing tube per direction, and apply (1.1). Enlarging direction caps costs only fixed constants. It follows that
\[
 |\{v:K_\delta1_E(v)>\lambda\}|
 \le C_\varepsilon\delta^{-(n-a)-\varepsilon}
                         \lambda^{-a}|E|.          \tag{9.7}
\]
Restricted weak interpolation with the trivial \(L^\infty\) bound gives, for every fixed \(r>a\), a strong \(L^r\) norm bound \(C_{r,e}\delta^{-(n-a+e)/r}\). Also
\[
 K_\delta f(v)\le C\delta^{-(n-1)}\|f\|_1,
\]
so the finite measure of the direction sphere gives a strong \(L^1\) norm bound of the same size. Interpolate these two strong bounds to exponent \(a\), with
\[
 \vartheta=\frac{r-a}{a(r-1)},\qquad
 \frac1a=\frac{1-\vartheta}{r}+\vartheta.
\]
The resulting scale exponent is
\[
 (1-\vartheta)\frac{n-a+e}{r}+\vartheta(n-1).
\]
Choose fixed \(r>a\) close enough to \(a\), and then fixed \(e>0\) small enough, to make it less than \((n-a)/a+\varepsilon\). Thus each endpoint above gives
\[
 \|K_\delta f\|_{L^a(S^{n-1})}
 \le C_\varepsilon\delta^{-(n-a)/a-\varepsilon}
                         \|f\|_{L^a(\mathbb R^n)}. \tag{9.8}
\]
For the diagonal limits, the scale exponents are \(13/29\) in dimension six and \(19/37\) in dimension eight. The same conversion applies to the stronger values in (1.2).

\clearpage

# A. A bush input and the CDR comparison

The Christ–Duoandikoetxea–Rubio de Francia exponent in ambient dimension \(r\) is \((r+1)/2\); see Katz–Tao's 2000 survey, Figure 1 and Section 2. In terms of the direction-cap parameter \(m=r-1\), this is \((m+2)/2\). We first prove the corresponding real-cap estimate, including arbitrary cumulative density, and then substitute it into the pivot theorem.

## A.1. The cumulative-density bush estimate

**Lemma A.1.** Let \(M\ge1\) unit \(N^{-1}\)-tubes in a fixed bounded region of \(\mathbb R^k\) satisfy
\[
\#\{T:\operatorname{dir}(T)\in B(v,r)\}
\le A(Nr)^m,
\qquad N^{-1}\le r\le1,
\]
where \(m>0\) and \(A\ge1\). Let their discrete shadings, possibly empty, have total incidence mass at least \(sNM\), where \(0<s\le1\). Their union count satisfies
\[
E\ge c_{k,m}A^{-1}N^{1-m/2}s^{(m+2)/2}M.
\tag{A.1}
\]
The constant depends only on \(k,m\) and the fixed tube and grid normalizations.

**Proof.** A fixed cover of the projective sphere by radius-one caps gives
\[
M\le C_k A N^m.
\]
If \(sN\) is bounded, the right side of (A.1) is at most a fixed multiple of \((sN)^{(m+2)/2}\). The union is nonempty, so \(E\ge1\), and a sufficiently small constant proves this case.

Assume henceforth that \(sN\) exceeds a sufficiently large fixed constant. Delete tubes with fewer than \(sN/2\) shaded cells. At least \(sNM/2\) incidences remain. Some occupied cell \(x\) belongs to
\[
\mu\ge \frac{sNM}{2E}
\]
retained tubes. A ball of radius \(c_1s\) about its center meets any tube in at most \(C_k(c_1sN+1)\) cells. Choose \(c_1\) small enough, and the lower threshold for \(sN\) large enough, that every tube of this bush retains at least \(c_2sN\) shaded cells outside the ball.

If an outside cell \(y\) belongs to a tube of the bush, that tube also meets \(x\). Its direction therefore lies within \(C_kN^{-1}/|x-y|\) of the projective direction of \(y-x\), where \(x,y\) now denote cell centers. Since \(|x-y|\ge c_1s\), the cap condition bounds the number of bush tubes through \(y\) by \(C_{k,m}A s^{-m}\). Fixed covers handle caps near the endpoints of the allowed radius range. Counting the outside incidences gives
\[
E\ge \frac{c\mu sN}{A s^{-m}}
\ge c A^{-1}s^{m+2}N^2M/E.
\]
Taking square roots and then using \(M\le C_kAN^m\), we obtain
\[
\begin{aligned}
E&\ge cA^{-1/2}s^{(m+2)/2}N M^{1/2}\\
 &\ge c'A^{-1}N^{1-m/2}s^{(m+2)/2}M.
\end{aligned}
\]
This proves (A.1). \(\square\)

The proof requires neither two ends nor comparable per-tube density. The intermediate bound has square-root dependence on both \(A^{-1}\) and \(M\); (A.1) is its linear-in-\(M\) consequence.

## A.2. Substitution into the pivot theorem

Take the original ambient dimension to be \(n\), so its cap parameter is \(m=n-1\). The lifted family has cap parameter \(d\). Lemma A.1, applied in the actual lifted ambient space \(\mathbb R^{n+1}\), supplies the analytic input (5.5) with
\[
d'=q=\frac{d+2}{2},\qquad
E_{\mathrm{lift}}\gtrsim F^{-1}N^{d'-d}\rho^qQ.
\]
Its constants are uniform in the cap coefficient \(F\); the scale and density errors allowed in (5.5) follow by weakening this estimate. We use the direct-input form of Theorem 5.1, which allows these exponents even when \(d'\le3\).

With a diagonal base input \(p=d\), the exponent map (5.35) becomes
\[
D=\frac{4n+d+4}{8},\qquad
C=\frac{d+3}{2},\qquad
D-C=\frac{4n-3d-8}{8}.
\tag{A.2}
\]
The same bush estimate in the original ambient space supplies the initial exponent \(d_0=(n+1)/2\). Thus the resulting diagonal iteration is
\[
d_{j+1}=\frac{4n+d_j+4}{8},\qquad
d_\infty=\frac{4n+4}{7},\qquad
d_j=d_\infty+(d_0-d_\infty)8^{-j}.
\tag{A.3}
\]

For every integer \(n\ge5\), this sequence increases from \(d_0\) to \(d_\infty\), and the hypotheses of the global reductions hold throughout. Indeed, \(1<d<n-1\), \(q\ge2\), and \(C>2\). The smallest values of \(D-C\) and \(n-1-D\) occur at the limit, where
\[
D-C=\frac{4n-17}{14}>0,
\qquad n-1-D=\frac{3n-11}{7}>0.
\]
Writing \(w=(n+2)/2\), the sparse-density margin in Proposition 7.1 is
\[
w-D+\frac{C-2}{3}
=\frac{d+8}{24}>0.
\tag{A.4}
\]
Proposition 7.1 therefore removes the angular restriction, and Proposition 8.1 removes two ends with density exponent \(\max(D,C)=D\). Its measurable conversion makes each resulting estimate available as the next base input. This argument uses neither the parameter restrictions nor the notation of the narrower recursive Corollary 8.2.

For a prescribed final scale loss \(\varepsilon>0\), choose a finite depth \(j\) with \(d_\infty-d_j<\varepsilon/2\), and apply that finite-stage estimate with loss \(\varepsilon/2\). Since \(0<\delta,\lambda\le1\),
\[
\delta^{n-d_j+\varepsilon/2}\lambda^{d_j}
\ge \delta^{n-d_\infty+\varepsilon}\lambda^{d_\infty}.
\]
Consequently the pivot and global reductions give the limiting maximal exponent \((4n+4)/7\), with arbitrary positive scale loss. Its difference from Wolff's exponent is
\[
\frac{4n+4}{7}-\frac{n+2}{2}=\frac{n-6}{14},
\]
so it improves that particular bound precisely when \(n\ge7\).

## A.3. Set exponents and density exponents

The choice of lifted input gives three distinct fixed points:

| Lifted input in cap parameter \(d\) | Set exponent \(d'\) | Density exponent \(q\) | Diagonal-input fixed point |
|---|---:|---:|---:|
| Fractional Wolff | \((d+3)/2\) | \((d+3)/2\) | \((4n+5)/7\) |
| CDR bush | \((d+2)/2\) | \((d+2)/2\) | \((4n+4)/7\) |
| Bush estimate with weakened set exponent | \((d+1)/2\) | \((d+2)/2\) | \((4n+3)/7\) |

For the third row, weaken only the power of \(N\) in Lemma A.1. Keeping \(q=(d+2)/2\), Theorem 5.1 gives
\[
D=\frac{4n+d+3}{8},\qquad C=\frac{d+3}{2}.
\]
Starting again from \(d_0=(n+1)/2\), its iterates satisfy
\[
d_j=\frac{4n+3}{7}
+\left(\frac{n+1}{2}-\frac{4n+3}{7}\right)8^{-j}.
\]
At the limiting exponent,
\[
D-C=\frac{2n-9}{7}>0,
\qquad n-1-D=\frac{3n-10}{7}>0
\qquad(n\ge5),
\]
and the angular margin is
\[
\frac{n+2}{2}-D+\frac{C-2}{3}
=\frac{d+11}{24}>0.
\]
The same reductions therefore apply for every integer \(n\ge5\).

The historical threshold \(n\ge9\) for \((4n+3)/7\) concerns its improvement over Wolff's bound:
\[
\frac{4n+3}{7}-\frac{n+2}{2}=\frac{n-8}{14}.
\]
Katz–Tao handle the lower dimensions using Wolff at the beginning of Section 5 of *New bounds for Kakeya problems*. Their sliced argument ends with
\[
E\gtrsim N\lambda^{(2n+14)/7}M^{4/7}
\]
and uses \(n>8\) to obtain the required density power. That intermediate density exponent is specific to their construction. In the pivot calculation above, both the lifted density exponent and the global reduction conditions have instead been displayed directly.

\clearpage

# B. Comparison with cited maximal estimates

Let
\[
 B_n=\max_{2\le \ell\le n}\min\left\{
 n-\ell+2,\frac{n^2+\ell^2+n-\ell}{2n}\right\},
 \qquad
 K_n=3+(2-\sqrt2)(n-4).
\]
The exponent \(B_n\) is supplied by Zahl [Z19, Theorem 1.5, equation (1.6)]. The same values follow from Hickman–Rogers–Zhang [HRZ19, Theorem 1.2 and Figure 1]; their adjoint threshold \(r_n\) is converted to the present convention by \(B_n=r_n/(r_n-1)\). The following table compares those results with the fractional-profile conclusion of this paper. Decimal entries are rounded to six places. The comparison is with the cited estimates and is not an exhaustive claim about subsequent literature.

| \(n\) | \(r_n\) | \(B_n\) | \(K_n\) | \(K_n-B_n\) |
|---:|---:|---:|---:|---:|
| 5 | \(18/13\) | \(18/5=3.600000\) | \(3.585786\) | \(-0.014214\)† |
| 6 | \(4/3\) | \(4\) | \(4.171573\) | \(+0.171573\) |
| 7 | \(34/27\) | \(34/7\approx4.857143\) | \(4.757359\) | \(-0.099784\) |
| 8 | \(21/17\) | \(21/4=5.250000\) | \(5.343146\) | \(+0.093146\) |
| 9 | \(6/5\) | \(6\) | \(5.928932\) | \(-0.071068\) |
| 10 | \(13/11\) | \(13/2=6.500000\) | \(6.514719\) | \(+0.014719\) |
| 11 | \(7/6\) | \(7\) | \(7.100505\) | \(+0.100505\) |
| 12 | \(31/27\) | \(31/4=7.750000\) | \(7.686292\) | \(-0.063708\) |
| 13 | \(106/93\) | \(106/13\approx8.153846\) | \(8.272078\) | \(+0.118232\) |
| 14 | \(9/8\) | \(9\) | \(8.857864\) | \(-0.142136\) |
| 15 | \(47/42\) | \(47/5=9.400000\) | \(9.443651\) | \(+0.043651\) |

† The five-dimensional row is a numerical comparison only. The density envelope \(p_j(m)=\max\{d_j(m),4\}\) does not yield a diagonal maximal estimate at \(K_5<4\). The fractional-profile maximal conclusion is stated for integer \(n\ge6\).

Among dimensions \(6\le n\le15\), \(K_n>B_n\) precisely for \(n=6,8,10,11,13,15\). This is also the comparison of the corresponding maximal consequences and Katz–Tao set bounds in [HRZ19, Section 9.2 and Figure 5]. In dimension eight, the first diagonal step from Wolff gives \(21/4\), which already equals the cited maximal benchmark. The later diagonal limit \(37/7\), and the fractional-profile value \(11-4\sqrt2\), exceed that benchmark. In dimension six, the first step \(33/8\) already exceeds the cited benchmark \(4\).

The numerical antecedents are set estimates. Katz–Tao [KT00, p. 14] record the Hausdorff bound \((4n+5)/7\), giving \(29/7\) and \(37/7\) in dimensions six and eight. Their real-cap recursion [KT02, Definition 6.1, Theorem 6.2, and the subsequent iteration] gives the set-exponent line \(K_n\). The contribution asserted here is the estimate for arbitrary-density shadings with density power equal to the displayed exponent.

\clearpage

# References

[HRZ19] J. Hickman, K. M. Rogers, and R. Zhang, *Improved bounds for the Kakeya maximal conjecture in higher dimensions*, American Journal of Mathematics **144** (2022), no. 6, 1511–1560; arXiv:1908.05589. [Preprint](https://arxiv.org/abs/1908.05589). Theorem 1.2 and Figure 1 give the maximal comparison; Section 9.2 and Figure 5 compare the resulting dimension bounds with the Katz–Tao set estimates.

[KT00] N. H. Katz and T. Tao, *Recent progress on the Kakeya conjecture*, arXiv:math/0010069 (2000). [Preprint](https://arxiv.org/abs/math/0010069). See pp. 3–4 for the classical comparisons and p. 14 for the Córdoba-enhanced de-slicing Hausdorff bound.

[KT02] N. H. Katz and T. Tao, *New bounds for Kakeya problems*, Journal d'Analyse Mathématique **87** (2002), 231–263; arXiv:math/0102135. [Preprint](https://arxiv.org/abs/math/0102135). Section 6 contains the real direction-cap framework, pivot, collision, lift, energy argument, and set-exponent iteration.

[W95] T. H. Wolff, *An improved bound for Kakeya type maximal functions*, Revista Matemática Iberoamericana **11** (1995), no. 3, 651–674. [DOI: 10.4171/RMI/188](https://doi.org/10.4171/RMI/188). Theorem 1 gives the maximal input; Lemma 3.1(ii) and Section 4 give the two-ends localization and reduction.

[WZ25] H. Wang and J. Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025). [Preprint](https://arxiv.org/abs/2502.17655v1). Lemma 7.8 gives the vector-selection argument; Corollary 7.10 supplies the restricted-shading overlap statement in dimension three. The higher-dimensional form used here is proved in the text.

[Z19] J. Zahl, *New Kakeya estimates using Gromov's algebraic lemma*, Advances in Mathematics **380** (2021), article 107596; arXiv:1908.05314. [Preprint](https://arxiv.org/abs/1908.05314). Theorem 1.5, equation (1.6), supplies the exponent \(B_n\) above.

[Z25] J. Zahl, *A Survey of the Kakeya conjecture, 2000–2025*, arXiv:2512.09397v1 (2025). [Preprint](https://arxiv.org/abs/2512.09397v1). Section 3.3 discusses repeated Córdoba density losses in the three-dimensional Wang–Zahl arguments.
