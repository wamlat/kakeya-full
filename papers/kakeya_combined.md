---
title: "Kakeya maximal estimates via the Katz–Tao pivot argument"
date: "8 September 2026"
geometry: margin=24mm
fontsize: 11pt
---

\begin{center}\small Research draft; revised exposition\end{center}

## Abstract

We derive Kakeya maximal estimates with exponent \(D_n=3+(2-\sqrt2)(n-4)\) for every integer \(n\ge6\), allowing an arbitrarily small scale loss. Katz and Tao proved the same exponent for Hausdorff dimension. The argument here tracks the shading density through their pivot construction to obtain the maximal estimate. We first treat \(\mathsf M_6(4)\Rightarrow\mathsf M_6(33/8)\), using Gaussian projection and Wolff's five-dimensional theorem for the lifted input. The general result requires cap estimates with real counting exponents and an iteration controlling both the scale and density powers.

\tableofcontents
\clearpage

# 1. Statements and conventions

## 1.1. Main result

A unit \(\delta\)-tube in \(\mathbb R^n\) is the \(\delta\)-neighborhood of a unit line segment. Its direction is unoriented. Throughout, directions are \(c\delta\)-separated for a fixed \(c>0\). A *shading* is a measurable subset \(Y(T)\subset T\); it has density at least \(\lambda\) if \(|Y(T)|\ge\lambda|T|\). Write \(\mathsf M_n(a)\) for the assertion that, for every \(\varepsilon>0\), there is \(c_\varepsilon>0\) such that every such family and all shadings of density at least \(\lambda\) satisfy
\[
 \left|\bigcup_{T\in\mathcal T}Y(T)\right|
 \ge c_\varepsilon\delta^{n-a+\varepsilon}\lambda^a
                   \sum_{T\in\mathcal T}|T|,
 \qquad 0<\delta,\lambda\le1.                         \tag{1.1}
\]
The constant is independent of scale, density, tube count and positions. Fixed changes in length, width and separation affect only constants. To work in a fixed bounded region, assign each tube to a unit cube meeting a fixed fraction of its shading. Restrict to that fraction, apply the estimate in each cube, and sum using bounded overlap and the linear dependence on tube number.

**Theorem 1.1.** For each integer \(n\ge6\), \(\mathsf M_n(D_n)\) holds, where
\[
 D_n=3+(2-\sqrt2)(n-4).
 \qquad
 D_6=7-2\sqrt2,\quad D_8=11-4\sqrt2.                 \tag{1.2}
\]
Katz and Tao [KT02, Section 6] proved the Hausdorff bound (1.2) using the cap estimates, pivot construction and scalar recursion that underlie our argument. The proposed contribution is the density factor in (1.1). At each pivot step, the input density powers \(p,q\) become \((p+2q+4)/4\); this includes every density loss in the lifted input. Section 9.2 controls these powers by \(p_j(m)=\max\{d_j(m),4\}\).

Section 2 first proves \(\mathsf M_6(4)\Rightarrow\mathsf M_6(33/8)\), with a lifted input obtained by Gaussian projection and Wolff's five-dimensional theorem. Section 9.1 gives the weaker limits \(\mathsf M_6(29/7)\) and \(\mathsf M_8(37/7)\). Their underlying exponent \((4n+5)/7\) was already a Hausdorff bound in [KT00, p. 14]. The full iteration uses the real cap estimates of Section 4. Appendix B compares its maximal exponents with those of Hickman–Rogers–Zhang and Zahl: (1.2) is stronger in some dimensions and weaker in others.

## 1.2. Cap bounds and discrete shadings

Let the ambient dimension \(k\) be an integer, let \(3<m\le k-1\) be real, and put \(\delta=N^{-1}\). In fixed projective direction charts assume the cap bound
\[
 \#\{T:\operatorname{dir}(T)\in B(v,r)\}
 \le A(Nr)^m,\qquad \delta\le r\le1,
 \qquad A\ge1.                                      \tag{1.3}
\]
Here \(m\) is a counting exponent, not the dimension of a manifold of directions. Directions remain \(c\delta\)-separated in the ambient sphere. Lifting increases the integer ambient dimension from \(k\) to \(k+1\).

A discrete shading consists of cells of a common \(\delta\)-grid whose centers lie within \(C\delta\) of the tube. Each tube has at most \(C_*N\) such cells and \(O(1)\) in each longitudinal interval of length \(\delta\). Fixed enlargements allow us to take \(\delta=2^{-J}\) and use aligned dyadic grids. Localization cubes are then unions of original cells; fixed normalizations restore this convention after rescaling. Write
\[
 M=\#\mathcal T,\qquad E=\#\bigcup_TY(T),\qquad
 L=\log(2N).
\]
Discrete unions are counted in cells; measurable unions use Lebesgue measure. A *marked shading* \(G(T)\subset Y(T)\) selects incidences used in the proof. Density and two ends refer to the full shading \(Y(T)\), unless stated otherwise.

A full shading has two ends with exponent \(\alpha>0\) and constant \(B\) if
\[
 |Y(T)\cap B(x,r)|\le Br^\alpha|Y(T)|,
 \qquad \delta\le r\le1.
\]
For discrete shadings, count cell centers. All auxiliary exponents are fixed before \(N\) varies. A logarithmic two-ends constant means \(B\le B_0L^b\), with \(B_0,b\) fixed. Constants may depend on these parameters and on fixed density-comparability constants. Thus \(L^{O(1)}\) has a fixed exponent and can be absorbed into any prescribed positive power of \(N\).


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

The selection in Section 4 retains at least \(cA^{-1}M\) whole tubes with a fixed cap coefficient. Apply it at the original scale, before choosing marks or imposing broadness. We may then work with
\[
 S=M/N^m\lesssim1,
\]
and restore \(A^{-1}\) at the end. Section 4.4 shows why this factor is necessary when \(A\) grows with \(N\).

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
Consequently
\[
 \lambda_j^rM_j
 =\lambda_j^{r-1}(\lambda_jM_j)
 \ge\frac{c_rs^rM}{\log(2N)}.
\]
Apply the input to this subfamily, which inherits the cap bound. If \(\lambda_j>1\), use density one at a fixed cost, since \(\lambda_j\le C_*\). The bin count is \(O(L)\) even when \(s<N^{-1}\). For the last assertion, use half the requested scale loss in the input and absorb the logarithm into the other half. \(\square\)

In particular, \(K(m,d,p)\) implies
\[
 \#U\ge c_\varepsilon A^{-1}N^{d-m-\varepsilon}s^pM
 \quad\text{if}\quad \sum_T\#Y(T)\ge sNM.
\]
This form of \(K(d,d',q)\) applies to arbitrary restrictions of the lifted shadings, whose line densities need not be comparable or satisfy two ends.

## 1.4. The induction step

Theorem 5.1 uses explicit base and lifted estimates, allowing the broader input range needed in Appendix A. Within the domain of \(K\), Corollary 8.2 gives
\[
 \begin{gathered}
 K(m,d,p),\quad K(d,d',q),\qquad
 3<d'<d<m,\quad p\ge d,\quad q\ge d',\\
 \Longrightarrow\quad K\bigl(m,D,\max(D,C)\bigr),\\
 D=\frac{2m+3+d'}4,
 \qquad C=\frac{p+2q+4}4.                           \tag{1.7}
 \end{gathered}
\]

The proof of (1.7) occupies Sections 3--8. Localization and angular decomposition select pieces suitable for the hairbrush and pivot arguments. Section 4 supplies the lifted estimate; Section 5 proves the pivot bound. Sampling and rescaling in Sections 6--8 remove the auxiliary hypotheses and recover measurable shadings. Section 9 iterates (1.7) and derives the operator bounds.

# 2. The six-dimensional case

One application of the pivot argument gives \(\mathsf M_6(4)\Rightarrow\mathsf M_6(33/8)\). Its lifted input follows from Wolff's five-dimensional theorem by Gaussian projection. Here \(S=M/N^5\lesssim1\), with the conventions of Section 1.

## 2.1. The lifted estimate by projection

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

**Proof.** First suppose all shading counts are comparable to \(sN>0\). Let \(P:\mathbb R^7\to\mathbb R^5\) be a standard Gaussian matrix. The operator-norm tail, the small-ball bound for \(Pv\), and Markov's inequality give fixed \(K,c>0\) for which, with probability bounded below, \(\|P\|\le K\) and \(|Pv|\ge c\) for at least \(M/2\) directions.

For projective directions at angle \(\psi\), choose representatives with
\[
 v'=\cos\psi\,v+\sin\psi\,w,\qquad w\perp v.
\]
The vectors \(Pv,Pw\) are independent. Conditional on \(Pv\), the perpendicular component of \(Pw\) is a four-dimensional standard Gaussian. If \(\|P\|\le K\), projected angular distance at most \(C\delta\) forces that component to have norm at most \(C_K\delta/\sin\psi\). The probability of this collision and \(\|P\|\le K\) is therefore at most
\[
 C_K\min\{1,(\delta/\psi)^4\}.
 \tag{2.3}
\]
Summing dyadic angular annuli using (2.1) gives at most \(CAM L\) expected ordered collisions. A sufficiently large Markov cutoff leaves positive probability for this bound and the preceding event to hold together. Fix such a \(P\).

The collision graph on the good directions has an independent set of size at least \(cM/(AL)\). Indeed, randomly ordering a graph's vertices and keeping those preceding all their neighbors gives expected size \(\sum_v(\deg(v)+1)^{-1}\ge V^2/(V+2e)\). The selected projected directions are \(\delta\)-separated.

Each original cell projects into \(O_K(1)\) target cells, so \(E'\le CE_{\mathcal L}\). On a good tube, one target cell confines the original longitudinal parameter to an \(O_{c,K}(\delta)\) interval and receives only \(O_{c,K}(1)\) shading cells. Projected densities remain comparable to \(s\), and lengths stay between fixed positive constants. Wolff's five-dimensional estimate [W95, Theorem 1] gives
\[
 E'\ge c_\eta N^{-1/2-\eta}s^{7/2}\frac{M}{AL}.
 \tag{2.4}
\]
Fixed changes in projected tube length and width affect only the constant.

Apply the binning argument of Corollary 1.1 with \(r=7/2\) to \(E_{\mathcal L}\ge cE^{\prime}\) and (2.4). It costs one further logarithm, uniformly even for \(s<N^{-1}\). Choose \(\eta<e\), absorb both logarithms into \(N^{e-\eta}\), and weaken the density power to \(7/2+e\). This proves (2.2). \(\square\)

## 2.2. From the pivot estimate to arbitrary shadings

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
Theorem 5.1 requires the base estimate (5.4) only in \(\mathbb R^6\); \(\mathsf M_6(4)\) supplies it at every coarser scale. Lemma 2.1 supplies (5.5) in \(\mathbb R^7\), including the factor \(A^{-1}\) and cumulative density. No all-ambient assertion \(K(5,4,4)\) is needed.

Suppose full discrete shadings have cardinality comparable to \(\lambda N\) and two ends with exponent \(0<\alpha\le1\) and constant \(B\). Let the marked incidence mass be at least \(\xi\lambda NM\), with no \(\theta\)-cap containing more than one tenth of the marks at any marked cell. Choose one sufficiently small geometric constant \(c\) before \(\alpha\) and all varying parameters, and set
\[
 \kappa=c\min\{\theta,1/100,(c/B)^{1/\alpha}\},
\]
Theorem 5.1 gives, for \(0<e<1\) and sufficiently large \(N\kappa^{20}\),
\[
 E^4\ge c_e\kappa^{58}\xi^7L^{-8}
       N^{33/2-3e}\lambda^{15+2e}S^3.
 \tag{2.8}
\]
The power of the separation parameter is
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

The key density calculation is as follows. Each selected fiber has normalized size \(\sigma\gtrsim\lambda^2\); the collision and energy estimates leave
\[
 \lambda^6\sigma^{q+e-2}
 =\lambda^6\sigma^{3/2+e}
 \gtrsim\lambda^{9+2e}.
\]
The angle count contributes \(\lambda^2\) and pruning contributes \(\lambda^4\), giving \(\lambda^{15+2e}\) in (2.8).

To remove angular concentration, use the continuous hairbrush estimate (4.23) at \(k=6,m=5\):
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

For completeness, the rescaling in Proposition 7.1 uses \(\beta=1/4\), \(R=N\tau\) and \(S'=M_j/R^5\). The original occupied-cell count \(E_j\) and the sampled count \(E_j^{\mathrm s}\) satisfy
\[
 E_j^{\mathrm s}\le\#\mathcal Q_j\le CE_j,
\]
where \(\mathcal Q_j\) contains the new cells meeting the transformed full shading. The transformed shading has normalized measurable volume comparable to \(\tau E_j\). Section 7 uses the margin \(11/24\) for low density and the cell-count inequality for sampling. Since \(S'\lesssim1\), weaken \((S')^{3/4}\) to \(S'\). Summing pieces with overlap \(O(\tau^{-1/4})\) leaves
\[
 \tau^{D-5+1/4-\eta}=\tau^{-5/8-\eta}\ge1.
 \tag{2.13}
\]
The angular factor is favorable because \(D<5\).

Finally apply Proposition 8.1. The localized old density \(\nu\) and radius \(\rho\) satisfy \(\nu\lesssim\rho\) and \(\nu\gtrsim L^{-A}\rho^\alpha\lambda\). Since
\[
 D-C=\frac38>0,
 \qquad \nu^C\rho^{D-C}\gtrsim\nu^D,
\]
localization gives density power \(D=33/8\). Choose \(\alpha\) after the final error budget and absorb the logarithms. The measurable conversion in Section 8.1 introduces \(w^{1-D}\ge1\) for \(0<w\le1\). Multiplication by \(\delta^6\) proves (2.6); [W95, Theorem 1] supplies \(\mathsf M_6(4)\). \(\square\)

The direction selections in Sections 5 and 8 simplify here. At scale \(r\ge\delta\), the conflict graph has degree \(O((Nr)^5)\), so a color class retains \(\gtrsim M/(Nr)^5\) tubes. Its \(r\)-separation gives the cap bound \(O((u/r)^5)\) for \(u\ge r\). After localization to radius \(\rho\), one color similarly retains \(\gtrsim\rho^5\) of the tubes. Thus this case needs ordinary coloring, the full-direction hairbrush and Lemma 2.1; the real cap estimates are needed only for the later iteration.

# 3. Localization and angular decomposition

Throughout this section the ambient space is $\mathbb R^k$, $\delta=N^{-1}$, and $L=\log(2N)$.

## 3.1. Smallest-scale localization

**Lemma 3.1 (Wolff two-ends localization).** For a discrete shading of density comparable to $\lambda$ and a fixed $0<\alpha<1/2$, there is a subfamily retaining a fraction $cL^{-2}$ of the tubes, a common dyadic radius $\rho$, and restrictions $Y_1(T)$ of common original density $\nu$, such that $$\nu\gtrsim\rho^\alpha\lambda,\qquad
 \nu\lesssim\rho,
 \tag{3.1}$$ and each restriction is supported in a $\rho$-ball and obeys two ends relative to that radius with a fixed constant. The same assertion holds for measurable shadings at scales at least $\delta$.

**Proof.** For each tube choose the smallest dyadic $r_T\in[\delta,1]$ for which some ball contains at least $r_T^\alpha$ of its shading. A fixed enlargement of the top scale guarantees existence. Restrict to such a ball. At every smaller radius $r<r_T/2$, minimality and dyadic rounding give $$|Y_1(T)\cap B(x,r)|
 \le 2^\alpha(r/r_T)^\alpha |Y_1(T)|.$$ For $r_T/2\le r\le r_T$ the estimate is trivial with a fixed constant. Tube geometry gives $|Y_1(T)|\lesssim r_T\delta^{k-1}$, while the defining lower bound gives $|Y_1(T)|\gtrsim r_T^\alpha\lambda\delta^{k-1}$. Pigeonhole first the radius, then the retained density; each has $O(L)$ possible classes. This proves the lemma. Restriction to one of the boundedly many $\rho$-grid cubes meeting the chosen ball retains a fixed fraction and preserves the relative two-ends inequality. $\square$

## 3.2. Angular decomposition

We adapt [WZ25, Lemma 7.8 and Corollary 7.10] to separate the shadings into pieces with controlled angular concentration.

A finite direction set $V$ in a $\tau$-cap is *broad* with exponent $\beta>0$ and constant $K$ if $$\#(V\cap B(v,r))\le K(r/\tau)^\beta\#V,
 \qquad \delta\le r\le\tau.
 \tag{3.2}$$ For larger radii, increase the constant. Work in finitely many fixed projective charts.

**Lemma 3.2 (angular decomposition).** Fix $0<\beta\le1$. For direction-separated tubes with arbitrary shadings there are a common angular scale $\tau\in[\delta,1]$, disjoint assigned tube families $\mathcal T_j$, and restricted shadings $Y_j(T)$, with the following properties. Each family lies inside one $O(\tau)$-tube and has directions in an $O(\tau)$-cap. The retained incidence mass is at least $cL^{-3}$ of the original mass. The unions $U_j$ have pointwise overlap at most $C\tau^{-\beta}$. At every point of each $U_j$, the retained directions there obey (3.2) with a fixed error. For discrete input all choices can be made constant on every original cell.

**Proof.** First consider a finite direction set $V$. On the remaining set greedily maximize $r^{-\beta}\#(V_{\rm rem}\cap B(v,r))$, with $\delta\le r\le1$. Retain the subset $W$ in the maximizing cap, delete the remaining directions in its $100$-fold enlargement, and stop after deleting at least half of the original directions. Maximality gives internal broadness, and comparison with a fixed radius-one covering of the direction sphere gives $$\#W\ge c_k r^\beta\#V.$$ The number deleted at that step is at most $C_k100^\beta\#W\le C_k100\#W$, using the same maximizing property, or a radius-one cover when $100r>1$. Thus the total retained size before radius pigeonholing is at least $c_k\#V$. One dyadic radius class retains at least $c_kL^{-1}\#V$. Enlarge its radii by at most two. The selected subsets remain disjoint, are broad with fixed error in radius-$\tau$ caps, and each has size at least $c_k\tau^\beta\#V$. Consequently at most $C_k\tau^{-\beta}$ such subsets occur. Only the direction subsets need be disjoint.

Apply the construction at each point. Pigeonholing the multiplicity, the pointwise radius and then one common radius costs $O(L)$ each, retaining at least $c_kL^{-3}$ of the incidence mass. The choices depend only on the finite incidence set, so are measurable and, for discrete input, constant on cells.

Choose a bounded-overlap global covering by caps of radius $3\tau$, assigning each pointwise cap to one containing global cap. At a point, the direction subsets assigned to different global caps remain disjoint. Unions of subsets broad at the same scale remain broad, by summing (3.2). Each direction belongs to at most $C_k$ global caps. Assign every tube to the cap retaining the largest portion of its shading; this loses at most $C_k$ in total mass. This assignment can spoil pointwise broadness. In each cap retain only points where the assigned subset contains at least $1/(4C_k)$ of the former subset. The discarded mass is at most one quarter of the post-assignment mass, by summing that proportional threshold. The retained directions are broad with a changed fixed error.

For a cap centered at $v$, use parallel covering tubes whose axes form a $2\tau$-lattice in $v^\perp$, with width $C_k\tau$. Every original tube assigned to the cap is contained in one covering tube; assign it to one such cover. At any fixed point, at most $C_k$ assigned cover tubes can occur, since their lattice axes lie within $C_k\tau$ of the line through that point parallel to $v$. As before, retain a point in a spatial piece only when its incidence subset is at least $1/(4C_k)$ of the parent cap subset. This loses at most one quarter of the remaining mass and preserves broadness with a fixed error. Each tube is now assigned once.

At each point there are at most $C_k\tau^{-\beta}$ selected direction subsets and $C_k$ spatial pieces per subset, proving the overlap bound. $\square$

## 3.3. Density and marks after restriction

Assume $c_0\sigma\delta^{k-1}\le |Y^{\mathrm{in}}(T)|\le C_0\sigma\delta^{k-1}$ and two-ends constant $B_0L^b$. Apply Lemma 3.2 with fixed $0<\beta\le1$. For a tube assigned to piece $j$, write $Y(T)=Y_j(T)\subset Y^{\mathrm{in}}(T)$. Then

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

for $\delta\le r\lesssim\tau$, with dimensional $K_0$. We retain density on each tube and broadness on selected incidences as follows.

**Discard sparse tubes.** Put $a=\kappa/8$. Delete $T$ if $|Y(T)|<a|Y^{\mathrm{in}}(T)|$. Let $\mathcal T_j^*$ be the surviving family in piece $j$. Its total deleted incidence mass $D$ obeys

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

**Recompute the good set.** Write

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

**Retain pieces with enough marks.** Keep pieces with $W_j^*\ge I_j^*/2$. On a rejected piece, $W_j^*<I_j^*-W_j^*$, so the sum of its good mass is at most $R$. Hence

$$\sum_{j\text{ retained}}W_j^*
 \ge W-2D-R\ge W-3D\ge5W/8.
\tag{3.10}$$

The retained pieces have at least half their incidence mass marked, density range (3.6), two-ends bound (3.7), broadness constant $2K_0$ on the marks, and the original overlap bound.

Section 4 allows $\Lambda/\lambda\lesssim L^3$, so applies directly to (3.6). For sampling in Section 7, first select a density class by marked mass and repeat the good-set restriction; this costs only an inverse power of $L$.

# 4. A hairbrush estimate under a cap bound

## 4.1. The continuous estimate

Fix an integer ambient dimension $k\ge3$, a real $1<m\le k-1$, a direction separation constant, and fixed upper and lower tube length constants. Put $\delta=N^{-1}$, $L=\log(2N)$. A family of unit $\delta$-tubes satisfies the $m$-dimensional cap condition with constant $A\ge1$ if

$$\#\{T:\operatorname{dir}(T)\in B(v,r)\}\le A(Nr)^m,
 \qquad \delta\le r\le1.
\tag{4.1}$$

Fixed changes in geometric constants are permitted. Normalized volume means physical volume divided by $\delta^k$; it equals the cell count for unions of full grid cells.

For fixed $\alpha>0$, $b\ge0$, $B_0\ge1$ and density constants $c_0,C_0>0$, we prove that there are $c>0$ and finite $P\ge0$ such that, whenever

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

The constants $c,P$ depend only on $k,m,\alpha,b,B_0,c_0,C_0$ and the fixed geometry. The displayed scale and density powers are independent of $\alpha$, although the constants may diverge as $\alpha\downarrow0$.

Density ratios bounded by a fixed power of $L$ change only $P$. The bounded-region reduction of Section 1 lets us work in one fixed ball.

## 4.2. The hairbrush argument

Consider $\delta$-tubes with $\delta$-separated directions in a fixed ball, and shadings $Y(T)$ satisfying

$$\lambda\delta^{k-1}\le |Y(T)|\le\Lambda\delta^{k-1},
 \qquad |Y(T)\cap B(x,r)|\le B r^\alpha |Y(T)|.
\tag{4.5}$$

Suppose a measurable set $G$ carries marked incidence mass

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

First assume $r_0\theta\ge C\delta$; the complementary logarithmic regime is treated below. Then $\theta\ge\delta$, and broadness in a $\theta$-cap centered at a marked direction forces multiplicity at least $C$. Choose $C>100$.

**Choose a stem.** Direction separation bounds the full multiplicity by $C\delta^{-(k-1)}$. Select a dyadic $\mu$ and a set

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

**Bound intersections in each plane.** Directions in a bin lie within $C\delta$ of a great circle. Its portion in a $\psi$-cap is covered by $O(\psi/\delta)$ spherical $\delta$-balls, so contains at most $C\psi/\delta$ separated directions. Thus, for each bristle $T$ in that bin,

$$\sum_{T'\text{ in the bin}}|T\cap T'|
 \le C\delta^{k-1}
 +\sum_{\psi\text{ dyadic}}C(\psi/\delta)(\delta^k/\psi)
 \le C L\delta^{k-1}.
\tag{4.13}$$

Cauchy--Schwarz and $|Y_2(T)|\ge c\lambda\delta^{k-1}/L$ yield

$$|U_j|\ge c\lambda^2\delta^{k-1}\#H_j/L^3.
\tag{4.14}$$

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

\needspace{6\baselineskip}

**Logarithmic dependence and coarse scales.** If $B\le B_1L^b$ and $K\le K_1L^q$, then

$$(r_0\theta)^{(k-1)/2}L^{-5/2}
 \ge c L^{-P_0},
 \quad
 P_0=\frac{k-1}{2}\left(\frac{b+1}{\alpha}+\frac q\beta\right)+\frac52.
\tag{4.17}$$

Here $c$ depends on $\alpha,\beta,B_1,K_1$. Substituting $\lambda=\sigma L^{-u}$ adds $3u/2$ to the logarithmic power in (4.16); a mass loss $L^{-v}$ adds $v$. Neither $r_0$ nor $\theta$ depends on density.

If $r_0\theta<C\delta$, these logarithmic bounds force $N$ to be bounded by a fixed power of $L$, with constants depending on the fixed parameters. Direction separation then bounds $\#\mathcal T$ by a fixed power of $L$. The elementary inequality $|U|\ge W_G/\#\mathcal T$ proves (4.16) with a larger logarithmic loss, since $A^{-1/2}\delta^{(m-1)/2}\lambda^{3/2}\Lambda^{-1/2}\lesssim1$. This also covers a coarse eccentricity $N'$ bounded by a fixed power of the original $L$, including when $\log(2N')$ is much smaller than $L$.

## 4.3. Removing angular concentration

Choose

$$0<\beta<\min\{1,(m-1)/2\},
\tag{4.18}$$

for example $\beta=\min\{1/2,(m-1)/4\}$. Apply Lemma 3.2 and Section 3.3. In each retained piece, expand coordinates perpendicular to the cap center by $\tau^{-1}$. After a fixed normalization the width is $\delta'\asymp\delta/\tau$, with directions separated at this scale. In slope coordinates on the cap, the map multiplies by $\tau^{-1}$; the chart maps are uniformly bi-Lipschitz. A new $r$-cap therefore pulls back into a $C\tau r$-cap, giving

$$\#\{T':\operatorname{dir}(T')\in B(v,r)\}
 \le C A(N\tau r)^m.
\tag{4.19}$$

Tube lengths change by fixed factors. Tube and shading volumes share determinant $\tau^{-(k-1)}$, preserving the density interval $[c\kappa\sigma,C\sigma]$. The inverse map contracts balls, so two ends holds at radii $r\ge\delta'\gtrsim\delta$ with $B'\le C\kappa^{-1}B_0L^b$. Marked fractions and broadness change only by fixed factors.

Let $V_j,W_j$ be old physical union volume and good incidence volume, and $V_j',W_j'$ the transformed quantities. Apply (4.16), using the original $L$ to bound all smaller multiplicity logarithms. It gives

$$V_j'\ge cL^{-P} A^{-1/2}(\delta/\tau)^{(m-1)/2}
 \sigma W_j'.
\tag{4.20}$$

The factor $\kappa^{3/2}$ is included in $L^{-P}$. If $N\tau$ is below the fixed logarithmic threshold, use the coarse-scale argument of Section 4.2 with the original $L$.

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

In normalized volumes, this rescaling gives $E'\asymp\tau E$: the determinant is $\tau^{-(k-1)}$, whereas the new cell volume is larger by $\tau^{-k}$. This comparison concerns measurable volume; Section 7 separately compares occupied-cell counts.

For $m=k-1$ and $A=O(1)$, (4.4) becomes

$$|\bigcup_T Z(T)|
 \ge cL^{-P}\delta^{(k-2)/2}\sigma^2
 \bigl(\delta^{k-1}\#\mathcal T\bigr).
\tag{4.23}$$

## 4.4. Selecting directions and removing two ends

**Lemma 4.1 (unrestricted cap estimate).** Under the cap condition (4.1), arbitrary discrete shadings of cumulative density $\sigma$ satisfy (4.29). The constants are uniform for $A\ge1$.

**Lemma 4.2 (selection under tree capacities).** Let a finite rooted tree partition a finite set $X$ at its leaves. Write $X_v$ for the elements below node $v$, and give every node an integer capacity $b_v\ge0$. If weights $0\le w_x\le1$ satisfy $$\sum_{x\in X_v}w_x\le b_v\qquad\text{for every node }v,$$ there is a subset $J\subset X$ with $\#(J\cap X_v)\le b_v$ at every node and $\#J\ge\sum_{x\in X}w_x$.

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

The floor bound in (4.24) works for real $m$. Chart choices, colorings and fixed radius changes affect only $c,C$.

Apply Lemma 3.1 to comparable-density discrete shadings of density $\sigma$, choosing $a\in(0,1/2)$ from the final error budget. At logarithmic cost in tube count, obtain a common radius $\rho$ and density $\sigma_1$ with

$$\sigma_1\ge c\rho^a\sigma,
 \quad \sigma_1\le C\rho,
 \quad \rho\ge c\sigma^{1/(1-a)}.
\tag{4.26}$$

Group localization centers into $\rho$-cubes, whose fixed enlargements have bounded overlap. Apply (4.25) in each spatial group before isotropic rescaling. The transformed eccentricity is $N\rho$, density is $\sigma_1/\rho$, and cap coefficient is $O(1)$. Formula (4.4), applied with the fixed two-ends exponent $a$ and a fixed two-ends constant, gives after undoing the scaling and summing

$$E\ge cL^{-P_a} A^{-1}
 N^{(3-m)/2}\sigma_1^2\rho^{(m-1)/2}\#\mathcal T.
\tag{4.27}$$

Here $E$ is the original normalized volume, equal to the original cell count for full cells. Selection contributes $A^{-1}\rho^m$; the rescaled hairbrush has a fixed cap coefficient.

Put $q=(m+3)/2$. Since $q-2>0$, (4.26) yields

$$\sigma_1^2\rho^{(m-1)/2}
 \ge c\sigma^2\rho^{q-2+2a}
 \ge c\sigma^{q/(1-a)}.
\tag{4.28}$$

Given $\varepsilon>0$, choose $a>0$ so small that $q/(1-a)\le q+\varepsilon/2$. The logarithmic power $P_a$ is finite for that fixed $a$. Absorb it into $N^{-\varepsilon}$, reserving part of the error for the density pigeonholes. The resulting fractional-direction estimate is

$$E\ge c_\varepsilon A^{-1}N^{(3-m)/2-\varepsilon}
 \sigma^{(m+3)/2+\varepsilon}\#\mathcal T.
\tag{4.29}$$

This proves (4.29) for comparable densities; Corollary 4.3 gives its cumulative form. \(\square\)

**Necessity of the factor $A^{-1}$.** The localization calculation is
$$\begin{aligned}
E&\gtrsim (Nr)^{(3-m)/2}(\sigma_1/r)^2
                (A^{-1}r^mM)\\
 &=A^{-1}N^{(3-m)/2}\sigma_1^2r^{(m-1)/2}M.
\end{aligned}$$
Here $r$ is the localization radius and the rescaled cap coefficient is fixed. The square-root dependence in (4.4) cannot replace $A^{-1}$ in the unrestricted estimate. Fix $1<m<k-1$, take $M\asymp N^{k-1}$ separated radial tubes through one common grid cell, and shade each by that cell. Then $$E\asymp1,\quad \sigma\asymp N^{-1},\quad
A\asymp N^{k-1-m},\quad M\asymp A N^m.$$ The cap condition holds because $(Nr)^{k-1}\le N^{k-1-m}(Nr)^m$. With $q=(m+3)/2$, an unrestricted bound $E\gtrsim A^{-\gamma}N^{(3-m)/2}\sigma^qM$ would require $1\gtrsim A^{1-\gamma}$. Thus uniformity for growing $A$ forces $\gamma\ge1$. Even with errors $N^{-e}\sigma^e$, the proposed square-root bound would force $1\gtrsim N^{(k-1-m)/2-2e}$, which fails for sufficiently small fixed $e>0$. This pencil has no fixed unit two ends and does not contradict (4.4).

**Corollary 4.3 (cumulative density).** Suppose the $M$ tubes satisfy (4.1), and let their discrete shadings, including any empty shadings, have total incidence count at least $\sigma NM$. Then, for every $\varepsilon>0$,

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

**Proof.** In (4.24)--(4.25), take $\rho=\delta/h$. The terminal resolution is comparable to $h$, the retained fraction is $cA^{-1}(\delta/h)^m$, and the cap bound is $C(r/h)^m$. A bounded coloring gives $h$-separation. For $h\asymp1$, select one direction in a fixed chart. $\square$

In the lift from $\mathbb R^k$ to $\mathbb R^{k+1}$, we use $m=d$. Formula (4.29) then gives the lifted input $d'=q=(d+3)/2$, with cap dependence $A^{-1}$.

# 5. The transverse pivot estimate

## 5.1. Hypotheses and statement

Fix an integer \(k\) and real parameters
\[
 1<d<m\le k-1,\qquad d'>0,\qquad p>0,\qquad q\ge2.
\]
Assume (5.4) and (5.5) below, with every positive scale loss and the stated uniformity. They concern tubes in \(\mathbb R^k\) and \(\mathbb R^{k+1}\), respectively; the cap exponents \(m,d\) may be real. The recursion will use \(3<d'<d<m\), \(p\ge d\), and \(q\ge d'\), but the present argument only needs the displayed range.

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
Take \(0<\xi,\theta\le1\) and \(B\ge1\). Ball conditions on discrete shadings count cell centers. Fix the geometric conventions, including allowed cell and tube enlargements, and then choose a sufficiently small geometric constant \(c_k>0\), before choosing \(\alpha\) or the varying data. Use this same constant in both places below. Put
\[
 E=\#\bigcup_TY(T),\qquad
 \kappa=c_k\min\{\theta,1/100,(c_k/B)^{1/\alpha}\}.
\]

**Theorem 5.1 (transverse pivot estimate).** Under the preceding geometric hypotheses and the analytic inputs (5.4), (5.5), for each fixed \(0<e<1\) and sufficiently large \(N\kappa^{20}\),
\[
 \boxed{
 E^4\ge c_e\kappa^{H_k}\xi^{p+3}L^{-(p+4)}
 N^{2m+3+d'-3e}\lambda^{p+2q+4+2e}S^3,
 \qquad H_k=5(k-1)+6q+12.}                       \tag{5.3}
\]
The constants may depend on \(k,m,d,d',p,q,e\) and the fixed normalizations, but not on \(N,\lambda,M,\xi,B,\theta\). The dependence on \(k\) in \(H_k\) comes from packing directions in the ambient sphere; the cap parameters in the scale powers remain \(m,d\).

The base input, at every eccentricity \(R\ge2\), is
\[
 E_R\ge c_e R^{d-m-e}\nu^p\#\mathcal U.             \tag{5.4}
\]
It holds for discrete shadings of comparable density \(\nu\) on separated tube families in \(\mathbb R^k\) with an absolute \(m\)-cap constant. The lifted input is
\[
 E_{\rm lift}\ge c_e A^{-1}N^{d'-d-e}
 s^{q+e}\#\mathcal L.                              \tag{5.5}
\]
It holds for every \(A\ge1\) and every separated tube family in \(\mathbb R^{k+1}\) with cap bound \(A(Nr)^d\), for shadings of total incidence mass at least \(sN\#\mathcal L\), including empty line shadings. Its constant is uniform in \(A,N,s\), line count, and positions under the fixed geometric normalizations. The factor \(A^{-1}\) must remain linear when \(A\) depends on \(N\).

The hypotheses \(K(m,d,p)\), \(K(d,d',q)\) supply (5.4), (5.5), the latter by Corollary 1.1. Choose that corollary's scale loss below \(e\), and weaken \(s^q\) to \(s^{q+e}\). If \(s\) has a fixed upper bound above one, this changes only the constant. Bounded eccentricities are absorbed into the normalizations.

## 5.2. Removing heavy cubes

Define
\[
 F=C_eN^{2e}\frac{E}{N^d}\lambda^{-p}S^{-1}
       (L/\xi)^{p+1}.                            \tag{5.6}
\]
The base input implies \(F\ge1\) after increasing \(C_e\). At each dyadic side length \(r\in[\delta,1]\), call an original grid cube heavy if it contains more than \(F(Nr)^d\) cells of the original occupied union. Use a fixed finite collection of shifted dyadic grids that covers each radius-\(r\) ball by boundedly many cubes of side comparable to \(r\).

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
Thus the coarsened family retains the cap condition at every radius.

At width \(r\), shade each retained tube by the heavy cubes it meets, using fixed grid and tube enlargements. These shadings have density at least \(ca\lambda\). Trim them to comparable cardinalities, using at least one cube when the lower bound is less than one. The base estimate (5.4), at eccentricity \(r^{-1}\), forces at least
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
For fixed enlargements of balls beyond radius one, use a bounded covering at unit scale.

Delete tubes that have lost more than half of their original full shadings. Their original full incidence mass is at most \(2R\). The total removed full mass is therefore at most \(3R\). Write \(m_0(x)\) and \(m_1(x)\) for the original and now surviving marked multiplicities. Discard the surviving marks at cells where \(m_1(x)<m_0(x)/2\). At such cells the number of marks being discarded is at most the number already removed. Hence at least \(W-6R\ge c\xi\lambda NM\) marked incidences remain, where \(W\ge\xi\lambda NM\) was the original marked mass.

Every retained tube still has comparable full density and two-ends constant at most \(2B\). At a retained marked cell each radius-\(\theta\) cap contains at most one fifth of the marks. Therefore a fixed proportion of ordered marked pairs at that cell have projective angle at least \(\theta\). Let \(\mathcal A\) be the set of these ordered angles \(a=(x,T_1,T_2)\), with \(x\) an occupied cell label. Cauchy–Schwarz over at most \(E\) cells gives
\[
 |\mathcal A|\ge c\frac{\xi^2\lambda^2N^2M^2}{E}
 =c\frac{\xi^2\lambda^2S^2N^{2m+2}}{E}.           \tag{5.10}
\]
From now on, use the retained shadings and marks, while \(M,S,E\) retain their original values.

## 5.3. Samples and fibers

Fix an angle \(a=(x,T_1,T_2)\). Shift the two axes by \(O_k(\delta)\) through the representative of \(x\), and choose unit vectors \(u_1,u_2\) along them. For each surviving shaded-cell label on either tube, choose its projection to the corresponding shifted axis, once and for all for this angle. A longitudinal interval of length \(\delta\) receives at most \(C_k\) labels.

The fixed choice of \(c_k\) allows for the factor-two increase in the two-ends constant: \(2B(C\kappa)^\alpha\le2c_k\) once \(Cc_k\le1\). Thus no ball of radius \(C\kappa\) contains a fixed small positive fraction of either shading. On one half of the first axis choose an early and a late fixed mass fraction, separated from the vertex and from each other by at least \(\kappa\). If they could not be so separated, the intervening fixed mass fraction would lie in a ball of radius \(C\kappa\), contradicting two ends. On the second axis choose a fixed mass fraction outside the vertex's \(\kappa\)-ball. After reversing \(u_1\) if needed, use coordinates based at \(x\); the resulting samples have the form
\[
 i=x+a_0u_1,\quad y_1=x+b u_1,\quad y_2=x+c u_2,
 \quad 0<a_0<b\le C,
 \quad a_0,b-a_0,|c|\ge\kappa,
 \quad |u_1\wedge u_2|\ge\kappa.                 \tag{5.11}
\]
Let \(\mathcal P_a\) be the set of these ordered triples of occupied-cell labels; it has size at least \(c\lambda^3N^3\). Here \(a_0\) is a scalar coordinate, while \(a\) labels the angle.

For a sample \(P\in\mathcal P_a\), define its exact pivot
\[
 u(P)=c(1-a_0/b),\qquad
 z(P)=x+a_0u_1+u(P)u_2,
\]
and its output
\[
 f(P)=(z_0,i_0),
\]
where \(z_0\) is the cell label of the \(\delta\)-cube containing \(z(P)\), and \(i_0\) is the original occupied-cell label whose chosen projection is \(i\). Use a fixed tie-breaking rule on grid boundaries. Define the fiber
\[
 \mathcal P(a,f)=\{P\in\mathcal P_a:f(P)=f\}.       \tag{5.12}
\]
For fixed \(a,f\), both \(i_0\) and \(i\) are fixed. We therefore identify (5.12) with its set of ordered endpoint-label pairs \((e_1,e_2)\), all from the same angle.

For fixed \(i_0\), the pivots lie on a bounded segment parallel to \(u_2\), which meets at most \(CN\) grid cells. Thus an angle has at most \(C\lambda N^2\) outputs. For fixed \(a,f,b\), the output condition confines \(u(P)\) to an interval of length \(C\delta\). Since \(1-a_0/b\ge c\kappa\), it confines \(c\) to an interval of length \(C\delta/\kappa\), containing at most \(C\kappa^{-1}\) endpoint labels. There are at most \(CN\) choices of \(b\). Consequently
\[
 |\mathcal P(a,f)|\le C\kappa^{-1}N.              \tag{5.13}
\]

Delete fibers with fewer than \(c\lambda^2N\) samples. Because of the output bound, these account for at most a small fraction of the \(c\lambda^3N^3\) samples per angle. Partition the remaining nonempty fibers by dyadic integer sizes. The number of bins is \(O(L)\): by (5.13) the largest size is \(C\kappa^{-1}N\), and \(N\kappa^{20}\gg1\) implies \(\log(\kappa^{-1})\le C\log N\). Choose one bin carrying at least a \(c/L\) fraction of the total remaining sample mass. Let \(h\ge1\) be its integer lower endpoint and put \(\sigma=h/N\). Define
\[
 \Omega=\{(a,f):h\le|\mathcal P(a,f)|<2h
             \text{ and the fiber survived deletion}\}.
\]
View \(\Omega\) as a bipartite graph of angle-output edges, each carrying its whole fiber. Dividing the selected sample mass by \(2h\) gives
\[
 \sigma\ge c\lambda^2,\qquad \sigma\le C\kappa^{-1},
 \qquad
 |\Omega|\ge c\lambda^3\sigma^{-1}N^2
                    |\mathcal A|/L.             \tag{5.14}
\]

## 5.4. Counting collisions

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
The distance and endpoint bounds follow by projection perpendicular to \(u_1\) and \(|u_1\wedge u_2|\ge\kappa\). All lengths have fixed upper bounds. For fixed output \(f=(z_0,i_0)\), the vector from the center of \(i_0\) to the center of \(z_0\) therefore determines the projective direction of \(T_2\) within \(C\delta\kappa^{-2}\). Packing \(\delta\)-separated directions in the actual \((k-1)\)-dimensional projective sphere gives at most \(C\kappa^{-2(k-1)}\) possibilities for \(T_2\). The one-tube-per-direction hypothesis is used here.

For each \(f\), choose a most frequent \(T_2\) among its incident edges in \(\Omega\), and retain those edges. Write \(\Omega^*\) for the result and \(\Omega_f^*=\{a:(a,f)\in\Omega^*\}\). Then
\[
 |\Omega^*|\ge c\kappa^{2(k-1)}|\Omega|.           \tag{5.16}
\]
Each retained edge keeps its whole fiber.

We bound collisions \(\sum_f|\Omega_f^*|^2\). Fix \(a=(x,T_1,T_2)\). If \(a'=(x',T'_1,T_2)\) shares an output \(f\) with \(a\) in \(\Omega^*\), then \(i_0\) lies within \(C\delta\) of both \(T_1\) and \(T'_1\), while \(x'\) lies within \(C\delta\) of \(T_2\). Also the longitudinal separation of \(x'\) from \(i_0\) on \(T'_1\) is at least \(\kappa\). The shifted axes of \(T_1,T_2\) determine a two-plane. Subtracting the perpendicular components of the two endpoints of the segment from \(x'\) to \(i_0\) shows that the direction of \(T'_1\) is within \(C\delta/\kappa\) of this plane.

In a dyadic shell \(\phi\le\angle(T_1,T'_1)\le2\phi\), with \(\delta\le\phi\le1\), the allowed great-circle arc has length \(O(\phi)\). Covering its tangential coordinate at spacing \(\delta\), and the \(k-2\) perpendicular coordinates at spacing \(\delta\) in a strip of width \(C\delta/\kappa\), gives at most
\[
 C\kappa^{-(k-2)}N\phi                           \tag{5.17}
\]
possible directions. The shell below \(\delta\) is counted using \(\phi=\delta\). This packing count uses the ambient dimension \(k-1\).

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
For each \(f\in\mathcal F\), choose one angle \(a(f)\in\Omega_f^*\) and exactly \(h\) pairs from \(\mathcal P(a(f),f)\), using fixed orderings. Denote this set by \(R_f\). Thus \(|R_f|=h=\sigma N\) for every output, all its pairs come from one angle, and selecting it incurs no further loss. These \(Q\) sets are the inputs to the lift.

## 5.5. Lifting the selected fibers

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
The same \(u_*\) works for every selected pair.

If two such points lie in the same lifted \(\delta\)-cell, their horizontal coordinates \(y_2\) differ by \(O(\delta)\). Bounded longitudinal multiplicity permits \(O(1)\) second endpoint labels in that cell. For a fixed such label, the identity
\[
 b=\frac{a_0c}{c-u},\qquad |c-u|\ge c\kappa^2,
\]
shows that an \(O(\delta)\) variation of \(c,u\) changes \(b\) by at most \(C\kappa^{-4}\delta\). Hence there are at most \(C\kappa^{-4}\) first endpoint labels. Thus each lifted cell receives at most \(C\kappa^{-4}\) pairs, and the \(h\) pairs occupy at least \(c\kappa^4h\) lifted cells.

By (5.21), the cells lie in at most \(C\kappa^{-1}\) integer unit slabs in the last coordinate, with slab membership determined by cell centers. A fullest slab on each line contains at least \(c\kappa^5h\) cells, and at least one. Choose the common integer
\[
 K=\max\{1,\lfloor c\kappa^6h\rfloor\},\qquad
 \rho=K/N,                                         \tag{5.22}
\]
with the fixed constant small enough that every chosen slab contains \(K\) cells. Trim to a set \(V_f^0\) of exactly \(K\) cells and attach one original pair from \(R_f\) to each cell. Considering separately \(c\kappa^6h<1\) and \(c\kappa^6h\ge1\) gives
\[
 \rho\ge c\kappa^6\sigma,\qquad 0<\rho\le C.
\]
The initial incidence set \(\mathscr I_0=\{(f,v):f\in\mathcal F,\ v\in V_f^0\}\) has mass
\[
 I_0=|\mathscr I_0|=KQ=\rho NQ.                                  \tag{5.23}
\]
The choice \(K\ge1\) covers \(\kappa^6\sigma N<1\), so no assumption \(\lambda^2N\gg1\) is needed.

To apply (5.5), first observe that the horizontal slopes \(v_f=u_*u_2\) are bounded by a fixed constant. Thus \(v\mapsto(v,1)/\sqrt{1+|v|^2}\) is uniformly bi-Lipschitz on this slope range. For each fixed pivot label \(z_0\),
\[
 v_f=\bar z_0-\bar i_0+O_k(\delta),               \tag{5.24}
\]
where bars denote cell centers. Distinct outputs with this fixed \(z_0\) have distinct labels \(i_0\). Consequently, an \(O(\delta)\)-ball in slope space contains only \(O_k(1)\) such outputs, because their \(i_0\) labels lie in an \(O(\delta)\)-ball of the original grid. Color the bounded-degree graph joining slopes within \(c\delta\) using \(J_0=O_k(1)\) colors. Each color is direction-separated, and all colors are retained.

More generally, a graph-direction cap of radius \(r\ge\delta\) confines the labels \(i_0\) to a ball of radius \(C_kr\), by (5.24) and the graph chart. Every such label lies in \(E'\). The pruned bound (5.9) therefore gives
\[
 \#\{f:\text{fixed }z_0,\ \operatorname{dir}(\ell_f)\in B(w,r)\}
 \le C F(Nr)^d.                                   \tag{5.25}
\]
The choice of one angle per output makes the labels \(i_0\) distinct for fixed \(z_0\); this is needed for (5.25). Its cap coefficient is \(CF\), independent of \(\kappa\).

Group the lines by \(g=(z_0,j)\), with \(j\) the chosen unit slab, and let \(M_g\) be the group size. Translate the last coordinate by \(j\). Since a retained point has horizontal coordinate \(y_2\) in the original bounded region and the slopes are bounded, the unit graph segment through it lies in a fixed enlarged bounded region and has length comparable to one. A cell assigned to \([j,j+1]\) by its center has its lifted point at most \(C\delta\) outside the slab, so a fixed tube-width enlargement handles boundary cells. Thus (5.5) applies to each group and color with geometric constants independent of \(\kappa\), and \(\sum_gM_g=Q\).

## 5.6. Removing high multiplicities

Set \(r_*=q+e>1\), let \(m_g(v)\) count incidences in group \(g\), before separating colors, and define
\[
 H_{\rm cut}=C_eF\rho^{1-q-e}N^{d-d'+1+e}.        \tag{5.26}
\]
Delete incidences at cells for which \(m_g(v)>H_{\rm cut}\). We prove that at least \(I_0/2\) survive.

Let \(U_{g,c}\) be the union of deleted cells in group \(g\), color \(c\), let \(I_{g,c}\) be their incidence mass, and let \(M_{g,c}\) be the original line count of that color. Set \(s_{g,c}=I_{g,c}/(NM_{g,c})\) when \(M_{g,c}>0\), and omit empty colors. Some line shadings may be empty. Apply the cumulative estimate (5.5) and then weighted convexity to obtain
\[
 \begin{aligned}
 \sum_{g,c}\#U_{g,c}
 &\ge c_eF^{-1}N^{d'-d-e}\sum_{g,c}M_{g,c}s_{g,c}^{r_*}\\
 &\ge c_eF^{-1}N^{d'-d-e}Q
          \left(\frac{I_{\rm high}}{NQ}\right)^{r_*},
 \end{aligned}                                    \tag{5.27}
\]
where \(I_{g,\rm high}=\sum_c I_{g,c}\) and \(I_{\rm high}=\sum_g I_{g,\rm high}\). On the other hand, each group has at most \(I_{g,\rm high}/H_{\rm cut}\) high cells, and each such cell belongs to at most \(J_0\) colored unions. Hence
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
where multiplicities in the last expression count only retained incidences. The weights in (5.27) sum to \(Q\), so the number of groups causes no loss. Energy is counted with the original slab labels, undoing the translations used to apply (5.5).

## 5.7. The energy estimate

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

This also bounds the number of pairs \((g,v)\): the triple fixes \(z_0\), and the cell, in its original coordinates, fixes its slab.

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
This proves (5.34). \(\square\)

Here \(q\) includes the density losses from earlier recursive stages.

**Completion of the proof of Theorem 5.1.** Substitute (5.6) and (5.10). The \(N\)-exponent is exactly
\[
 (d'-d+1-e)+(d-2e)+(2m+2)=2m+3+d'-3e;
\]
the density exponent is \(p+2q+4+2e\), and the remaining factors are \(\xi^{p+3}S^3L^{-(p+4)}\). Moving the two additional inverse factors of \(E\) to the left proves (5.3), because \(e<1\) and \(0<\kappa<1\) imply
\[
 \kappa^{5(k-1)+6(q+e)+6}\ge\kappa^{5(k-1)+6q+12}.
\]
\(\square\)

## 5.8. The exponents after one step

Suppose \(B\le B_0L^A\), \(\xi\ge\xi_0L^{-A}\), and \(\theta\ge\theta_0L^{-A}\), with fixed \(B_0,\xi_0,\theta_0,\alpha>0\) and \(A\ge0\). Then
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
The second inequality uses \(S\le C_0\). At bounded scales, use \(E\ge1\). The exponents \(D,C\) are unchanged by these logarithmic bounds; constants and scale thresholds may depend on \(B_0,\xi_0,\theta_0,A,\alpha\).

Sections 7 and 8 remove the angular and two-ends restrictions. Each lift takes place in \(\mathbb R^{k+1}\). Constants may depend on the fixed parameters and finite recursion depth; uniformity as \(m\downarrow3\) is unnecessary.

# 6. Sampling restricted shadings

We either count cells with small marked multiplicity or sample discrete shadings on the same tubes. Each sampled cell has positive intersection with the full shading, allowing the comparison with original cells in Section 7.

**Lemma 6.1 (sampling).** Fix an integer $k\ge2$, fixed positive geometric constants, $0<s<1$, $0<\alpha<1-s$, $\beta>0$, and $A\ge0$. Put $h=N^{-1}$ and $L=\log(2N)$. Let $\mathcal T$ be $M\ge1$ tubes of length comparable to one and width comparable to $h$, contained in a fixed bounded region of $\mathbb R^k$, with one tube per $ch$-separated projective direction. In particular, $M\le C_kN^{k-1}$.

For each $T$, let $F_T\subset T$ be its measurable full shading and $G_T\subset F_T$ its marked subset. Assume, with constants independent of $N$ and $\lambda$:

1.  Density: $$c_0\lambda h^{k-1}\le |F_T|\le C_0\lambda h^{k-1},
      \qquad N^{-s}<\lambda\le1.
      \tag{6.1}$$

2.  Two ends: $$|F_T\cap B(x,r)|\le B r^\alpha |F_T|,
      \qquad h\le r\le1,
      \qquad 1\le B\le B_0L^A.
      \tag{6.2}$$

3.  Total marked mass: $$W_g:=h^{-k}\sum_T|G_T|\ge\xi\lambda NM,
      \qquad \xi\ge\xi_0L^{-A}>0.
      \tag{6.3}$$

4.  Angular broadness of the marks: for almost every $x$, every projective cap $\omega(v,r)$, and $h\le r\le1$, $$\sum_{T:\,\operatorname{dir}(T)\in\omega(v,r)}1_{G_T}(x)
      \le K r^\beta\sum_T1_{G_T}(x),
      \qquad 1\le K\le K_0L^A.
      \tag{6.4}$$

Let $\mathcal Q$ contain the $h$-grid cells with positive-measure intersection with $\bigcup_TF_T$, and put $\Omega=\bigcup_{Q\in\mathcal Q}Q$. Adding cells with zero-measure intersection is harmless. Define $$p_{TQ}=h^{-k}|F_T\cap Q|,\qquad
 p^g_{TQ}=h^{-k}|G_T\cap Q|,\qquad
 \mu_g(Q)=\sum_Tp^g_{TQ}.
 \tag{6.5}$$ Both probabilities lie in $[0,1]$, and $p^g_{TQ}\le p_{TQ}$.

There are $N_0$ depending only on the fixed parameters above and a dimensional threshold $a_0>0$ such that, for $N\ge N_0$, at least one of the following alternatives holds.

**(i) Cells with low marked multiplicity.** The cells with $0<\mu_g(Q)<a_0L$ carry at least $W_g/2$ of the expected marked mass and satisfy $$\#\{Q:0<\mu_g(Q)<a_0L\}
 \ge\frac{W_g}{2a_0L}.
 \tag{6.6}$$

**(ii) Discrete shadings.** On the same tubes there are full discrete shadings $Y_T\subset\mathcal Q$ and marks $H_T\subset Y_T$ such that $$\frac{c_0}{2}\lambda N\le\#Y_T\le2C_0\lambda N,
 \tag{6.7}$$ $$\#\{Q\in Y_T:q_Q\in B(x,r)\}
 \le C B r^\alpha\#Y_T
 \qquad(h\le r\le1),
 \tag{6.8}$$ and $$\sum_T\#H_T\ge W_g/4
 \ge\frac{\xi}{8C_0}\sum_T\#Y_T.
 \tag{6.9}$$ Here $q_Q$ denotes a cell center. At every marked cell every projective cap of radius $$\theta=\min\left\{\frac1{100},\frac12(1000K)^{-1/\beta}\right\}
 \tag{6.10}$$ contains at most one tenth of the marked tube directions there. In particular, $\theta\ge cL^{-A/\beta}$. All cell centers in $Y_T$ lie within $C_kh$ of $T$, and each longitudinal interval of length $h$ contains only $O_k(1)$ such centers. All tubes and directions are retained. Thus any input cap bound $\#\{T:\operatorname{dir}(T)\in\omega(v,r)\}\le A_{\rm cap}(Nr)^m$, with real $m$, holds unchanged for the output, although sampling itself does not require this hypothesis.

The output satisfies $$\bigcup_T\bigcup_{Q\in Y_T}Q\subset\Omega,
 \qquad
 \#\bigcup_TY_T\le\#\mathcal Q.
 \tag{6.11}$$ The cells in $\Omega$ may extend beyond $\bigcup_TF_T$.

**Proof.** The numbers $\mu_g(Q)$ and the low/high partition are deterministic. Call $Q$ low if $\mu_g(Q)<a_0L$, and high otherwise. If $$\sum_{Q\text{ low}}\mu_g(Q)\ge W_g/2,$$ then, omitting zero-mass cells, $$\frac{W_g}{2}
 \le\sum_{Q\text{ low}}\mu_g(Q)
 \le a_0L\,\#\{Q:0<\mu_g(Q)<a_0L\}.
 \tag{6.12}$$ This proves (i).

Otherwise $$W_{\rm high}:=\sum_{Q\text{ high}}\mu_g(Q)>W_g/2.
 \tag{6.13}$$ Choose independent uniform random variables $U_{TQ}$ on $[0,1]$, indexed by all tube-cell pairs with positive full mass. Select the full incidence $(T,Q)$ if $U_{TQ}\le p_{TQ}$, and select its mark if $U_{TQ}\le p^g_{TQ}$. By (6.5), every selected mark is a selected full incidence. Retain only marks in high cells, while keeping all selected full incidences.

We show that density, two ends, and angular control hold simultaneously with positive probability.

**Full density.** Write $X_T$ for the selected full count. Its mean is $$\mu_T=\sum_Qp_{TQ}=h^{-k}|F_T|\in[c_0\lambda N,C_0\lambda N].$$ The Poisson-binomial Chernoff estimates give $$\Pr\{X_T\notin[\mu_T/2,2\mu_T]\}
 \le2\exp(-\mu_T/12)
 \le2\exp(-cN^{1-s}).
 \tag{6.14}$$ A union bound over $C_kN^{k-1}$ tubes proves (6.7) with failure probability smaller than any fixed inverse power of $N$.

**Full two ends.** Test balls centered on an $h$-lattice in a fixed enlarged region, at dyadic radii $h,2h,4h,\ldots$ up to a radius comparable to one. There are $O_k(N^kL)$ tests. Every ball of radius $t\in[h,1]$ lies in a test ball with radius between $t$ and $C_kt$.

For a test ball of radius $r$, the sum of the means of selected cells whose centers it contains is at most $$h^{-k}|F_T\cap B(z,r+\sqrt{k}h)|
 \le C_k B r^\alpha\mu_T
 \le C_k C_0B r^\alpha\lambda N.
 \tag{6.15}$$ If the enlarged radius exceeds one, the original radius is bounded below by a dimensional constant, so total mass gives the same bound. All tested radii are at least $h$.

Choose the upper threshold $t_r=C_*B r^\alpha\lambda N$, where $C_*$ is large enough that $t_r\ge4\mathbb E X_{T,z,r}$. The elementary upper-tail estimate $$\Pr\{X\ge t\}\le(e\mathbb EX/t)^t
 \qquad(t>\mathbb EX)$$ then bounds the failure probability by $\exp(-c t_r)$. Its threshold satisfies $$t_r\ge c\lambda N h^\alpha
 >cN^{1-s-\alpha}.
 \tag{6.16}$$ Since $1-s-\alpha>0$, a union bound over $C_kN^{2k-1}L$ tube-ball pairs has failure probability $o(1)$. Dividing by $X_T\ge c_0\lambda N/2$ and passing from test balls to arbitrary balls proves (6.8), with constants independent of $N$, $\lambda$, and the shadings.

**Angular bounds in high cells.** Integrating (6.4) over a cell gives $$\sum_{T:\,\operatorname{dir}(T)\in\omega(v,r)}p^g_{TQ}
 \le Kr^\beta\mu_g(Q).
 \tag{6.17}$$ For $N\ge N_0$, the radius $2\theta$ in (6.10) is at least $h$. A $\theta$-net on projective direction space has at most $C_k\theta^{-(k-1)}$ elements. Every cap of radius $\theta$ lies in a net cap of radius $2\theta$. The expected number of marks in such a net cap is at most $\mu_g(Q)/1000$, by (6.10) and (6.17).

At a high cell $Q$, let $Z_Q$ be its actual marked multiplicity and $Z_{Q,\omega}$ its marked multiplicity in a net cap. Chernoff and the preceding elementary tail estimate give $$\Pr\{Z_Q<\mu_g(Q)/2\}\le e^{-\mu_g(Q)/8},$$ $$\Pr\{Z_{Q,\omega}>\mu_g(Q)/20\}
 \le(e/50)^{\mu_g(Q)/20}
 \le e^{-\mu_g(Q)/8}.
 \tag{6.18}$$ These tail bounds allow real thresholds. On the complementary events each radius-$\theta$ cap has at most $$\mu_g(Q)/20\le Z_Q/10$$ actual marks.

There are $O_k(N^k)$ cells. Since $\theta^{-1}$ is a fixed power of $L$, increasing $N_0$ ensures that the total number of high-cell and net-cap tests is at most $N^{k+2}$. One may take, for example, $a_0=64(k+4)$. Since high cells have $\mu_g(Q)\ge a_0L$, the sum of their failure probabilities is at most $$N^{k+2}e^{-a_0L/8}<1/8.
 \tag{6.19}$$ The density and two-ends failure probabilities in (6.14)--(6.16) sum to less than $1/8$ after another increase in $N_0$. The union bound gives a probability greater than $3/4$ that every required event holds.

Choose one such realization. By (6.13) and the high-cell lower multiplicity estimates, $$\sum_T\#H_T
 =\sum_{Q\text{ high}}Z_Q
 \ge\frac12W_{\rm high}>\frac14W_g.$$ Moreover $\sum_T\#Y_T\le2C_0\lambda NM$, so (6.3) implies (6.9). The axes are unchanged and every sampled cell has positive full intersection, which preserves separation and gives the stated support, distance, and longitudinal multiplicity bounds. This proves (ii). $\square$

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
Equation (7.2) verifies \(\eta>0\).

**Proof.** We may weaken \(\alpha\) to \(\min\{\alpha,1/4\}\). Fix
\[
 0<\beta<\min\{1,m-D\}.
\]
Apply the angular decomposition and density and mark refinements of Section 3. Use one common angular radius \(\tau\), and choose the comparable density class by marked incidence mass. If its common density is \(\lambda_1\), the retained pieces satisfy, with \(L=\log(2N)\),
\[
 \lambda L^{-A}\le\lambda_1\le C\lambda,
 \qquad \sum_jM_j\ge ML^{-A}.
\]
At each marked point, discard the selected marks if their multiplicity is less than a sufficiently small inverse logarithmic fraction of the previous marked multiplicity. This costs at most one quarter of the selected mass. Then discard pieces whose remaining marked mass is less than a sufficiently small inverse logarithmic fraction of their full mass, losing at most another quarter. The retained pieces have comparable full densities, logarithmic two-ends and broadness constants, and marked mass at least an inverse logarithmic fraction of full mass.

Write \(F_j(T)=Y_j(T)\) for the restricted full shading of a piece and \(G_j(T)\subset F_j(T)\) for its final marks. If \(U_0\) is the input union, these old-grid restrictions satisfy
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

In the high-cell sampling alternative, write \(F_j^{\mathrm s}(T)\) for the sampled full shadings and
\[
 E_j^{\mathrm s}:=\#\bigcup_TF_j^{\mathrm s}(T).
\]
Let \(\mathcal Q_j\) be the new grid cells meeting \(A_j\bigcup_TF_j(T)\). Each transformed old cube meets boundedly many new cubes, so
\[
 E_j^{\mathrm s}\le\#\mathcal Q_j\le C_kE_j.
\]
Apply the core to \(E_j^{\mathrm s}\), weakening \((S')^{3/4}\) to \(C_k^{-1/4}S'\) since \(S'\le C_k\). Sum only the original counts \(E_j\), to which the overlap bound applies. The transformed normalized volume is \(\asymp\tau E_j\).

A continuous estimate of the same exponents would give \(E_j\gtrsim\tau^{-1}(N\tau)^{D-e}\lambda_1^CS'\); sampling gives the bound without \(\tau^{-1}\). Their angular factors are respectively \(\tau^{D-m-1+\beta-e}\) and \(\tau^{D-m+\beta-e}\), so the sampled argument requires \(D<m\).

Summing (7.1) over the angular pieces with overlap \(\lesssim\tau^{-\beta}\) produces

\[
\tau^{D-m+\beta-\epsilon}.
\]

This factor is at least one because \(D-m+\beta<0\). Thus (7.1), once proved, yields the proposition after summation and absorption of logarithmic losses. We prove (7.1) in four cases.

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
   Lemma 6.1 controls all \(O_k((N')^{2k-1}\log N')\) tube-ball tests and the angular-net tests simultaneously. Its output satisfies the transverse core hypotheses with logarithmic conditioning. Applying the core gives
   \[
   E_j^{\mathrm s}\ge c_e(N')^{D-e}\lambda_1^{C+e}
                 \frac{M_j}{(N')^m}.
   \]
   Use \(E_j^{\mathrm s}\le\#\mathcal Q_j\le C_kE_j\). Since \(\lambda_1>(N')^{-1/3}\), the extra density factor costs at most \((N')^{-e/3}\), proving (7.1) with an arbitrarily small scale loss. The test counts depend on the ambient sphere, even when \(m\) is real.

   Also \(\sigma N'\gtrsim\lambda_1^2N'>(N')^{1/3}\), up to fixed factors. Equations (5.22)–(5.23) give lifted mass \(\rho_{\rm lift}N'Q\) with \(\rho_{\rm lift}\ge c\kappa^6\sigma\). Integer trimming and the one-tube bound cover the remaining bounded scales.

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

Summing (7.1) over the original pieces proves the proposition, with the exponents in (5.35). \(\square\)

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

The localization of Section 3 selects a common radius \(\rho\in[\delta,1]\) and refined old density \(\nu\), with
\[
 \nu\gtrsim L^{-A_0}\rho^\alpha\lambda,
 \qquad \nu\lesssim\rho,
 \qquad L=\log(2N).
\]
Here \(A_0\) depends on the fixed \(\alpha\) and normalizations. A common dyadic class retains an inverse logarithmic fraction of the tubes. Each localization ball meets boundedly many cubes of a common aligned \(\rho\)-grid. Restrict its shading to one cube carrying a fixed fraction of its cells; this preserves relative two ends up to a fixed constant. These cubes are unions of old cells. Assign each tube to its chosen cube, so the resulting spatial groups have disjoint restricted unions.

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
The retained fraction \(\rho^m\) comes from the full cap condition.

If \(C\le D\), the bound \(\nu\lesssim\rho\) gives \(\nu^C\rho^{D-C}\gtrsim\nu^D\). If \(C>D\), then \(\rho\le1\) gives \(\nu^C\rho^{D-C}\ge\nu^C\). Thus in both cases
\[
 \nu^C\rho^{D-C}\gtrsim\nu^P
 \gtrsim L^{-A_0P}\delta^{\alpha P}\lambda^P,
 \qquad P=\max(D,C).
\]
Choose \(\alpha P\) below one third of the final scale-loss budget. With \(\alpha\) fixed, choose \(e\) and absorb the logarithms into the remaining budget. This proves the discrete estimate; only its constants depend on \(\alpha\). \(\square\)

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

Shrink each measurable shading to volume comparable to \(\lambda|T|\). We must prove
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

Let \(U=\bigcup_TY(T)\). For each old grid cube \(Q\), put \(w_Q=|U\cap Q|/|Q|\). A unit tube meets at most \(CN\) cubes, so those with \(w_Q<c\lambda\) contain at most a small fixed fraction of its shaded mass, for sufficiently small \(c\). Remove these incidences. Partition the remaining cubes into dyadic occupancy classes; there are \(O(L)\) because \(\lambda>\delta\), where \(L=\log(2N)\).

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
Absorb the remaining fixed powers of \(L\) into an arbitrarily small scale loss. Finally,
\[
 \delta^kN^{D-m}\lambda^PM
 =\delta^{m+1-D}\lambda^P\sum_T|T|
\]
up to fixed tube-volume constants. This proves the measurable assertion. \(\square\)

# 9. Iteration and maximal consequences

## 9.1. Iteration using the Wolff input

Section 4 gives
\[
 K\left(m,\frac{m+3}{2},\frac{m+3}{2}\right)
 \qquad(m>3).
\]
Here \(\lambda\gtrsim N^{-1}\) absorbs the arbitrarily small density loss into the scale loss. Section 8.1 gives the measurable form and, for full directions in \(\mathbb R^n\), the seed \(\mathsf M_n((n+2)/2)\).

Given \(\mathsf M_n(d)\), apply the direct-input form of Theorem 5.1 with
\[
 m=n-1,\qquad p=d,\qquad d'=q=\frac{d+3}{2}.
\]
Corollary 4.3 supplies the cumulative lifted input with cap exponent \(d\) in \(\mathbb R^{n+1}\). The output exponents are
\[
 D=\frac{4n+d+5}{8},\qquad C=\frac{2d+7}{4}.
                                                               \tag{9.1}
\]
When \(D<n-1\) and \(C\le D\), Propositions 7.1 and 8.1 give \(\mathsf M_n(D)\). The density cutoff in Section 7 is admissible since
\[
 \frac{n+2}{2}-D+\frac{C-2}{3}
 =\frac{d+7}{24}>0.                               \tag{9.2}
\]

Starting at \(d_0=4\) for \(n=6\), or \(d_0=5\) for \(n=8\), gives
\[
 \begin{gathered}
 d_{j+1}=\frac{4n+5+d_j}{8},\\
 d_j^{(6)}=\frac{29}{7}-\frac{1}{7\cdot8^j},\qquad
 d_j^{(8)}=\frac{37}{7}-\frac{2}{7\cdot8^j}.
                                                               \tag{9.3}
 \end{gathered}
\]
For \(4\le d\le29/7\) when \(n=6\), and \(5\le d\le37/7\) when \(n=8\),
\[
 D-C=\frac{4n-3d-9}{8}>0,
 \qquad D<n-1.
\]
Thus the reductions apply at every finite stage.

| Dimension | Seed | First two iterates | Limit |
|---:|---:|---:|---:|
| \(6\) | \(4\) | \(33/8,\ 265/64\) | \(29/7\) |
| \(8\) | \(5\) | \(21/4,\ 169/32\) | \(37/7\) |

The published eight-dimensional maximal exponent \(21/4\) [HRZ19, Z19] can also serve as the base input, starting this iteration one stage later.

For a prescribed \(\varepsilon>0\), choose a finite \(j\) with \(d_\infty-d_j\le\varepsilon/2\), where \(d_\infty=(4n+5)/7\). The stage-\(j\) bound with loss \(\varepsilon/2\) implies \(\mathsf M_n(d_\infty)\), since
\[
 \delta^{n-d_j+\varepsilon/2}\lambda^{d_j}
 \ge\delta^{n-d_\infty+\varepsilon}\lambda^{d_\infty}.
\]
The constant may depend on \(j\), hence on \(\varepsilon\).

## 9.2. Iteration of real-cap estimates

Define
\[
 a_0=\frac12,\qquad a_{j+1}=\frac{2+a_j^2}{4},
 \qquad d_j(m)=3+a_j(m-3),
 \qquad p_j(m)=\max\{d_j(m),4\}.                    \tag{9.4}
\]
We prove \(K(m,d_j(m),p_j(m))\) for every fixed \(m>3\), finite \(j\), and fixed integer ambient dimension \(k\ge m+1\). The recurrence for \(a_j\) and its limiting set exponent are due to [KT02, Section 6].

The seed follows by increasing the density exponent in the fractional Wolff estimate from \(d_0(m)=(m+3)/2\) to \(p_0(m)\). Suppose the assertion holds at depth \(j\) for every fixed real cap parameter above three. Apply it at \(m\) and, in the lifted integer ambient dimension, at \(d=d_j(m)\). This gives
\[
 d'=d_j(d_j(m))=3+a_j^2(m-3),
 \quad p=p_j(m),\quad q=p_j(d_j(m)).
\]
Corollary 8.2 has output set exponent
\[
 D=\frac{2m+3+d'}4=d_{j+1}(m).
\]
Since \(a_j\) increases from \(1/2\) and stays below \(2-\sqrt2<1\),
\[
 3<d'<d\le D<m.
\]
Set \(P=\max(D,4)\). Then \(p,q\le P\), so
\[
 C=\frac{p+2q+4}{4}
 \le\frac{3P+4}{4}\le P.                          \tag{9.5}
\]
Increasing the output density exponent \(\max(D,C)\) to \(P=p_{j+1}(m)\) completes the induction. The density exponent four is needed to close the argument when the set exponent is below four.

At any finite depth, only finitely many fixed cap parameters occur, all greater than three. Constants may depend on them; no uniformity as \(m\downarrow3\) is needed.

The slopes converge to the smaller fixed point of \(a=(2+a^2)/4\):
\[
 a_\infty=2-\sqrt2,\qquad
 d_\infty(m)=3+(2-\sqrt2)(m-3).                    \tag{9.6}
\]
For a prescribed scale loss \(\varepsilon\), choose finite \(j\) with \(d_\infty(m)-d_j(m)<\varepsilon/2\). Apply the depth-\(j\) bound with loss \(\varepsilon/2\) and use
\[
 \lambda^{p_j(m)}\ge
 \lambda^{\max\{d_\infty(m),4\}}.
\]
As in Section 9.1, the exponent gap is absorbed by the remaining scale loss. This proves the limiting cap estimate with density exponent \(\max\{d_\infty(m),4\}\). If \(m=n-1\) and \(n\ge6\), then \(d_\infty(m)>4\); Section 8.1 therefore gives Theorem 1.1.

| Depth | Slope \(a_j\) | Dimension 6: \(d_j(5)\) | Dimension 8: \(d_j(7)\) |
|---:|---:|---:|---:|
| \(0\) | \(1/2\) | \(4\) | \(5\) |
| \(1\) | \(9/16\) | \(33/8\) | \(21/4\) |
| \(2\) | \(593/1024\) | \(2129/512\) | \(1361/256\) |
| \(3\) | \(2448801/4194304\) | \(8740257/2097152\) | \(5594529/1048576\) |
| Limit | \(2-\sqrt2\) | \(7-2\sqrt2\) | \(11-4\sqrt2\) |

The two iterations agree at the first step. The real-cap iteration then uses the improved lifted estimates and gives the stronger limits.

## 9.3. Maximal operator bounds

Define
\[
 K_\delta f(v)=\sup_{T\parallel v}\frac1{|T|}\int_T|f(x)|\,dx.
\]
Assume \(\mathsf M_n(a)\). Choose separated directions in a level set of \(K_\delta1_E\), select one witnessing tube per direction, and apply (1.1). Enlarging the direction caps costs only fixed constants, giving
\[
 |\{v:K_\delta1_E(v)>\lambda\}|
 \le C_\varepsilon\delta^{-(n-a)-\varepsilon}
                         \lambda^{-a}|E|.          \tag{9.7}
\]
Interpolating this restricted weak bound with the trivial \(L^\infty\) bound gives, for every fixed \(r>a\), a strong \(L^r\) norm bound \(C_{r,e}\delta^{-(n-a+e)/r}\). Also,
\[
 K_\delta f(v)\le C\delta^{-(n-1)}\|f\|_1,
\]
which gives a strong \(L^1\) bound of the same size because the direction sphere has finite measure. Interpolate these strong bounds to exponent \(a\), with
\[
 \vartheta=\frac{r-a}{a(r-1)},\qquad
 \frac1a=\frac{1-\vartheta}{r}+\vartheta.
\]
The scale exponent is
\[
 (1-\vartheta)\frac{n-a+e}{r}+\vartheta(n-1).
\]
Choose fixed \(r>a\) sufficiently close to \(a\), then fixed \(e>0\) sufficiently small, to make this less than \((n-a)/a+\varepsilon\). Thus
\[
 \|K_\delta f\|_{L^a(S^{n-1})}
 \le C_\varepsilon\delta^{-(n-a)/a-\varepsilon}
                         \|f\|_{L^a(\mathbb R^n)}. \tag{9.8}
\]
The scale exponents for the limits in Section 9.1 are \(13/29\) in dimension six and \(19/37\) in dimension eight. The same argument applies to the stronger exponents in (1.2).

# A. The bush estimate and alternative iterations

The Christ–Duoandikoetxea–Rubio de Francia exponent in ambient dimension \(r\) is \((r+1)/2\), or \((m+2)/2\) for direction-cap parameter \(m=r-1\); see [KT00, Figure 1 and Section 2]. We prove its real-cap, cumulative-density form and apply it in the pivot theorem.

## A.1. The cumulative-density bush estimate

**Lemma A.1.** Let \(M\ge1\) unit \(N^{-1}\)-tubes in a fixed bounded region of \(\mathbb R^k\) satisfy
\[
\#\{T:\operatorname{dir}(T)\in B(v,r)\}
\le A(Nr)^m,
\qquad N^{-1}\le r\le1,
\]
where \(m>0\) and \(A\ge1\). If their discrete shadings, possibly empty, have total incidence mass at least \(sNM\), where \(0<s\le1\), then their union count satisfies
\[
E\ge c_{k,m}A^{-1}N^{1-m/2}s^{(m+2)/2}M.
\tag{A.1}
\]
The constant depends only on \(k,m\) and the fixed tube and grid normalizations.

**Proof.** A fixed cover of the projective sphere by radius-one caps gives
\[
M\le C_k A N^m.
\]
When \(sN\) is bounded, the right side of (A.1) is at most a fixed multiple of \((sN)^{(m+2)/2}\); the nonempty union has \(E\ge1\), proving the estimate after choosing the constant small enough.

Otherwise, delete tubes with fewer than \(sN/2\) shaded cells. At least \(sNM/2\) incidences remain, so some cell \(x\) belongs to
\[
\mu\ge \frac{sNM}{2E}
\]
retained tubes. A ball of radius \(c_1s\) about its center meets each tube in at most \(C_k(c_1sN+1)\) cells. Choose \(c_1\) small enough and the threshold for \(sN\) large enough that each tube through \(x\) retains at least \(c_2sN\) shaded cells outside this ball.

A tube through \(x\) and an outside cell \(y\) has direction within \(C_kN^{-1}/|x-y|\) of the projective direction of \(y-x\), with \(x,y\) denoting cell centers. Since \(|x-y|\ge c_1s\), the cap condition bounds the number of these tubes through \(y\) by \(C_{k,m}A s^{-m}\). Fixed covers handle the endpoints of the allowed cap-radius range. Counting outside incidences gives
\[
E\ge \frac{c\mu sN}{A s^{-m}}
\ge c A^{-1}s^{m+2}N^2M/E.
\]
Taking square roots and using \(M\le C_kAN^m\) gives
\[
\begin{aligned}
E&\ge cA^{-1/2}s^{(m+2)/2}N M^{1/2}\\
 &\ge c'A^{-1}N^{1-m/2}s^{(m+2)/2}M.
\end{aligned}
\]
\(\square\)

Neither two ends nor comparable per-tube densities were needed. The last step makes the estimate linear in \(M\).

## A.2. Iteration with the bush input

In original ambient dimension \(n\), take \(m=n-1\). For a lifted family with cap parameter \(d\) in \(\mathbb R^{n+1}\), Lemma A.1 supplies (5.5) with
\[
d'=q=\frac{d+2}{2},\qquad
E_{\mathrm{lift}}\gtrsim F^{-1}N^{d'-d}\rho^qQ.
\]
The constant is independent of \(F\); weakening the estimate allows the scale and density losses in (5.5). The direct-input form of Theorem 5.1 permits these exponents even when \(d'\le3\).

With base density exponent \(p=d\), (5.35) becomes
\[
D=\frac{4n+d+4}{8},\qquad
C=\frac{d+3}{2},\qquad
D-C=\frac{4n-3d-8}{8}.
\tag{A.2}
\]
The bush estimate in \(\mathbb R^n\) supplies \(d_0=(n+1)/2\), giving
\[
d_{j+1}=\frac{4n+d_j+4}{8},\qquad
d_\infty=\frac{4n+4}{7},\qquad
d_j=d_\infty+(d_0-d_\infty)8^{-j}.
\tag{A.3}
\]

For every integer \(n\ge5\), this sequence increases to \(d_\infty\). Throughout, \(1<d<n-1\), \(q\ge2\), and \(C>2\). The minima of \(D-C\) and \(n-1-D\) occur at the limit:
\[
D-C=\frac{4n-17}{14}>0,
\qquad n-1-D=\frac{3n-11}{7}>0.
\]
With \(w=(n+2)/2\), the density cutoff in Proposition 7.1 has margin
\[
w-D+\frac{C-2}{3}
=\frac{d+8}{24}>0.
\tag{A.4}
\]
Propositions 7.1 and 8.1 therefore remove the angular and two-ends restrictions with density exponent \(\max(D,C)=D\). Section 8.1 converts the result to measurable shadings for the next base input. We use the direct-input theorem, not the narrower parameter range of Corollary 8.2.

Given \(\varepsilon>0\), choose finite \(j\) with \(d_\infty-d_j<\varepsilon/2\) and use that stage with loss \(\varepsilon/2\). Since \(0<\delta,\lambda\le1\),
\[
\delta^{n-d_j+\varepsilon/2}\lambda^{d_j}
\ge \delta^{n-d_\infty+\varepsilon}\lambda^{d_\infty}.
\]
Thus the limiting maximal exponent is \((4n+4)/7\), with arbitrary positive scale loss. It improves Wolff's bound precisely for \(n\ge7\), since
\[
\frac{4n+4}{7}-\frac{n+2}{2}=\frac{n-6}{14}.
\]

## A.3. Dependence on the lifted exponents

The following inputs give different fixed points:

| Lifted input in cap parameter \(d\) | Set exponent \(d'\) | Density exponent \(q\) | Fixed point for base input \(p=d\) |
|---|---:|---:|---:|
| Fractional Wolff | \((d+3)/2\) | \((d+3)/2\) | \((4n+5)/7\) |
| CDR bush | \((d+2)/2\) | \((d+2)/2\) | \((4n+4)/7\) |
| Bush with weakened set exponent | \((d+1)/2\) | \((d+2)/2\) | \((4n+3)/7\) |

For the third row, weaken only the power of \(N\) in Lemma A.1 and keep \(q=(d+2)/2\). Theorem 5.1 gives
\[
D=\frac{4n+d+3}{8},\qquad C=\frac{d+3}{2}.
\]
From \(d_0=(n+1)/2\), the iterates are
\[
d_j=\frac{4n+3}{7}
+\left(\frac{n+1}{2}-\frac{4n+3}{7}\right)8^{-j}.
\]
At the limit,
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
Thus the same reductions apply for every integer \(n\ge5\).

The historical threshold \(n\ge9\) for \((4n+3)/7\) concerns improvement over Wolff:
\[
\frac{4n+3}{7}-\frac{n+2}{2}=\frac{n-8}{14}.
\]
Katz–Tao [KT02, Section 5] use Wolff in lower dimensions. Their sliced argument yields
\[
E\gtrsim N\lambda^{(2n+14)/7}M^{4/7},
\]
and uses \(n>8\) to obtain the required density power. That intermediate density exponent belongs to their sliced construction; the pivot calculation here uses the lifted density exponent \(q=(d+2)/2\) and the reduction conditions checked above.

# B. Comparison with cited maximal estimates

Set
\[
 B_n=\max_{\substack{2\le \ell\le n\\ \ell\in\mathbb Z}}\min\left\{
 n-\ell+2,\frac{n^2+\ell^2+n-\ell}{2n}\right\},
 \qquad
 K_n=3+(2-\sqrt2)(n-4).
\]
Zahl [Z19, Theorem 1.5, equation (1.6)] gives the maximal exponent \(B_n\). Hickman–Rogers–Zhang [HRZ19, Theorem 1.2 and Figure 1] give the same values: their adjoint threshold \(r_n\) converts to \(B_n=r_n/(r_n-1)\). The table compares these cited estimates with the real-cap iteration, without claiming an exhaustive survey of subsequent literature. Decimals are rounded to six places.

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

† The five-dimensional row is numerical only. The density exponent \(p_j(m)=\max\{d_j(m),4\}\) does not give a diagonal maximal estimate at \(K_5<4\); the theorem applies to integer \(n\ge6\).

For \(6\le n\le15\), the claimed exponent exceeds \(B_n\) exactly when \(n=6,8,10,11,13,15\); compare [HRZ19, Section 9.2 and Figure 5]. In dimension eight, the first step \(21/4\) equals the cited benchmark, while \(37/7\) and \(11-4\sqrt2\) exceed it. In dimension six, \(33/8\) already exceeds the benchmark \(4\).

These numerical exponents have precedents as set bounds. Katz–Tao [KT00, p. 14] record the Hausdorff bound \((4n+5)/7\), including \(29/7\) and \(37/7\). Their real-cap iteration [KT02, Definition 6.1 and Theorem 6.2] gives \(K_n\). The contribution asserted here is the arbitrary-density maximal estimate with the same density exponent.

# References

[HRZ19] J. Hickman, K. M. Rogers, and R. Zhang, *Improved bounds for the Kakeya maximal conjecture in higher dimensions*, American Journal of Mathematics **144** (2022), no. 6, 1511–1560; arXiv:1908.05589. [Preprint](https://arxiv.org/abs/1908.05589).

[KT00] N. H. Katz and T. Tao, *Recent progress on the Kakeya conjecture*, arXiv:math/0010069 (2000). [Preprint](https://arxiv.org/abs/math/0010069).

[KT02] N. H. Katz and T. Tao, *New bounds for Kakeya problems*, Journal d'Analyse Mathématique **87** (2002), 231–263; arXiv:math/0102135. [Preprint](https://arxiv.org/abs/math/0102135).

[W95] T. H. Wolff, *An improved bound for Kakeya type maximal functions*, Revista Matemática Iberoamericana **11** (1995), no. 3, 651–674. [DOI: 10.4171/RMI/188](https://doi.org/10.4171/RMI/188).

[WZ25] H. Wang and J. Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025). [Preprint](https://arxiv.org/abs/2502.17655v1).

[Z19] J. Zahl, *New Kakeya estimates using Gromov's algebraic lemma*, Advances in Mathematics **380** (2021), article 107596; arXiv:1908.05314. [Preprint](https://arxiv.org/abs/1908.05314).

[Z25] J. Zahl, *A Survey of the Kakeya conjecture, 2000–2025*, arXiv:2512.09397v1 (2025). [Preprint](https://arxiv.org/abs/2512.09397v1).
