---
{
  "id": "critical-exponents",
  "title": "Critical exponent conventions",
  "subtitle": "Power laws, logarithmic limits and spatial scales",
  "kind": "concept",
  "category": "General theory",
  "summary": "A logarithmic exponent records a leading power and can coexist with unbounded logarithmic corrections. The order parameter, susceptibility, volume tail, Euclidean arm and two-point function use different limits and conventions.",
  "context": ["The parameter is the homogeneous opening probability $p$, so the symbol $\\beta$ below denotes an exponent, not an intensity.", "For the two one-sided parameter limits, assume $0<p_c<1$ and the stated observables are finite and positive where their logarithms are used.", "No existence or numerical value of a critical exponent is asserted for a model merely by introducing the notation."],
  "related": ["criticality", "susceptibility", "triangle-condition", "branching-processes", "cutoff-families"],
  "sourceIds": ["perclib-log-exponent", "perclib-tail-comparison", "perclib-window-hyperscaling", "perclib-damped-window-tails"],
  "aliases": ["critical exponent", "logarithmic exponent", "one-arm exponent", "anomalous dimension", "power law", "logarithmic correction"],
  "prototypeUses": []
}
---

## Three strengths of asymptotic statement {#section-asymptotics}

<a id="tag-PHLF" data-assertion="definition" data-title="Asymptotic equivalence, comparison and logarithmic power exponent"></a><p>For eventually positive functions $f,g$ as $x\to\infty$, write $f\sim g$ if $f(x)/g(x)\to1$. Write $f\asymp g$ if there are constants $0&lt;c\leq C&lt;\infty$ such that $cg(x)\leq f(x)\leq Cg(x)$ for all sufficiently large $x$. A logarithmic power exponent $\alpha\in\mathbb R$ means</p><div class="math-display">$$\lim_{x\to\infty}\frac{\log f(x)}{\log x}=\alpha,$$</div><p>equivalently $f(x)=x^{\alpha+o(1)}$. This is a weaker statement than $f\asymp x^\alpha$. At a parameter approaching zero, the corresponding definition uses $\log f(\varepsilon)/\log\varepsilon$ as $\varepsilon\downarrow0$; the denominator is negative, so inequalities must be handled with that sign in mind.</p>

<a id="tag-UBFE" data-assertion="proposition" data-title="Power comparisons imply logarithmic exponents but not conversely"></a><p>For eventually positive $f$ and real $\alpha$, $f\sim c x^\alpha$ with $c&gt;0$ implies $f\asymp x^\alpha$, which implies logarithmic exponent $\alpha$. The converse implications fail. For any fixed real $b,c$,</p><div class="math-display">$$f(x)=x^\alpha(\log x)^b(\log\log x)^c$$</div><p>has logarithmic exponent $\alpha$, for sufficiently large $x$, but is not comparable to $x^\alpha$ unless $b=c=0$.</p><p><em>Proof.</em> Equivalence bounds the ratio above and below eventually. Two-sided power comparison gives $\log f(x)=\alpha\log x+O(1)$, proving the logarithmic limit. For the displayed function, division of its logarithm by $\log x$ gives</p><div class="math-display">$$\alpha+b\frac{\log\log x}{\log x}+c\frac{\log\log\log x}{\log x}\longrightarrow\alpha.$$</div><p>If $b\ne0$, the ratio to $x^\alpha$ tends to zero or infinity because $\log\log x$ dominates $\log\log\log x$; if $b=0$ and $c\ne0$, the same conclusion follows directly. Finally, $x^\alpha(2+\sin\log x)$ is comparable to $x^\alpha$ but is not asymptotic to any constant multiple of it.</p><p>Thus knowing a leading exponent does not settle logarithmic corrections or an amplitude. A statement written with $\asymp$ should not be justified merely by a logarithmic limit.</p>

## Parameter and volume exponents {#section-parameter}

<a id="tag-U5MC" data-assertion="definition" data-title="Logarithmic order-parameter, susceptibility and volume-tail exponents"></a><p>Fix a root $o$ and write $\theta(p)=\mathbb P_p(|K_o|=\infty)$, $\chi(p)=\mathbb E_p|K_o|$, and $a(n)=\mathbb P_{p_c}(|K_o|\geq n)$. When the following limits exist with the indicated finite values, the logarithmic exponent conventions are</p><div class="math-display">$$\beta=\lim_{\varepsilon\downarrow0}\frac{\log\theta(p_c+\varepsilon)}{\log\varepsilon},\qquad \gamma=-\lim_{\varepsilon\downarrow0}\frac{\log\chi(p_c-\varepsilon)}{\log\varepsilon},\qquad \frac1\delta=-\lim_{n\to\infty}\frac{\log a(n)}{\log n}.$$</div><p>The first limit requires $\theta(p_c+\varepsilon)&gt;0$ for sufficiently small $\varepsilon$; the second requires finite positive subcritical susceptibility; the third requires eventually positive tails and defines a finite positive $\delta$ when its reciprocal limit lies in $(0,\infty)$. In this notation the powers are respectively $\varepsilon^{\beta+o(1)}$, $\varepsilon^{-\gamma+o(1)}$ and $n^{-1/\delta+o(1)}$.</p><p>These are definitions conditional on existence of limits, not assertions that all models have exponents. Stronger claims such as $\chi(p_c-\varepsilon)\asymp\varepsilon^{-\gamma}$ must be stated separately. If $\theta(p_c)&gt;0$, then $a(n)\downarrow\theta(p_c)$ and its reciprocal-volume-exponent limit is zero, not a positive $1/\delta$. A convention allowing $\delta=\infty$ may encode that limit, but the finite-positive convention above does not.</p><p>The two parameter limits also require room on the appropriate side of $p_c$. At $p_c=1$, there is no supercritical homogeneous-probability interval within $[0,1]$; writing its order-parameter exponent formula would not define a limit of this model. Extended intensity parametrizations require their own endpoint conventions.</p>

## Spatial exponents and the one-arm reciprocal {#section-spatial}

<a id="tag-BLNL" data-assertion="definition" data-title="Euclidean one-arm and two-point exponent conventions"></a><p>For nearest-neighbour percolation on $\mathbb Z^d$ rooted at $o=0$, set $\Lambda_r=[-r,r]^d\cap\mathbb Z^d$ for positive integers $r$, and let $\partial\Lambda_r=\{x:\|x\|_\infty=r\}$. Put $\pi(r)=\mathbb P_{p_c}(o\leftrightarrow\partial\Lambda_r)$. When the relevant positive-probability logarithmic limits exist, define</p><div class="math-display">$$\frac1\rho=-\lim_{r\to\infty}\frac{\log\pi(r)}{\log r},\qquad d-2+\eta=-\lim_{\|x\|\to\infty}\frac{\log\tau_{p_c}(o,x)}{\log\|x\|}.$$</div><p>A finite positive $\rho$ requires a positive finite reciprocal limit. The two-point limit is a limit over all lattice vertices tending to infinity; a limit along one fixed direction alone is not the same assertion. Any fixed norm may be used in its denominator, since norms on $\mathbb R^d$ are comparable.</p><p>Under this convention a Euclidean arm decay $r^{-2+o(1)}$ corresponds to $\rho=1/2$, not $\rho=2$. An author who calls the decay power itself the one-arm exponent uses the reciprocal convention. Intrinsic arms instead ask for vertices at large graph distance inside the open cluster. They are different events and need not have the same exponent.</p><p>For long-range models, the event of hitting this vertex boundary need not coincide with reaching outside the box: an edge can jump across it. Such models must specify the spatial arm event before using an exponent symbol. A correlation-length exponent likewise requires a chosen definition of correlation length; a symbol $\nu$ alone does not identify an observable.</p>

<p>These symbols, the reciprocal convention for $\rho$, and several predicted values and logarithmic corrections are standard. This article fixes the conventions and separates the strengths of the asymptotic statements. It does not establish the listed predictions. In particular, a branching-process calculation is not by itself a Euclidean spatial theorem, and thermodynamic consequences of a triangle condition should not be reported as a proof of every spatial exponent without the additional geometric inputs.</p>

## Counting clusters from a sampled vertex {#section-box-counting}

<a id="tag-OB0A" data-assertion="proposition" data-title="Finite-window cluster moments under uniform root sampling"></a>
<p>Let $\Lambda$ be a nonempty finite vertex set in any random graph. Partition $\Lambda$ by connectivity in the full graph, and denote the nonempty intersection sizes by $S_1,\ldots,S_k$. Choose $U$ uniformly from $\Lambda$, independently of the graph, and put $X=|K_U\cap\Lambda|$. For every real $m\geq0$,</p>
<div class="math-display">$$\mathbb E X^m=\frac1{|\Lambda|}\mathbb E\sum_{i=1}^k S_i^{m+1}.$$</div>
<p>For $0&lt;a\leq b&lt;\infty$ and $v&gt;0$, let $N$ count the intersections with $av\leq S_i\leq bv$. Their contribution to the root moment satisfies</p>
<div class="math-display">$$\frac{(av)^{m+1}}{|\Lambda|}\mathbb EN\leq\mathbb E\bigl[X^m\mathbf1_{\{av\leq X\leq bv\}}\bigr]\leq\frac{(bv)^{m+1}}{|\Lambda|}\mathbb EN.$$</div>
<p><em>Proof.</em> Conditional on the graph, exactly $S_i$ choices of $U$ have $X=S_i$. Average over the $|\Lambda|$ possible roots, then over the graph. Restricting the sum to the indicated sizes and bounding each $S_i^{m+1}$ proves the inequalities.</p>
<p>The partition uses full-graph connectivity: paths may leave and re-enter $\Lambda$. For clusters of the induced graph, the same counting identity applies to that different partition. Neither version identifies the sampled-root moment with the moment at the centre of the box. Translation invariance alone does not remove the dependence of a window intersection on the root's position within the window.</p>

## What the hyperscaling picture assumes {#section-hyperscaling}

<a id="tag-DEZI" data-assertion="proposition" data-title="Exponent relations conditional on finite-box moment and tail matching"></a>
<p>Let $\Lambda_r$ be finite windows with $|\Lambda_r|\asymp r^d$, where $d&gt;0$, and use the sampled-root variable $X_r$ and intersection sizes $S_{r,i}$ above. Suppose there are scales $v_r\asymp r^{d_f}$ with $d_f&gt;0$ and nonnegative cluster counts $N_r$ with $\mathbb EN_r\asymp r^\kappa$. Assume</p>
<div class="math-display">$$\mathbb E\sum_i S_{r,i}^2\asymp v_r^2\mathbb EN_r,\qquad \mathbb EX_r\asymp r^\alpha.$$</div>
<p>Suppose also that a nonnegative integer-valued random variable $Z$ has $\mathbb P(Z\geq n)\asymp n^{-1/\delta}$ for a finite $\delta&gt;0$, and that the additional matching relation</p>
<div class="math-display">$$\mathbb P(Z\geq\lceil v_r\rceil)\asymp\frac{v_r\mathbb EN_r}{|\Lambda_r|}$$</div>
<p>holds. Then</p>
<div class="math-display">$$\alpha=2d_f+\kappa-d,\qquad \frac{d_f}{\delta}=d-d_f-\kappa&gt;0.$$</div>
<p>In particular, if $\kappa=0$, then</p>
<div class="math-display">$$d_f=\frac{d\delta}{\delta+1},\qquad \alpha=d\frac{\delta-1}{\delta+1}.$$</div>
<p><em>Proof.</em> The counting identity gives $\mathbb EX_r\asymp r^{2d_f+\kappa-d}$. Two positive power functions can be comparable at infinity only if their exponents agree. Since $v_r\to\infty$, rounding it up does not change its order. The tail assumption and matching relation give $r^{-d_f/\delta}\asymp r^{d_f+\kappa-d}$, proving the second equality and its strict positivity. Set $\kappa=0$ and solve the two equations for the last display.</p>
<p>The hyperscaling heuristic motivates these hypotheses by a picture of $N_r$ large clusters of volume $v_r$. The counting identity alone controls only their contribution. It neither bounds the contribution of other sizes nor relates a finite-window intersection to the tail of the full cluster at a fixed root. These are precisely the two matching assumptions above. Tightness of $N_r$ alone also need not bound its expectation; rare configurations can dominate that expectation.</p>
<p>If an independent two-point estimate supplies $\alpha=2-\eta$, the case $\kappa=0$ becomes $2-\eta=d(\delta-1)/(\delta+1)$. Substituting the mean-field values $\delta=2$ and $\eta=0$ forces $d=6$. This is a consistency calculation under the stated matching hypotheses, not a proof of an upper critical dimension. With $d_f=4$ and $\kappa=d-6$, the general relations instead give $\alpha=2$ and $\delta=2$ for every $d$; proving that cluster picture requires separate geometry. A one-arm coalescence argument likewise needs an additional spatial merging estimate and is not a consequence of the counting identity.</p>

## From a spatial arm bound to a volume tail {#section-radius-volume}

<a id="tag-HPE6" data-assertion="proposition" data-title="Volume-tail bound from escape probabilities and window means"></a>
<p>Let $K$ be a random subset of a countable vertex set, and let $(\Lambda_r)_{r\geq1}$ be deterministic finite sets indexed by positive integers. Suppose that, for constants $a&gt;0$, $b\geq0$ and $C_1,C_2&lt;\infty$,</p>
<div class="math-display">$$\mathbb P(K\not\subseteq\Lambda_r)\leq C_1r^{-a},\qquad \mathbb E|K\cap\Lambda_r|\leq C_2r^b\qquad(r\geq1).$$</div>
<p>Then $K$ is finite almost surely and, for every integer $n\geq1$,</p>
<div class="math-display">$$\mathbb P(|K|\geq n)\leq(2^aC_1+C_2)n^{-a/(a+b)}.$$</div>
<p>If, in addition, this tail has a finite positive logarithmic exponent $1/\delta$, then $\delta\leq(a+b)/a$.</p>
<p><em>Proof.</em> On $\{K\subseteq\Lambda_r\}$, the size of $K$ equals its window intersection. The union bound and Markov's inequality therefore give</p>
<div class="math-display">$$\mathbb P(|K|\geq n)\leq\mathbb P(K\not\subseteq\Lambda_r)+\frac{\mathbb E|K\cap\Lambda_r|}{n}\leq C_1r^{-a}+C_2r^b/n.$$</div>
<p>Take $r=\lfloor n^{1/(a+b)}\rfloor$. For $x\geq1$ one has $x/2\leq\lfloor x\rfloor\leq x$, so each term has the asserted order with the displayed constant. Letting $n\to\infty$ proves almost-sure finiteness. Finally, take logarithms of the upper bound and divide by $\log n$; the assumed tail limit gives $1/\delta\geq a/(a+b)$. No independence, translation invariance or nesting of the windows is needed for this argument.</p>

<a id="tag-0RX3" data-assertion="corollary" data-title="A conditional planar volume-tail exponent inequality"></a>
<p>Let $K_0$ be the root cluster of any random nearest-neighbour bond subgraph of $\mathbb Z^2$. Put $\Lambda_r=[-r,r]^2\cap\mathbb Z^2$ and $\partial\Lambda_r=\{x:\|x\|_\infty=r\}$. Suppose $0&lt;\eta&lt;2$ and, for finite constants $C_1,C_2$,</p>
<div class="math-display">$$\mathbb P(0\leftrightarrow\partial\Lambda_r)\leq C_1r^{-\eta/2},\qquad \mathbb P(0\leftrightarrow x)\leq C_2(1+\|x\|_\infty)^{-\eta}$$</div>
<p>for every integer $r\geq1$ and every $x\in\mathbb Z^2$. Then</p>
<div class="math-display">$$\mathbb P(|K_0|\geq n)\leq C n^{-\eta/(4-\eta)}\qquad(n\geq1)$$</div>
<p>for a finite $C$. If the positive finite volume-tail exponent $\delta$ exists, then $\delta\leq(4-\eta)/\eta$.</p>
<p><em>Proof.</em> A nearest-neighbour path from $0$ to outside $\Lambda_r$ visits $\partial\Lambda_r$, giving the escape bound. There are $8k$ vertices on the square shell of radius $k\geq1$, so summing the two-point estimate yields</p>
<div class="math-display">$$\mathbb E|K_0\cap\Lambda_r|\leq C_2\left(1+8\sum_{k=1}^r k(1+k)^{-\eta}\right)\leq C_3r^{2-\eta}.$$</div>
<p>The last comparison follows by summing the power $k^{1-\eta}$, whose exponent is greater than $-1$. Apply the preceding proposition with $a=\eta/2$ and $b=2-\eta$. Its optimizing radius has order $n^{2/(4-\eta)}$.</p>
<p>This proves the upper-tail step of planar hyperscaling, conditional on the two displayed spatial estimates. It proves neither RSW nor the arm-to-two-point comparison, and it does not give the reverse exponent inequality. At $\eta=2$ the shell sum is logarithmic, so the stated power estimate cannot simply be extended to that endpoint. For long-range bonds, use escape from the box directly: a bond may jump across its vertex boundary without visiting it.</p>

## Logarithmic corrections in the source argument {#section-log-source}

<p>The source proves the implications and failed converses in <a href="/tag/UBFE/">UBFE</a> for real functions at infinity. Its first observation works along any filter: if eventually positive $f$ and $g$ are comparable, then $\log f-\log g$ is bounded. Indeed, $cg\leq f\leq Cg$ gives $\log c\leq\log f-\log g\leq\log C$. With $g(x)=x^\alpha$, division by $\log x\to\infty$ gives the exponent. More generally, the same conclusion follows whenever $\log f(x)-\alpha\log x=o(\log x)$.</p>
<p>For $f(x)=x^\alpha(\log x)^b(\log\log x)^c$, take $x$ large enough that all bases are positive. The logarithmic correction is $b\log\log x+c\log\log\log x=o(\log x)$, for every real $\alpha,b,c$. To see exactly when comparison with $x^\alpha$ is possible, put $L=\log\log x$. Such comparison would make $bL+c\log L$ bounded. Dividing by $L\to\infty$ forces $b=0$; the remaining boundedness then forces $c=0$. Thus a logarithmic exponent permits corrections of either sign, but a two-sided power comparison excludes all nonzero corrections in this family.</p>
<p>The source uses $(2+\sin x)x^\alpha$ for the other failed converse; the earlier example uses $\sin\log x$ instead. The source ratio lies between one and three, so it is comparable to $x^\alpha$. Equivalence to $c x^\alpha$ would force $\sin x\to c-2$, contradicted by the sequences $2\pi n$ and $\pi/2+2\pi n$. No amplitude exists despite the two-sided comparison.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-analytic/">sixteen-contract inventory</a> includes the small-order logarithmic estimates and these counterexamples. The formal limit lemmas use a total real logarithm; the positive-function hypotheses are what give them their intended asymptotic interpretation. This file proves no model's exponent, no hyperscaling relation and no parameter-zero limit.</p>


## Finite windows without spatial structure {#section-window-tail-source}

<p>The new source for <a href="/tag/HPE6/">HPE6</a> separates almost-sure finiteness from the optimized volume-tail estimate. Finiteness already follows from escape alone: an infinite set cannot be contained in any finite $\Lambda_r$, so</p>
<div class="math-display">$$\mu(K\text{ infinite})\leq\mu(K\not\subseteq\Lambda_r)\leq C_1r^{-a}\longrightarrow0.$$</div>
<p>No nesting or exhaustion property of the windows is used. With measurable membership events, the finite-window volume is a finite sum of indicators. Markov's inequality therefore gives the same escape-plus-window-mean bound for any measure, even on an uncountable ambient vertex set; events without established measurability are interpreted through outer measure. The article's countable probability setting is a specialization.</p>
<p>The source logarithmic consequence assumes a probability measure and the limit $\log\mathbb P(|K|\geq n)/\log n\to-1/\delta$ with $\delta&gt;0$. In its total real-logarithm convention, $\log0=0$. A negative limiting ratio forces positive tail values eventually, which justifies taking the logarithm of the upper bound there. The ordinary mathematical formulation likewise presupposes that this logarithmic tail is defined eventually. The source proves the conditional bound on $\delta$, not existence of that exponent or either spatial hypothesis in the planar application. All eight contracts are recorded in the <a href="/coverage/sources/perclib-3978a2f-tails/">moment and tail inventory</a>.</p>


## Moment orders and rounding in the source {#section-matching-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-windows/">window inventory</a> records the general partition identity behind <a href="/tag/OB0A/">OB0A</a>. Its explicit averaged-moment exports use natural orders. For the real orders in the article, apply the general identity with $f(s)=s^m$ and then take expectations; all window sizes are bounded and nonzero traces have positive size. The empty-window algebraic convention in the source does not define a uniformly sampled root.</p>
<p>For <a href="/tag/DEZI/">DEZI</a>, the assumption $d_f&gt;0$ and the positive lower comparison imply $v_r\to\infty$. Eventually $v_r\leq\lceil v_r\rceil\leq2v_r$, so replacing $v_r$ by its ceiling changes its logarithm by at most $\log2$. The two comparisons for the matched tail therefore have logarithms $-(d_f/\delta)\log r+O(1)$ and $(d_f+\kappa-d)\log r+O(1)$. Their difference is bounded only when the exponents agree. The positive lower constants are essential to this argument; an upper bound alone would yield only an inequality.</p>



## The square-lattice crossing input {#section-planar-crossings}

<a id="tag-WD31" data-assertion="theorem" data-title="Critical square-lattice bonds have uniform fixed-aspect-ratio crossings"></a>
<p>For nearest-neighbour bond percolation on $\mathbb Z^2$, $p_c=1/2$. At $p=1/2$, for each integer $k\geq2$ there is $c_k&gt;0$ such that every integer $n\geq1$ satisfies</p>
<div class="math-display">$$\mathbb P_{1/2}\bigl([0,2kn]\times[0,2n]\text{ has an open left-to-right crossing}\bigr)\geq c_k.$$</div>
<p>Crossings use edges inside the rectangle. Translations and quarter-turns give the corresponding statements in other positions and orientations. This is the RSW input in <a href="https://arxiv.org/pdf/math/0410359v3#page=8">Bollobás–Riordan, Corollary 7</a>; their Theorems 8 and 10 give the critical value. These are cited results. The arguments below prove their arm and two-point consequences, without reproducing the RSW or threshold proofs.</p>

## Extending an arm and blocking it {#section-planar-arm-bounds}

<a id="tag-XB1U" data-assertion="theorem" data-title="Critical square-lattice one-arm probabilities have uniform polynomial scale bounds"></a>
<p>Write $B_r(x)=x+[-r,r]^2\cap\mathbb Z^2$, $B_r=B_r(0)$, and</p>
<div class="math-display">$$A(r)=\mathbb P_{1/2}(0\leftrightarrow\partial B_r),\qquad r\in\mathbb N,\quad r\geq1.$$</div>
<p>The arm can be stopped on first reaching the boundary, so this is an event on the edges inside $B_r$. There are constants $c,C,a,b&gt;0$ such that, for all integers $1\leq r\leq R$,</p>
<div class="math-display">$$A(2r)\geq cA(r),\qquad
c(R/r)^{-b}A(r)\leq A(R)\leq C(R/r)^{-a}A(r).$$</div>
<p>In particular, $A(r)$ lies between two positive polynomial bounds and tends to zero. Thus there is almost surely no infinite open cluster at $p_c$.</p>
<p><em>Proof.</em> First build a circuit. Require horizontal crossings of $[-4n,4n]\times[2n,4n]$ and $[-4n,4n]\times[-4n,-2n]$, and vertical crossings of the two remaining strips $[2n,4n]\times[-4n,4n]$ and $[-4n,-2n]\times[-4n,4n]$. Adjacent crossings intersect: their portions in the common corner square cross it in perpendicular directions. Following the four crossings around the square gives a closed walk surrounding $B_n$; deleting loops that do not surround $B_n$ leaves a simple circuit. All its vertices lie in $B_{4n}\setminus B_{2n-1}$. The crossing input and <a href="/tag/X5SS/">Harris association</a> therefore give a constant $c_0\in(0,1)$, independent of $n$, for the event $C_n$ that such an open circuit exists.</p>
<p>For $r\geq8$, take $n=\lfloor r/8\rfloor$. In addition to $0\leftrightarrow\partial B_r$ and $C_n$, require a horizontal crossing of $[0,30n]\times[-n,n]$. Its probability is at least $c_{15}$. The original arm exits $B_{4n}$ and hence meets the circuit. The horizontal crossing starts inside the circuit, also meets it, and reaches the line $x=2r$, since $r\leq15n$. Consequently these three increasing events imply $0\leftrightarrow\partial B_{2r}$. Harris yields $A(2r)\geq c_0c_{15}A(r)$. All finitely many ratios $A(2r)/A(r)$ with $1\leq r&lt;8$ are positive; reduce the constant to obtain $c\in(0,1)$ valid for every $r$.</p>
<p>Iterate this inequality $k=\lceil\log_2(R/r)\rceil$ times. Since $A$ is decreasing, $A(R)\geq A(2^kr)\geq c^kA(r)\geq c(R/r)^{-b}A(r)$, where $b=-\log c/\log2$.</p>
<p>For the upper bound, regard each closed primal edge as an open edge of the dual lattice $\mathbb Z^2+(1/2,1/2)$. These dual edges are again independent with probability $1/2$. The same four-strip construction centred at $(1/2,1/2)$ gives a closed-dual circuit surrounding zero with probability at least $c_0$. Its edge coordinates, viewed as crossed primal bonds, lie between radii $2n-1$ and $4n+1$ in the maximum norm. Such a circuit blocks every primal arm from zero to $\partial B_{8n}$.</p>
<p>If $R\geq16r$, use scales $n_j=2r\,8^j$ for $0\leq j&lt;N$, where $N=1+\lfloor\log_8(R/(16r))\rfloor$. Their edge sets are disjoint from one another and from all edges inside $B_r$. Each circuit lies strictly inside $B_R$ and surrounds zero. Therefore independence gives</p>
<div class="math-display">$$A(R)\leq A(r)(1-c_0)^N
\leq16^a(r/R)^aA(r),\qquad a=-\frac{\log(1-c_0)}{\log8}&gt;0.$$</div>
<p>For $r\leq R&lt;16r$, the same bound follows from $A(R)\leq A(r)$. Taking $r=1$ proves the polynomial bounds and $A(R)\to0$. An infinite root cluster would reach every box boundary. Its probability is therefore zero; a countable union over roots excludes every infinite cluster.</p>
<p>The open-arm extension uses positive association even though its events overlap. Independence enters only in the separated closed-dual annuli. In particular, an arbitrary arm endpoint is never assumed to connect to a prescribed crossing with a uniform conditional probability.</p>

## One arm at each endpoint {#section-planar-two-point}

<a id="tag-Y8K3" data-assertion="theorem" data-title="The critical planar two-point function is comparable to the square of the one-arm probability"></a>
<p>For critical nearest-neighbour bond percolation on $\mathbb Z^2$, there are constants $0&lt;c_*\leq C_*&lt;\infty$ such that every $x\ne0$, with $r=\|x\|_\infty$, satisfies</p>
<div class="math-display">$$c_*A(r)^2\leq\tau_{p_c}(0,x)\leq C_*A(r)^2.$$</div>
<p>Consequently the logarithmic one-arm exponent exists if and only if the logarithmic two-point exponent exists as a limit over all vertices tending to infinity. In the conventions <a href="/tag/BLNL/">BLNL</a>, they then satisfy $\eta=2/\rho$. More strongly, for each $s&gt;0$, $A(r)\asymp r^{-s}$ is equivalent to $\tau_{p_c}(0,x)\asymp\|x\|^{-2s}$, uniformly in $x\ne0$.</p>
<p><em>Proof.</em> For $r\geq3$, set $m=\lfloor r/3\rfloor$. A connection from zero to $x$ forces an arm inside each of $B_m(0)$ and $B_m(x)$. The boxes are vertex-disjoint because $2m&lt;r$. Their arm events use disjoint edges, so</p>
<div class="math-display">$$\tau_{p_c}(0,x)\leq A(m)^2\leq c^{-6}A(r)^2.$$</div>
<p>For the second inequality, $r\leq5m&lt;8m$ and three applications of XB1U give $A(r)\geq A(8m)\geq c^3A(m)$. Enlarge the constant for $r=1,2$, using $\tau\leq1$ and $A(2)&gt;0$.</p>
<p>For the lower bound, require an arm to distance $8r$ from each endpoint and the circuit $C_r$ constructed in XB1U. The circuit surrounds both zero and $x$ and lies inside $B_{4r}(0)$. The first arm leaves this box. If $v$ is the endpoint of the arm from $x$, then $\|v\|_\infty\geq8r-\|x\|_\infty=7r$, so the second arm leaves it as well. Both arms therefore meet the same open circuit. They are connected, and Harris gives</p>
<div class="math-display">$$\tau_{p_c}(0,x)\geq c_0A(8r)^2\geq c_0c^6A(r)^2.$$</div>
<p>All intersections here are intersections of nearest-neighbour paths in the planar square lattice and hence share lattice vertices. No disjointness of the two long arms is required.</p>
<p>The comparison gives $\log\tau_{p_c}(0,x)=2\log A(\|x\|_\infty)+O(1)$, with a uniform error. A one-arm logarithmic limit therefore gives the two-point limit in every direction simultaneously. Conversely, a two-point limit along all vertices applies to $x=re_1$ and gives the one-arm limit. The polynomial bounds in XB1U make either limit, if it exists, positive and finite. Norm equivalence does not change the limit. The stronger power comparisons follow directly from the same two-sided estimate.</p>
<p>This proves the planar arm comparison and exponent identity under RSW. It supplies the missing arm hypothesis for the conditional planar volume-tail bound <a href="/tag/0RX3/">0RX3</a> when its two-sided spatial power law and exponent range hold. It does not establish a numerical exponent for square-lattice bonds, nor transfer the triangular-site SLE exponent values to this model. Crossed long-range bonds need not share vertices, so the gluing argument is specific to the planar nearest-neighbour embedding.</p>


## Three points at two scales {#section-planar-three-point-scales}

<a id="tag-K8A1" data-assertion="theorem" data-title="Critical square-lattice three-point probabilities have a uniform two-scale comparison"></a>
<p>In critical nearest-neighbour bond percolation on $\mathbb Z^2$, let $a,b,c$ be distinct. Relabel them so that $s=\|a-b\|_\infty$ is the smallest pair distance and $R=\|a-c\|_\infty$ is the largest. There are absolute constants $c_3,C_3&gt;0$ such that</p>
<div class="math-display">$$c_3A(s)A(R)^2\leq t(a,b,c)\leq C_3A(s)A(R)^2,
\qquad t(a,b,c)=\mathbb P(a,b,c\text{ lie in one open cluster}).$$</div>
<p>In particular the normalized ratio satisfies, uniformly over all such triples,</p>
<div class="math-display">$$0&lt;c_4\leq\frac{t(a,b,c)}{\sqrt{\tau(a,b)\tau(a,c)\tau(b,c)}}\leq2\sqrt2.$$</div>
<p><em>Proof.</em> Use the constants $c,c_0$ and circuits from XB1U, with $c,c_0\in(0,1)$. Require arms of lengths $8R,8s,8R$ from $a,b,c$, respectively, and open circuits surrounding $B_{2s-1}(a)$ and $B_{2R-1}(a)$, contained respectively in $B_{4s}(a)$ and $B_{4R}(a)$. The first circuit meets both the arm from $a$ and the arm from $b$: both marks are inside it, and the latter arm reaches a vertex at distance at least $7s$ from $a$. The second circuit similarly meets the arms from $a$ and $c$. Thus all three marks are connected. Harris association, followed by three doublings at each arm scale, gives</p>
<div class="math-display">$$t(a,b,c)\geq c_0^2 A(8s)A(8R)^2\geq c_0^2c^9 A(s)A(R)^2.$$</div>
<p>This argument also covers $s=R$: the two circuit requirements may coincide, and Harris still gives the displayed lower bound. No independence of overlapping arms or circuits is asserted.</p>
<p>Put $r=\|b-c\|_\infty$. The triangle inequality gives $R\leq s+r\leq2r$, so $A(R)\leq A(r)\leq c^{-1}A(R)$. The two-point comparison Y8K3 therefore bounds $\sqrt{\tau(a,b)\tau(a,c)\tau(b,c)}$ above and below by fixed positive multiples of $A(s)A(R)^2$. The lower ratio bound follows. For the upper bound apply the <a href="/tag/87RB/">countable three-point product theorem</a>, $t^2\leq8\tau(a,b)\tau(a,c)\tau(b,c)$. This also gives the remaining upper two-scale estimate.</p>
<p>The circuit input is RSW; the numerical upper constant comes from the decision-tree theorem, which needs no planar hypothesis. This proves boundedness without assuming a power law or conformal invariance. It supplies a precise form of the comparison discussed in <a href="https://arxiv.org/html/2408.08457v1#S6.SS3">Gladkov, section 6.3</a>.</p>

<a id="tag-UQ4B" data-assertion="corollary" data-title="The three-point logarithmic exponent retains the smallest pair scale"></a>
<p>Suppose in this model that $A(r)=r^{-\alpha+o(1)}$ as $r\to\infty$. For a sequence of distinct triples with largest distance $R_n\to\infty$ and smallest distance $s_n$, suppose $\log s_n/\log R_n\to\lambda\in[0,1]$. Then</p>
<div class="math-display">$$t(a_n,b_n,c_n)=R_n^{-\alpha(2+\lambda)+o(1)}.$$</div>
<p><em>Proof.</em> K8A1 gives $\log t=\log A(s_n)+2\log A(R_n)+O(1)$. For each $\varepsilon&gt;0$, the assumed arm limit gives $|\log A(s)+\alpha\log s|\leq\varepsilon\log s+C_\varepsilon$ for every integer $s\geq1$, after increasing $C_\varepsilon$ to handle finitely many small values. Divide by $\log R_n$, use $1\leq s_n\leq R_n$, and let $\varepsilon\downarrow0$.</p>
<p>Comparable pair distances give $\lambda=1$ and exponent $3\alpha$. A pair kept at bounded distance gives $\lambda=0$ and exponent $2\alpha$. Thus even when the one-arm exponent exists, a diameter alone does not specify the three-point exponent. This statement proves no numerical value of $\alpha$ for square-lattice bonds.</p>


## Pointwise and Fourier forms of the averaged exponent {#section-two-point-averaging-update}

<p>The <a href="/articles/two-point-averages/">two-point averaging article</a> supplies the implications behind the different conventions for $\eta$. J9YA sums a spatial power law and retains its precise strength: comparison, logarithmic exponent, or an exact equivalent with a cube integral. Under an integrable positive spectral-density representation, 44EA obtains the averaged exponent from a Fourier singularity by Gaussian smoothing and a tail estimate. Both use $0<2-\eta<d$; neither supplies the pointwise or Fourier premise for a particular percolation model.</p>
