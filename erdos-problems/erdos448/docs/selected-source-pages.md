# Erdős Problem 448 - Required Paper Pages

Faithful Markdown transcription of the selected source pages:

- P. Erdős and G. Tenenbaum, *Sur la structure de la suite des diviseurs d'un entier*, pp. 18-19 and 22-32.
- H. Halberstam and H.-E. Richert, *On a Result of R. R. Hall*, pp. 77-82.

Mathematical expressions have been reconstructed in LaTeX. Printed page numbers are retained as section markers.

---

# P. Erdős and G. Tenenbaum

## *Sur la structure de la suite des diviseurs d'un entier*

## Page 18

**C2.** *Pour tout réel positif $\varepsilon$ et presque tout entier $n$, on a :*

$$
1+(\log n)^{1-\log 3-\varepsilon}
< \min\left\{\frac{d'}{d}: d\mid n,\ d'\mid n,\ d<d'\right\}
<1+(\log n)^{1-\log 3+\varepsilon}.
$$

Malheureusement, alors que l'inégalité de gauche a été récemment prouvée, sous une forme légèrement plus précise, par Erdős et Hall [6], celle de droite doit pour le moment rester conjecturale.

Fondée sur le même argument heuristique, une autre conjecture est énoncée par Hall et Tenenbaum dans [9] :

**C3.** *Pour tout réel $\alpha$ de $[0,1]$ et presque tout entier $n$, on a :*

$$
U(n,\alpha):=\operatorname{card}\left\{d\mid n,\ d'\mid n:(d,d')=1,
\ \left|\log\frac{d'}d\right|\leqslant(\log n)^\alpha\right\}
=(\log n)^{\log 3-1+\alpha+o(1)}.
$$

Dans leur article les auteurs prouvent que l'inégalité

$$
U(n,\alpha)\leqslant(\log n)^{\log 3-1+\alpha+o(1)}
$$

a effectivement lieu pour presque tout $n$, mais ils n'obtiennent pas la borne inférieure souhaitée.

Désignons par $\tau(n)$ le nombre des diviseurs d'un entier $n$ ; dans le but de prouver C1, Erdős a introduit la fonction arithmétique $n\longmapsto\tau^+(n)$ égale au nombre des entiers $k$ pour lesquels l'intervalle $[2^k,2^{k+1}[$ contient au moins un diviseur de $n$. On a toujours $\tau^+(n)\leqslant\tau(n)$ et il suffirait, pour prouver C1, d'établir, pour presque tout $n$, l'inégalité stricte.

Cela a conduit Erdős (voir par exemple [4]) à émettre la conjecture suivante :

**C4.** *Quitte à négliger une suite d'entiers de densité nulle, le rapport $\tau^+(n)/\tau(n)$ tend vers $0$ lorsque $n$ tend vers l'infini.*

L'un des objets de cet article est de réfuter C4, prouvant même que toute suite $\mathcal A$ telle que

$$
\lim_{n\in\mathcal A}\frac{\tau^+(n)}{\tau(n)}=0
$$

est de densité nulle.

Plus précisément, nous obtenons le résultat quantitatif suivant :

## Page 19

**THÉORÈME 1.** - *Pour tout réel positif $\varepsilon$ il existe une constante positive $c(\varepsilon)$ telle que, pour tout réel $\alpha$, $0\leqslant\alpha\leqslant1$, la densité supérieure de la suite des entiers $n$ satisfaisant à $\tau^+(n)\leqslant\alpha\tau(n)$ ne dépasse pas $c(\varepsilon)\alpha^{1-\varepsilon}$.*

**Remarque.** - Ce résultat laisse augurer que la fonction arithmétique $\tau^+/\tau$ possède une fonction de répartition continue et croissante sur $[0,1]$.

Le reste de cette introduction est consacré plus spécifiquement aux propriétés de l'ensemble ordonné des diviseurs d'un entier ; nous notons

$$
1=d_1<d_2<\cdots<d_\tau=n
$$

la suite croissante des diviseurs d'un entier générique $n$.

Les conjectures C1 et C2 peuvent être traduites par des évaluations de la quantité

$$
\min\left\{\frac{d_{i+1}}{d_i}:1\leqslant i\leqslant\tau-1\right\}.
$$

Dans [10], Tenenbaum a établi que la fonction

$$
\psi(n):=(\log n)^{-1}\max\left\{\log\frac{d_{i+1}}{d_i}:1\leqslant i\leqslant\tau-1\right\}
$$

possède une fonction de répartition continue sur $[0,1]$ et « voisine » de l'identité. À une légère modification près, la démonstration du lemme 7 de [10] implique le résultat suivant :

*Soit $n$ un entier dont la décomposition en produit de facteurs premiers est $n=\prod_{i=1}^k p_i^{\nu_i}$, avec $p_1<p_2<\cdots<p_k$ ; alors on a*

$$
\max_{i=1}^{\tau-1}\frac{d_{i+1}}{d_i}
=\max_{j=1}^k p_j\Big/\prod_{i=1}^{j-1}p_i^{\nu_i}.
$$

Erdős et Hall se sont intéressés à la fonction

$$
f(n):=\operatorname{card}\{i\ (1\leqslant i\leqslant\tau-1):(d_i,d_{i+1})=1\},
$$

fournissant en particulier une minoration non triviale de son ordre maximal [5]. Cependant, aucun résultat satisfaisant n'a pu être obtenu pour l'ordre moyen de $f(n)$.

Parallèlement à l'étude de $f(n)$, on peut considérer la fonction

$$
g(n):=\operatorname{card}\{i\ (1\leqslant i\leqslant\tau-1):d_i\mid d_{i+1}\}.
$$

Nous montrons le résultat suivant :

## Page 22

Les lettres $c,c_1,c_2$ désignent des constantes absolues positives. Dans l'utilisation des symboles $\ll$ de Vinogradov, toute dépendance éventuelle en fonction des paramètres $\sigma,\theta,\ldots$ sera indiquée sous la forme $\ll_{\sigma,\theta,\ldots}$.

Nous notons $\tau(n)$ le nombre des diviseurs d'un entier $n$ et $\Omega(n)$ (resp. $\omega(n)$) le nombre de ses facteurs premiers, comptés avec (resp. sans) leur ordre de multiplicité.

Le plus grand (resp. le plus petit) facteur premier d'un entier $n>1$ est noté $P^+(n)$ (resp. $P^-(n)$). Par convention $P^+(1)=1$, $P^-(1)=+\infty$. Pour chaque valeur du paramètre réel $\sigma\geqslant2$, on note $n\longmapsto\chi(n,\sigma)$ la fonction caractéristique de l'ensemble des entiers $n\geqslant1$ satisfaisant à $P^-(n)\geqslant\sigma$ et l'on pose :

$$
\tau(n,\sigma):=\sum_{d\mid n}\chi(d,\sigma),
$$

$$
\Omega(n,\sigma):=\sum_{p^\nu\parallel n,\,p<\sigma}\nu,
$$

$$
\omega(n,\sigma):=\sum_{p^\nu\parallel n,\,p<\sigma}1.
$$

Pour tout réel $\theta>1$, nous définissons une fonction arithmétique $\tau^+(n,\theta)$ par la formule

$$
\tau^+(n,\theta):=\operatorname{card}\{k\in\mathbb N:\exists d\mid n:\theta^k\leqslant d<\theta^{k+1}\};
$$

dans le cas $\theta=2$, nous notons simplement $\tau^+(n,2)=\tau^+(n)$.

Le symbole $\sum_{d,d'}^\theta$ indique une sommation restreinte aux couples d'entiers $(d,d')$ satisfaisant à $d\ne d'$ et

$$
\frac1\theta<\frac{d'}d<\theta.
$$

Enfin, par convention, une somme (resp. un produit) portant sur l'ensemble vide est nulle (resp. égal à 1).

### 3. Résultats préliminaires

Nous ferons grand usage du résultat suivant, dû à Halberstam et Richert [7] et généralisant un résultat de Hall.

**LEMME 1.** - *Soit $h$ une fonction multiplicative réelle satisfaisant, pour tout $p$, à*

$$
0\leqslant h(p^j)\leqslant\lambda_1\lambda_2^j\qquad(j=0,1,2,\ldots),
$$

*où* 

## Page 23

*$\lambda_1\geqslant0$ et $0\leqslant\lambda_2<2$ ; on a pour $x\geqslant2$*

$$
\sum_{n<x}h(n)\ll\frac{x}{\log x}\prod_{p<x}\sum_{j=0}^\infty h(p^j)p^{-j}.
$$

Au cours de la démonstration des théorèmes 1 et 2, nous utiliserons la généralisation suivante du lemme 1 :

**LEMME 2.** - *Soient $u$ et $v$ deux fonctions arithmétiques multiplicatives réelles satisfaisant, pour tout $p$, à*

$$
0\leqslant u(p^{i+j})v(p^j)\leqslant\lambda_i\lambda^j
\qquad(i,j=0,1,2,\ldots),
$$

*où $\lambda_i\geqslant0$ $(i=0,1,2,\ldots)$ et $0\leqslant\lambda<2$.*

*Si l'on pose, pour tout $p$,*

$$
w(p^i)=
\frac{\displaystyle\sum_{j=0}^\infty u(p^{i+j})v(p^j)(1+j\log p)p^{-j}}
{\displaystyle\sum_{j=0}^\infty u(p^j)v(p^j)p^{-j}}
\qquad(i=1,2,\ldots),
$$

*alors on a uniformément en $k\geqslant1$ et $x\geqslant2$*

$$
\sum_{n<x}u(kn)v(n)
\ll
\prod_{\substack{p^i\parallel k\\p<x}}w(p^i)
\prod_{\substack{p^i\parallel k\\p\geqslant x}}u(p^i)
\frac{x}{\log x}
\prod_{p<x}\sum_{j=0}^\infty u(p^j)v(p^j)p^{-j}.
\tag{1}
$$

**Remarque.** - Sous certaines hypothèses supplémentaires (par exemple $u(n)>0$ pour tout $n$) on peut supprimer le facteur $(1+j\log p)$ dans la définition de $w(p^i)$, ce qui rend le résultat optimal - cf. par exemple [1] Théorème T. Dans le cas général, cependant, ce facteur supplémentaire est indispensable, comme le montre l'exemple suivant : $k$ est un nombre premier de l'intervalle $[x/2,x[$, $u(1)=u(k^2)=1$, $u(n)=0$ pour $n\ne1$ ou $k^2$, $v(n)=1$ pour tout $n$ ; l'inégalité (1) s'écrit alors :

$$
1\ll\frac{1+\log k}{k}\frac{x}{\log x}.
$$

*Démonstration du lemme 2.* - Le cas des facteurs premiers $\geqslant x$ de $k$ est trivial ; nous supposons donc $P^+(k)<x$.

On a :

$$
\sum_{n<x}u(kn)v(n)\log x
=\sum_{d\mid k^\infty}u(kd)v(d)
\sum_{\substack{m<x/d\\(m,k)=1}}u(m)v(m)
\left\{\log\frac{x}{d}+\log d\right\}.
$$

## Page 24

Dans un premier temps, le lemme 1 appliqué à

$$
n\longmapsto h(n)=
\begin{cases}
u(n)v(n),&\text{si }(n,k)=1,\\
0,&\text{sinon}
\end{cases}
$$

permet d'écrire

$$
\sum_{\substack{m<x/d\\(m,k)=1}}u(m)v(m)\log(x/d)
\ll\frac{x}{d}
\prod_{\substack{p<x\\p\nmid k}}
\sum_{j=0}^\infty u(p^j)v(p^j)p^{-j};
$$

ensuite on a la majoration triviale

$$
\begin{aligned}
\sum_{\substack{m<x/d\\(m,k)=1}}u(m)v(m)\log d
&\leqslant\frac{x}{d}\log d
\sum_{\substack{m<x\\(m,k)=1}}\frac{u(m)v(m)}m\\
&\leqslant\frac{x}{d}\log d
\prod_{\substack{p<x\\p\nmid k}}
\sum_{j=0}^\infty u(p^j)v(p^j)p^{-j}.
\end{aligned}
$$

On obtient donc

$$
\sum_{n<x}u(kn)v(n)
\ll\frac{x}{\log x}
\sum_{d\mid k^\infty}\frac{u(kd)v(d)}d(1+\log d)
\prod_{\substack{p<x\\p\nmid k}}
\sum_{j=0}^\infty u(p^j)v(p^j)p^{-j};
$$

le résultat s'en déduit en remarquant que, pour tout $d$,

$$
1+\log d\leqslant\prod_{p^j\parallel d}(1+j\log p).
$$

**LEMME 3.** - *Pour tout couple $(\beta,\sigma)$ des réels satisfaisant à $1<\beta<2$ et $\sigma\geqslant2$, notons $\delta(\beta,\sigma)$ la densité supérieure de la suite des entiers $n$ satisfaisant à*

$$
\tau(n,\sigma)\leqslant\tau(n)(\log\sigma)^{-\beta\log2}.
$$

*On a*

$$
\delta(\beta,\sigma)\ll_\beta(\log\sigma)^{\beta-1-\beta\log\beta}.
$$

*Démonstration.* - On a, pour tout $n$, $\tau(n,\sigma)\geqslant2^{-\Omega(n,\sigma)}\tau(n)$, d'où

$$
\delta(\beta,\sigma)
\leqslant\limsup_{x\to\infty}\frac1x
\operatorname{card}\{n<x:\Omega(n,\sigma)\geqslant\beta\log\log\sigma\}.
$$

D'après le lemme 1, on a pour $1<y<2$

$$
\sum_{n<x}y^{\Omega(n,\sigma)}\ll_y x(\log\sigma)^{y-1};
$$

cela implique

$$
\delta(\beta,\sigma)
\leqslant\limsup_{x\to\infty}\frac1x
\sum_{n<x}y^{\Omega(n,\sigma)-\beta\log\log\sigma}
\ll_y(\log\sigma)^{y-1-\beta\log y},
$$

d'où l'on tire le résultat annoncé en choisissant $y=\beta$.

## Page 25

**LEMME 4.** - *Il existe une fonction d'une variable $\varepsilon\longmapsto\xi_0(\varepsilon)$ telle que, pour tous réels $\varepsilon,\xi,\sigma,\theta$ satisfaisant à*

$$
0<\varepsilon\leqslant\frac15,
\qquad \xi\geqslant\xi_0(\varepsilon),
\qquad \sigma\geqslant\theta\geqslant2,
$$

*il existe une suite d'entiers $\mathcal A$ possédant les propriétés suivantes :*

1. *Pour tout $n$ de $\mathcal A$, $P^-(n)\geqslant\theta$.*
2. *La densité inférieure de $\mathcal A$ est au moins égale à*

$$
\left(1-(\log\xi)^{-(9/10)\varepsilon^2}\right)
\prod_{p<\theta}\left(1-\frac1p\right).
$$

3. *Pour tout $n$ de $\mathcal A$,*

$$
\sum_{d\mid n}\chi(d,\sigma)\chi^*(d)
\geqslant\frac9{10}\tau(n,\sigma),
$$

*où $\chi^*$ est la fonction caractéristique de l'ensemble des entiers $d$ satisfaisant à*

$$
\sup_{\exp\{\log\xi\cdot\log\sigma\}\leqslant u<n}
\frac{\left|\Omega(d,u)-\frac12\log(\log u/\log\sigma)\right|}
{\log(\log u/\log\sigma)}
\leqslant\varepsilon.
\tag{2}
$$

*Démonstration.* - Supposons $\sigma$ et $\theta$ donnés comme indiqué et définissons, pour tout $y$ de $]0,2[$ et tout $u>\sigma$, une fonction arithmétique par

$$
f(y,u,n)=\chi(n,\theta)\tau(n,\sigma)^{-1}
\sum_{d\mid n}y^{\Omega(d,u)}\chi(d,\sigma);
$$

c'est une fonction multiplicative ; on a pour $\nu\geqslant1$

$$
f(y,u,p^\nu)=
\begin{cases}
0,&p<\theta,\\
1,&\theta\leqslant p<\sigma,\\
(\nu+1)^{-1}\displaystyle\sum_{j=0}^\nu y^j,&\sigma\leqslant p<u,\\
1,&u\leqslant p.
\end{cases}
$$

En particulier, on a pour tout $\nu\geqslant1$

$$
0\leqslant f(y,u,p^\nu)\leqslant(\max\{1,y\})^\nu;
$$

on peut donc appliquer le lemme 1 ; on obtient pour $x$ infini

$$
\sum_{n<x}f(y,u,n)
\ll_y x\prod_{p<\theta}\left(1-\frac1p\right)
\left(\frac{\log u}{\log\sigma}\right)^{(y-1)/2},
\tag{3}
$$

la constante impliquée étant localement uniforme en $y$.

## Page 26

En remarquant que l'on a pour tout $n$

$$
\begin{aligned}
&\chi(n,\theta)\tau(n,\sigma)^{-1}
\sum\left\{\chi(d,\sigma):d\mid n,
\ \Omega(d,u)>\frac y2\log\frac{\log u}{\log\sigma}\right\}\\
&\qquad\leqslant f(y,u,n)
\left(\frac{\log u}{\log\sigma}\right)^{-\frac12y\log y},
\qquad 1<y<2,
\end{aligned}
$$

et

$$
\begin{aligned}
&\chi(n,\theta)\tau(n,\sigma)^{-1}
\sum\left\{\chi(d,\sigma):d\mid n,
\ \Omega(d,u)<\frac y2\log\frac{\log u}{\log\sigma}\right\}\\
&\qquad\leqslant f(y,u,n)
\left(\frac{\log u}{\log\sigma}\right)^{-\frac12y\log y},
\qquad 0<y<1,
\end{aligned}
$$

on obtient, grâce à (3), en choisissant successivement

$$
y=y_1=1+1{,}96\varepsilon
\quad\text{et}\quad
y=y_2=1-1{,}96\varepsilon,
\qquad \varepsilon\leqslant\frac15,
$$

$$
\begin{aligned}
&\sum_{n<x}\frac{\chi(n,\theta)}{\tau(n,\sigma)}
\sum\left\{\chi(d,\sigma):d\mid n,
\ \left|\Omega(d,u)-\frac12\log\frac{\log u}{\log\sigma}\right|
\geqslant0{,}98\varepsilon\log\frac{\log u}{\log\sigma}\right\}\\
&\qquad\ll x\prod_{p<\theta}\left(1-\frac1p\right)
\sum_{i=1}^2
\left(\frac{\log u}{\log\sigma}\right)^{\frac12(y_i-1-y_i\log y_i)}\\
&\qquad\ll x\prod_{p<\theta}\left(1-\frac1p\right)
\left(\frac{\log u}{\log\sigma}\right)^{-0{,}901\varepsilon^2}.
\end{aligned}
\tag{4}
$$

Posons :

$$
\Lambda(d,u)=
\frac{\displaystyle\Omega(d,u)-\frac12\log\frac{\log u}{\log\sigma}}
{\displaystyle\log\frac{\log u}{\log\sigma}}
$$

et

$$
u_k=\exp\{e^k\log\sigma\cdot\log\xi\}
\qquad(k=0,1,2,\ldots);
$$

d'après (4), on a :

$$
\begin{aligned}
&\sum_{n<x}\frac{\chi(n,\theta)}{\tau(n,\sigma)}
\sum\left\{\chi(d,\sigma):d\mid n,
\ \sup_{u_k<x}|\Lambda(d,u_k)|\geqslant0{,}98\varepsilon\right\}\\
&\qquad\leqslant cx\prod_{p<\theta}\left(1-\frac1p\right)
\sum_{k=0}^\infty(e^k\log\xi)^{-0{,}901\varepsilon^2}\\
&\qquad\leqslant\frac1{10}x\prod_{p<\theta}\left(1-\frac1p\right)
(\log\xi)^{-(9/10)\varepsilon^2},
\end{aligned}
$$

pour $\xi\geqslant\xi_1(\varepsilon)$.

## Page 27

Comme pour $u\in[u_k,u_{k+1}]$ on a :

$$
\left(1-\frac1{\log\log\xi}\right)
\left(\Lambda(d,u_k)-\frac1{\log\log\xi}\right)
\leqslant\Lambda(d,u)
$$

$$
\leqslant
\left(\Lambda(d,u_{k+1})+\frac1{\log\log\xi}\right)
\left(1+\frac1{\log\log\xi}\right),
$$

pour tout $d$ et tout $\xi\geqslant\xi_2$, on voit finalement que, pour

$$
\xi\geqslant\xi_0(\varepsilon)
:=\max\left\{\xi_1(\varepsilon),\xi_2,
\exp\exp\left(\frac1{0{,}01\varepsilon}\right)\right\},
$$

$$
\begin{aligned}
&\sum\left\{\chi(n,\theta):n<x,
\ \sum_{d\mid n}\chi(d,\sigma)\chi^*(d)
\leqslant\frac9{10}\tau(n,\sigma)\right\}\\
&\qquad\leqslant x\prod_{p<\theta}\left(1-\frac1p\right)
(\log\xi)^{-(9/10)\varepsilon^2},
\end{aligned}
$$

ce qui achève la démonstration du lemme 4.

**Remarques.** - (i) L'énoncé du lemme 4 reste évidemment valable si l'on y remplace $\Omega(d,u)$ par $\omega(d,u)$ et, quitte à restreindre $\varepsilon$, la constante $9/10$ par toute autre constante numérique $<1$.

(ii) Il est bien connu que, pour presque tout diviseur $d$ d'un entier usuel $n$, et $u$ assez grand, on a $\Omega(d,u)\sim\frac12\Omega(n,u)$ ; cela découle, par exemple, facilement de l'inégalité suivante, valable pour tout $n$, et établie par Hall dans [8],

$$
\sum_{d\mid n}\left|\omega(d)-\frac12\omega(n)\right|^2
\leqslant\frac14\tau(n)\left\{|\omega(n)-\Omega(n)|^2+\omega(n)\right\}.
$$

Notre lemme 4 exprime la même idée, de façon quantitative, et, en se restreignant aux diviseurs $d$ tels que $P^-(d)\geqslant\sigma$ des entiers $n$ tels que $P^-(n)\geqslant\theta$.

(iii) Si l'on désire obtenir un résultat valable pour presque tout $n$ et une estimation plus précise de la différence entre $\Omega(d,u)$ et son ordre normal lorsque $u\to\infty$ avec $n$, on peut appliquer, à quelques légères modifications près, la méthode employée au lemme 4 pour prouver le résultat suivant :

*Soit $\varepsilon$ un réel positif et $\xi=\xi(n)\to\infty$, alors on a pour presque tout entier $n$*

$$
\operatorname{card}\left\{d:d\mid n,
\ \sup_{\xi<u<n}
\frac{\left|\Omega(d,u)-\frac12\log\log u\right|}
{(\log\log u\cdot\log\log\log u)^{1/2}}
\geqslant1+\varepsilon\right\}
=o(\tau(n)).
$$

## Page 28

### 4. Preuve des théorèmes 1 et 2

**PROPOSITION 1.** - *Soit $(\varepsilon,\xi,\sigma,\theta)$ un système de nombres réels satisfaisant aux conditions du lemme 4 et $\mathcal A$ une suite d'entiers possédant les propriétés (i), (ii) et (iii) du lemme 4.*

*Alors on a, pour tout $n$ de $\mathcal A$,*

$$
\frac45\frac{\tau(n,\sigma)}{\tau^+(n,\theta)}
\leqslant1+\frac1{\tau(n,\sigma)}
\sum_{\substack{d,d'\mid n}}^\theta\chi(d,\sigma)\chi^*(d).
\tag{5}
$$

*Démonstration.* - Pour tout $n$ de $\mathcal A$, désignons par $k_1<\cdots<k_r$ la suite des entiers $k$ pour lesquels on a

$$
\nu(k):=\sum\{\chi(d,\sigma)\chi^*(d):d\mid n,\ \theta^k\leqslant d<\theta^{k+1}\}\geqslant1.
$$

Alors $r\leqslant\tau^+(n,\theta)$ et

$$
\sum_{d,d'\mid n}^\theta\chi(d,\sigma)\chi^*(d)
\geqslant\sum_{i=1}^r\nu(k_i)(\nu(k_i)-1)
\geqslant\sum_{i=1}^r\nu(k_i)^2-\tau(n,\sigma).
$$

D'après l'inégalité de Cauchy-Schwarz, on a donc

$$
\begin{aligned}
\left\{\sum_{d\mid n}\chi(d,\sigma)\chi^*(d)\right\}^2
&=\left\{\sum_{i=1}^r\nu(k_i)\right\}^2\\
&\leqslant r\sum_{i=1}^r\nu(k_i)^2\\
&\leqslant\tau^+(n,\theta)
\left\{\sum_{d,d'\mid n}^\theta\chi(d,\sigma)\chi^*(d)+\tau(n,\sigma)\right\}.
\end{aligned}
$$

La conclusion souhaitée découle de cette inégalité puisque, grâce au lemme 4, on peut minorer le membre de gauche par $\frac45\tau(n,\sigma)^2$.

**PROPOSITION 2.** - *Soit $(\varepsilon,\xi,\sigma,\theta)$ un système de nombres réels satisfaisant aux conditions du lemme 4, et supposons donné un réel $y$ de $]0,1[$. Si l'on pose pour tout $n$*

$$
f(n):=\frac{\chi(n,\theta)}{\tau(n)}
\sum_{d,d'\mid n}^\theta\chi(d,\sigma)\chi^*(d),
$$

*et*

$$
f_k(y,n):=\frac1{\tau(n)}
\sum_{\substack{d,d'\mid n\\\theta^k<d<\theta^{k+1}}}^\theta
\chi(d,\sigma)
\sum_{t\mid n/(dd')}y^{\Omega(dt,\theta^k)}\chi(t,\sigma)
\qquad(k=0,1,2,\ldots),
$$

*alors on a*

## Page 29

$$
f(n)\leqslant
\left(\frac{2\log\xi\cdot\log\theta}{\log\sigma}\right)^{-(\frac12+\varepsilon)\log y}
\sum_{k\geqslant\frac12\frac{\log\sigma}{\log\theta}}
k^{-(\frac12+\varepsilon)\log y}f_k(y,n).
\tag{6}
$$

*Démonstration.* - On a :

$$
f(n)=\frac{\chi(n,\theta)}{\tau(n)}
\sum_{k\geqslant[\log\sigma/\log\theta]}
\sum_{\substack{d,d'\mid n\\(d,d')=1,\,\theta^k\leqslant d<\theta^{k+1}}}^\theta
\sum_{t\mid n/(dd')}\chi(dt,\sigma)\chi^*(dt).
$$

Il suffit donc de montrer que

$$
\chi^*(m)\leqslant
\left(\frac{2k\log\xi\cdot\log\theta}{\log\sigma}\right)^{-(\frac12+\varepsilon)\log y}
y^{\Omega(m,\theta^k)}
\tag{7}
$$

pour tout $m\geqslant1$ et tout

$$
k\geqslant\left[\frac{\log\sigma}{\log\theta}\right]
\geqslant\frac12\frac{\log\sigma}{\log\theta}.
$$

D'une part, si

$$
k\geqslant\frac{\log\sigma}{\log\theta}\cdot\log\xi
$$

et $\chi^*(m)=1$ on a :

$$
\Omega(m,\theta^k)
\leqslant\left(\frac12+\varepsilon\right)
\log\left(\frac{k\log\theta}{\log\sigma}\right),
$$

donc

$$
y^{\Omega(m,\theta^k)}k^{-(\frac12+\varepsilon)\log y}
\geqslant
\left(\frac{\log\sigma}{\log\theta}\right)^{-(\frac12+\varepsilon)\log y}
$$

et (7) est bien vérifiée.

D'autre part si

$$
\frac12\frac{\log\sigma}{\log\theta}
\leqslant k<\frac{\log\sigma}{\log\theta}\cdot\log\xi,
$$

on a :

$$
\Omega(m,\theta^k)
\leqslant\Omega(m,\exp\{\log\xi\cdot\log\sigma\})
\leqslant\left(\frac12+\varepsilon\right)\log\log\xi,
$$

d'où l'on déduit encore que l'inégalité (7) est satisfaite.

**PROPOSITION 3.** - *Avec les hypothèses et notations de la proposition 2, on a uniformément pour $x>\theta^{2k-1}$ et $k\geqslant1$*

$$
\begin{aligned}
\sum_{n<x}f_k(y,n)
\ll_\theta{}&x(\log\sigma)^{-y}k^{(y-3)/2}\\
&\times\left\{
k^{(y-1)/2}
+(\log(2x\theta^{1-2k}))^{(y-1)/2}
+\frac{(\log\sigma)^{y/2}}{(\log(2x\theta^{1-2k}))^{1/2}}
\right\}.
\end{aligned}
$$

*Démonstration.* - Posons : $S_k(x,y)=\sum_{n<x}f_k(y,n)$. Après inversion de sommations on peut écrire

## Page 30

$$
S_k(x,y)=
\sum_{\substack{d,d'\\\theta^k<d<\theta^{k+1}}}^\theta
\sum_{t<x/(dd')}\chi(dt,\sigma)y^{\Omega(dt,\theta^k)}
\sum_{m<x/(tdd')}\tau(mtdd')^{-1}.
\tag{8}
$$

Nous dirons qu'une fonction multiplicative $w$ est « de type $\tau^{-1}$ » s'il existe un réel $\delta>0$ tel que

$$
w(p^\nu)=\frac1{\nu+1}+O(p^{-\delta})
$$

pour tout $\nu\geqslant1$.

Le lemme 2 permet de majorer la somme intérieure de (8) : on a

$$
\begin{aligned}
\sum_{m<x/(tdd')}\tau(mtdd')^{-1}
&\ll x\frac{w_1(tdd')}{tdd'}
\left(\log\frac{x}{tdd'}\right)^{-1/2}\\
&\ll w_1(tdd')\sum_{m<x/(tdd')}(\log m)^{-1/2},
\end{aligned}
$$

où $w_1$ est de type $\tau^{-1}$.

En reportant dans (8), on déduit

$$
\begin{aligned}
S_k(x,y)\ll
\sum_{\substack{d,d'\\\theta^k<d<\theta^{k+1}}}^\theta
&\chi(d,\sigma)y^{\Omega(d,\theta^k)}
\sum_{m<x/(dd')}(\log m)^{-1/2}\\
&\times\sum_{t<x/(mdd')}y^{\Omega(t,\theta^k)}\chi(t,\sigma)w_1(tdd').
\end{aligned}
$$

Le lemme 2 permet à nouveau d'estimer la somme intérieure, on a :

$$
\sum_{t<z}y^{\Omega(t,\theta^k)}\chi(t,\sigma)w_1(tdd')
\ll_\theta
\begin{cases}
zw_2(dd')(\log\sigma)^{-y/2}k^{(y-1)/2}(\log z)^{-1/2},&z\geqslant\theta^k,\\
zw_2(dd')(\log\sigma)^{-y/2}(\log z)^{y/2-1},&\sigma\leqslant z<\theta^k,\\
w_1(dd'),&z<\sigma,
\end{cases}
$$

où $w_2$ est de type $\tau^{-1}$.

Il existe donc une fonction $w_3$ de type $\tau^{-1}$ telle que

$$
\begin{aligned}
S_k(x,y)\ll_\theta(\log\sigma)^{-y/2}
\sum_{\substack{d,d'\\\theta^k<d<\theta^{k+1}}}^\theta
\chi(d,\sigma)y^{\Omega(d,\theta^k)}w_3(dd')
\{A_k(x)+B_k(x)+C_k(x)\}.
\end{aligned}
\tag{9}
$$

où l'on a posé

> (*) Ici et dans les calculs qui vont suivre, $(\log1)^{-1}$ est systématiquement interprété comme valant 1 dans une sommation.

## Page 31

$$
\begin{aligned}
A_k(x)
&=\frac{x}{\theta^{2k}}
\sum_{m<x\theta^{1-3k}}
(\log m)^{-1/2}k^{(y-1)/2}m^{-1}
\left(\log\frac{x\theta^{1-2k}}m\right)^{-1/2}\\
&\ll\frac{x}{\theta^{2k}}k^{(y-1)/2},
\end{aligned}
$$

$$
\begin{aligned}
B_k(x)
&=\frac{x}{\theta^{2k}}
\sum_{x\theta^{1-3k}<m<x\theta^{1-2k}}
(\log m)^{-1/2}m^{-1}
\left(\log\frac{x\theta^{1-2k}}m\right)^{y/2-1}\\
&\ll_\theta\frac{x}{\theta^{2k}}
(\log(2x\theta^{1-2k}))^{(y-1)/2},
\end{aligned}
$$

et

$$
C_k(x)=\frac{x}{\theta^{2k}}(\log\sigma)^{y/2}
(\log(2x\theta^{1-2k}))^{-1/2}.
$$

Enfin, d'après le lemme 2,

$$
\begin{aligned}
&\sum_{\substack{d,d'\\\theta^k<d<\theta^{k+1}}}^\theta
\chi(d,\sigma)y^{\Omega(d,\theta^k)}w_3(dd')\\
&\qquad\ll_\theta\theta^k
\sum_{\theta^{k-1}<d'<\theta^{k+2}}
w_4(d')(\log\sigma)^{-y/2}k^{y/2-1}\\
&\qquad\ll_\theta\theta^{2k}(\log\sigma)^{-y/2}k^{(y-3)/2},
\end{aligned}
$$

(où $w_4$ est de type $\tau^{-1}$).

En reportant dans (9) et en tenant compte des évaluations de $A_k(x)$, $B_k(x)$, $C_k(x)$, on obtient le résultat annoncé.

**PROPOSITION 4.** - *Soit $f$ la fonction arithmétique définie à la proposition 2. On a pour $0<y<1$ et*

$$
0<\varepsilon<-
\frac{1-y+\frac12\log y}{\log y}
$$

$$
\sum_{n<x}f(n)
\ll_{\theta,y,\varepsilon}
(\log\xi)^{-(\frac12+\varepsilon)\log y}(\log\sigma)^{-1}x+o(x).
\tag{10}
$$

*Démonstration.* - On a, d'après (6),

$$
\sum_{n<x}f(n)
\ll_{\theta,y}
\left(\frac{\log\xi}{\log\sigma}\right)^{-(\frac12+\varepsilon)\log y}
\sum_{\frac12\frac{\log\sigma}{\log\theta}<k<\frac12(1+\frac{\log x}{\log\theta})}
k^{-(\frac12+\varepsilon)\log y}
\sum_{n<x}f_k(y,n);
$$

utilisant la majoration de la proposition 3, il vient

## Page 32

$$
\begin{aligned}
\sum_{n<x}f(n)
\ll_{\theta,y}{}&(\log\xi)^{-(\frac12+\varepsilon)\log y}
(\log\sigma)^{-y+(\frac12+\varepsilon)\log y}\\
&\times\left\{
x\sum_{\frac12\frac{\log\sigma}{\log\theta}<k<\frac12(1+\frac{\log x}{\log\theta})}
k^{y-2-(\frac12+\varepsilon)\log y}+o(x)
\right\},
\end{aligned}
$$

la quantité $o(x)$ provenant de la sommation des termes en $\log(2x\theta^{1-2k})$, traitée par intégration par parties.

Pour

$$
\varepsilon<-
\frac{1-y+\frac12\log y}{\log y}
$$

la série en $k$ est convergente, d'où (10).

*Démonstration du théorème 1.* - Choisissons $\sigma=\theta=2$, $y$ dans $]0,1[$ et $\varepsilon$ dans

$$
\left]0,-\frac{1-y+\frac12\log y}{\log y}\right[;
$$

d'après la proposition 1, on a

$$
\frac{\tau(n)}{\tau^+(n)}\leqslant\frac54(1+f(n))
$$

sauf pour une suite de valeurs de $n$ de densité supérieure

$$
\leqslant(\log\xi)^{-(9/10)\varepsilon^2}.
$$

Comme (10) implique l'existence d'une constante $c_1(y,\varepsilon)$ telle que

$$
\sum_{n<x}f(n)
\leqslant c_1(y,\varepsilon)
(\log\xi)^{-(\frac12+\varepsilon)\log y}x+o(x),
$$

on en déduit que la densité de la suite des entiers $n$ pour lesquels

$$
\frac{\tau(n)}{\tau^+(n)}\geqslant\frac1\alpha
$$

ne dépasse pas

$$
c_2(y,\varepsilon)\alpha
(\log\xi)^{-(\frac12+\varepsilon)\log y}
+(\log\xi)^{-(9/10)\varepsilon^2}.
$$

Si $y>1/2$, on peut prendre $\varepsilon=1/5$ ; en choisissant alors, pour $y$ suffisamment voisin de 1, la valeur optimale de $\xi$, soit

$$
\xi=\exp\exp\left\{
\frac{-\log\alpha}{0{,}036-0{,}7\log y}
\right\},
$$

on obtient, comme majoration, une puissance arbitrairement proche de l'unité de $\alpha$.

*Démonstration du théorème 2.* - Choisissons $\xi=\exp\{(\log\sigma)^{1/2}\}$, $y=1/2$, et $\varepsilon=1/10$. D'après la proposition 4, on a

$$
\sum_{n<x}f(n)\ll_\theta(\log\sigma)^{0{,}3\log2-1}x+o(x).
\tag{11}
$$

Maintenant, rappelons que

---

# H. Halberstam and H.-E. Richert

## *On a Result of R. R. Hall*

## Page 77

As Hall pointed out, special interest attaches to the following case: let $K$ be a positive integer none of whose prime factors exceeds $x$, and take

$$
h_K(n):=
\begin{cases}
1,&(n,K)=1,\\
0,&(n,K)>1.
\end{cases}
$$

Hall's result evidently applies to $h_K$ and one derives easily from (1.2) that

$$
\sum_{\substack{n\leqslant x\\(n,K)=1}}1
\leqslant e^\gamma\frac{\phi(K)}Kx
\left(1+O\left(\frac{\log\log x}{\log x}\right)\right).
\tag{1.3}
$$

Now (1.3) is an upper sieve estimate, admittedly of a special kind, which has the remarkable feature of being best possible (apart from the error term) as reference to the prime number theorem shows; to put it in another way, the Selberg sieve applied to the sum on the left of (1.3) would lead to an estimate which is (essentially) *twice* that given on the right of (1.3) (cf. van Lint and Richert [6], or Halberstam and Richert [2], Chapter 3).

Such improvements of standard sieve estimates are potentially important, as will be illustrated in a simple sieve application in section 3. Therefore it is perhaps of interest to give a simpler and more transparent proof of Hall's inequality; this proof leads at the same time to a result which is more general in several respects. Moreover, Hall used the prime number theorem in his argument; this turns out to be unnecessary and we shall use instead (1.4) below, which may be considered as a (generalized) upper Čebyčev estimate.

**THEOREM 1.** *Let $h$ be a non-negative sub-multiplicative arithmetic function such that $h(1)=1$, satisfying also*

$$
\sum_{p\leqslant y}h(p)\log p
\leqslant\kappa y+O\left(\frac{y}{\log^2y}\right)
\qquad(y\geqslant2)
\tag{1.4}
$$

*for some constant $\kappa>0$, and*

$$
\sum_{\substack{p^r>y\\r\geqslant2}}
\frac{h(p^r)}{p^r}\log p^r
\ll\frac1{\log y}
\qquad(y\geqslant2).
\tag{1.5}
$$

*Let $z\geqslant2$ and define*

$$
P(z):=\prod_{p<z}p.
$$

## Page 78

*Then*

$$
\sum_{\substack{n\leqslant x\\(n,P(z))=1}}h(n)
\leqslant\kappa\frac{x}{\log x}m\left(\frac{x}{z},z\right)
+O\left(\frac{x,m(x,z)}{\log^2x}\right),
\tag{1.6}
$$

*where*

$$
m(x,z):=\sum_{\substack{n\leqslant x\\(n,P(z))=1}}\frac{h(n)}n.
$$

The $O$-constant in (1.6) depends at most on $\kappa$ and on the $O$-constants implied by (1.4) and (1.5).

If we put $z=2$ in Theorem 1, the condition $(n,P(z))=1$ becomes void, and we obtain as a special case

**THEOREM 2.** *Under the assumptions of Theorem 1 we have*

$$
\sum_{n\leqslant x}h(n)
\leqslant\kappa\frac{x}{\log x}
\left(1+O\left(\frac1{\log x}\right)\right)
\sum_{n\leqslant x}\frac{h(n)}n.
$$

The main feature of (1.6) is of course the reduction to $m(x,z)$, a function which can often be evaluated asymptotically (cf. also Levin and Fainleib [5]), as we shall demonstrate in one special case in section 4. However, it is immediate from (1.1) that

$$
\sum_{n\leqslant x}\frac{h(n)}n
\leqslant\prod_{p\leqslant x}
\left(1+\sum_{r=1}^\infty\frac{h(p^r)}{p^r}\right),
$$

and by a well-known result of Mertens

$$
\frac1{\log x}
=e^\gamma\prod_{p\leqslant x}\left(1-\frac1p\right)
\left(1+O\left(\frac1{\log x}\right)\right).
$$

Hence Theorem 2 implies (1.2) on taking $\kappa=1$, and the factor $\log\log x$ in the error term can be avoided, as had been conjectured (cf. [3]); in particular, we now obtain (1.3) in the improved form

$$
\sum_{\substack{n\leqslant x\\(n,K)=1}}1
\leqslant e^\gamma\frac{\phi(K)}Kx
\left(1+O\left(\frac1{\log x}\right)\right),
$$

where the $O$-constant is absolute.

Condition (1.4) requires that $h(p)$ is at most $\kappa$ on average; and it is easy to

## Page 79

verify that (1.5) holds (in even sharper form) if we impose the Wirsing condition

$$
h(p^r)\leqslant\gamma_1\gamma_2^r
\qquad(r=2,3,4,\ldots)
$$

where $\gamma_1,\gamma_2$ are constants satisfying $0\leqslant\gamma_1$, $0\leqslant\gamma_2<2$.

If one requires a result like (1.6) but one attaches no importance to the quality of the final error term one may replace the hypotheses (1.4) and (1.5) by

$$
\sum_{p\leqslant y}h(p)\log p
\leqslant\kappa y+O\left(\frac{y}{g(y)}\right),
$$

and

$$
\sum_{p,\,r\geqslant2}\frac{h(p^r)}{p^r}\log p^r<\infty,
$$

respectively, where $g(y)$ is a positive function tending to infinity with $y$ in such a way that

$$
\sum_l\frac1{l g(l)}<\infty.
$$

Then one derives, in the same way, (1.6) with $O(xm(x,z)/\log^2x)$ replaced by $o(xm(x,z)/\log x)$.

It would be interesting to know to what extend the conditions in both theorems can be weakened without affecting the outcome. Also, it would be both interesting and important, to derive corresponding results for arbitrary intervals of length $x$, and/or for arithmetic progressions, at some level of generality (cf. Hall's remarks on p. 348 of [3] concerning the twin primes problem and $\pi(x+y)-\pi(x)$). This has been underlined recently by the successful application of the sieve by Iwaniec and Jutila [4] to the location of primes in short intervals.

### 2. Proof of Theorem 1

Throughout the proof we indicate by $\sum'$ that the variables of summation have to be coprime with $P(z)$. Let

$$
M(x,z):=\sum_{\substack{n\leqslant x\\(n,P(z))=1}}h(n)
=\sum_{n\leqslant x}'h(n),
$$

and

$$
I(x,z):=\int_1^x\frac{M(t,z)}t\,dt
=\sum_{n\leqslant x}'h(n)\log\frac xn.
$$

## Page 80

We observe at once that

$$
M(x,z)+I(x,z)
=\sum_{n\leqslant x}'h(n)\left(\log\frac xn+1\right)
\leqslant\sum_{n\leqslant x}'h(n)\frac xn,
$$

so that

$$
M(x,z)+I(x,z)\leqslant x m(x,z),
$$

which implies both

$$
M(x,z)\leqslant x m(x,z),
\tag{2.1}
$$

and

$$
I(x,z)\leqslant x m(x,z);
\tag{2.2}
$$

and we remark at this stage also that $m(x,z)$ is monotonic increasing in $x$, a fact that will be used often in the argument below.

The proof depends on the identity

$$
\begin{aligned}
M(x,z)\log x
&=\sum_{n\leqslant x}'h(n)\log n
+\sum_{n\leqslant x}'h(n)\log\frac xn\\
&=\sum_{n\leqslant x}'h(n)\sum_{p^r\parallel n}\log p^r+I(x,z)\\
&=\Sigma(x,z)+I(x,z),
\end{aligned}
\tag{2.3}
$$

say. We begin by showing (cf. (1.6)) that

$$
M(x,z)\ll\frac{x}{\log x}m(x,z).
\tag{2.4}
$$

We have immediately that

$$
\Sigma(x,z)
=\sum_{\substack{p^rm\leqslant x\\(p,m)=1}}'h(p^rm)\log p^r
\leqslant\sum_{p^rm\leqslant x}'h(m)h(p^r)\log p^r
$$

by (1.1), so that

$$
\begin{aligned}
\Sigma(x,z)
\leqslant{}&\sum_{pn\leqslant x}'h(n)h(p)\log p
+\sum_{\substack{p^rn\leqslant x\\r\geqslant2}}'h(n)h(p^r)\log p^r\\
\leqslant{}&\sum_{n\leqslant x/z}'h(n)
\sum_{z\leqslant p\leqslant x/n}h(p)\log p
+\sum_{\substack{p^r\leqslant x\\r\geqslant2}}
h(p^r)\log p^r M\left(\frac{x}{p^r},z\right).
\end{aligned}
\tag{2.5}
$$

## Page 81

We now apply (1.4) in the more convenient equivalent form

$$
\sum_{p\leqslant y}h(p)\log p
\leqslant\kappa y
+O\left(\sum_{2\leqslant l\leqslant y}\frac1{\log^2l}\right)
\qquad(y\geqslant2);
$$

then

$$
\begin{aligned}
&\sum_{n\leqslant x/z}'h(n)
\sum_{z\leqslant p\leqslant x/n}h(p)\log p\\
&\qquad\leqslant\kappa x m\left(\frac{x}{z},z\right)
+O\left(\sum_{n\leqslant x/z}'h(n)
\sum_{2\leqslant l\leqslant x/n}\frac1{\log^2l}\right)\\
&\qquad\leqslant\kappa x m\left(\frac{x}{z},z\right)
+O\left(\sum_{2\leqslant l\leqslant x}
\frac{M(x/l,z)}{\log^2l}\right);
\end{aligned}
$$

and therefore, from (2.5),

$$
\begin{aligned}
\Sigma(x,z)\leqslant{}&\kappa x m\left(\frac{x}{z},z\right)
+O\left(\sum_{2\leqslant l\leqslant x}\frac{M(x/l,z)}{\log^2l}\right)\\
&+\sum_{\substack{p^r\leqslant x\\r\geqslant2}}
h(p^r)\log p^r M\left(\frac{x}{p^r},z\right).
\end{aligned}
\tag{2.6}
$$

If now we apply the trivial bound (2.1) we have

$$
\begin{aligned}
\Sigma(x,z)\leqslant{}&\kappa x m(x,z)
+O\left(x\sum_{2\leqslant l\leqslant x}
\frac{m(x/l,z)}{l\log^2l}\right)\\
&+x\sum_{\substack{p^r\leqslant x\\r\geqslant2}}
\frac{h(p^r)\log p^r}{p^r}
m\left(\frac{x}{p^r},z\right)
\end{aligned}
$$

and, since $m(y,z)$ is monotonic increasing in $y$,

$$
\Sigma(x,z)
\leqslant x m(x,z)
\left(\kappa+O(1)
+\sum_{p,\,r\geqslant2}\frac{h(p^r)}{p^r}\log p^r\right)
\ll x m(x,z),
\tag{2.7}
$$

provided only that

$$
\sum_{p,\,r\geqslant2}\frac{h(p^r)}{p^r}\log p^r<\infty,
$$

which certainly is implied by (1.5). Now (2.3) with (2.7) and (2.2) proves (2.4).

## Page 82

We are able to complete the proof of the theorem on the basis of (2.3) and (2.4). First of all, by (2.4)

$$
I(x,z)\ll\int_1^x\frac{m(t,z)}{\log(2t)}\,dt
\ll m(x,z)\frac{x}{\log x}.
$$

Hence, by (2.3),

$$
M(x,z)=\frac{\Sigma(x,z)}{\log x}
+O\left(\frac{x m(x,z)}{\log^2x}\right).
\tag{2.8}
$$

We deal with $\Sigma(x,z)$ on the basis of (2.6). Take first the $O$-term. We have, by (2.4) and (2.1) (in that order) that

$$
\begin{aligned}
\sum_{2\leqslant l\leqslant x}\frac{M(x/l,z)}{\log^2l}
&=\left(\sum_{2\leqslant l\leqslant x^{1/2}}
+\sum_{x^{1/2}<l\leqslant x}\right)
\frac{M(x/l,z)}{\log^2l}\\
&\ll\frac{x m(x,z)}{\log x}
\sum_{2\leqslant l\leqslant x^{1/2}}\frac1{l\log^2l}
+x m(x,z)\sum_{l>x^{1/2}}\frac1{l\log^2l}\\
&\ll\frac{x m(x,z)}{\log x}.
\end{aligned}
\tag{2.9}
$$

Finally, the last expression on the right of (2.6) is at most

$$
\begin{aligned}
&\left(
\sum_{\substack{p^r\leqslant x^{1/2}\\r\geqslant2}}
+\sum_{\substack{x^{1/2}<p^r\leqslant x\\r\geqslant2}}
\right)
h(p^r)\log p^r M\left(\frac{x}{p^r},z\right)\\
&\qquad\ll\frac{x m(x,z)}{\log x}
\sum_{\substack{p^r\leqslant x^{1/2}\\r\geqslant2}}
\frac{h(p^r)}{p^r}\log p^r
+x m(x,z)
\sum_{\substack{p^r>x^{1/2}\\r\geqslant2}}
\frac{h(p^r)}{p^r}\log p^r\\
&\qquad\ll\frac{x m(x,z)}{\log x};
\end{aligned}
\tag{2.10}
$$

on the way we have used once more first (2.4), then (2.1) and, at the last stage, (1.5). Hence, from (2.6), (2.9) and (2.10),

$$
\Sigma(x,z)
\leqslant\kappa x m\left(\frac{x}{z},z\right)
+O\left(\frac{x m(x,z)}{\log x}\right),
$$

and Theorem 1 now follows from (2.8).
