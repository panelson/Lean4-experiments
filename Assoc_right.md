
Axiom: $\forall u x y z w \in S, R x y u \text{ and } R u z w \implies \exists v \in S, R x v w \text{ and } R y z v$

Lemma: $\forall x, x^{-1-1}=x$

Lemma: $\forall u x y z w \in S, R x v w \text{ and } R y z v \implies \exists u \in S, R x y u \text{ and } R u z w$

Proof: 

> Assume $u, x, y, z, w \in S$.

> Assume $R x v w$ and $R y z v$.

> $R v^{-1} x^{-1} w^{-1}$ by Pierce3 applied to $R x v w$.

> $R z^{-1} y^{-1} v^{-1}$ by Pierce3 applied to $R y z v$.

> $R z^{-1} y^{-1} v^{-1}$ and $R v^{-1} x^{-1} w^{-1}$ by conjunction.

> $\exists t \in S, R z^{-1} t w^{-1} \text{ and } R y^{-1} x^{-1} t$ by Axiom with $v^{-1} z^{-1} y^{-1} x^{-1} w^{-1}$.

>> Consider $c \in S$ such that $R z^{-1} c w^{-1}$ and $R y^{-1} x^{-1} c$.

>> $R c^{-1} z w$ by Pierce3 and $x^{-1-1}=x$.

>> $R x y c^{-1}$ by Pierce3 and $x^{-1-1}=x$.

> $\exists u \in S, R x y u \text{ and } R u z w$ by $\exists$-introduction with $u=c^{-1}$.


Proposition 16.8. Let $R$ be a ring. Then for all $x,y\in R$,
1. $x0 = 0x = 0$
2. $x(-y) = (-x)y = -xy$
3. $(-x)(-y) = xy$

Proof: Assume $R$ is a ring and let $x,y\in R$.

1. $x0=x0+0$ ................... since $0$ is the additive identity
>>>> $=x0+(x0+-x0)$ .. since $-x0$ is the inverse of $x0$

>>>> $=(x0+x0)+-x0$ .. by assoc. of $+$

>>>> $=x(0+0)+-x0$ ... by left distributivity

>>>> $=x0+-x0$ ............ since $0+0=0$

>>>> $=0$



