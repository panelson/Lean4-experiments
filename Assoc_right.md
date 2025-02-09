
Axiom: $\forall u x y z w \in S, R x y u \text{ and } R u z w \implies \exists v \in S, R x v w \text{ and } R y z v$


Lemma: $\forall u x y z w \in S, R x v w \text{ and } R y z v \implies \exists u \in S, R x y u \text{ and } R u z w$

Proof: 

> Assume $u, x, y, z, w \in S$.

> Assume $R x v w$ and $R y z v$.

> $R v⁻¹ x⁻¹ w⁻¹$ by Pierce3 applied to $R x v w$.

> $R z⁻¹ y⁻¹ v⁻¹$ by Pierce3 applied to $R y z v$.

> $R z⁻¹ y⁻¹ v⁻¹$ and $R v⁻¹ x⁻¹ w⁻¹$ by conjunction.

> $\exists t \in S, R z⁻¹ t w⁻¹ \text{ and } R y⁻¹ x⁻¹ t by Axiom with v⁻¹ z⁻¹ y⁻¹ x⁻¹ w⁻¹

>> Consider $c \in S$ such that $R z⁻¹ c w⁻¹$ and $R y⁻¹ x⁻¹ c$.

>> $R c⁻¹ z w$ by Pierce3 and $x⁻¹⁻¹=x$.

>> $R x y c⁻¹$ by Pierce3 and $x⁻¹⁻¹=x$.

> $\exists u \in S, R x y u \text{ and } R u z w$ by $\exists$-introduction with $u=c⁻¹$.

