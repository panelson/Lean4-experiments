The smallest non-modular lattice is the **pentagon lattice**, denoted as \( N_5 \). It is a 5-element lattice with the following structure:

---

### Structure of \( N_5 \)
The elements of \( N_5 \) are typically labeled as \( \{0, a, b, c, 1\} \), where:
- \( 0 \) is the least element (bottom),
- \( 1 \) is the greatest element (top),
- The relations are:
  \(0 < a < b < 1, \quad 0 < c < 1, \quad \text{and } a \nleq c, \quad c \nleq b.\)

The Hasse diagram of \( N_5 \) looks like this:

```
      1
     / \
    b   c
    |   |
    a   |
     \ /
      0
```

---

### Why \( N_5 \) is Non-Modular
The lattice \( N_5 \) violates the **modular law**, which states that for all \( x, y, z \) in a lattice:
$$
\text{If } x \leq z, \text{ then } x \lor (y \land z) = (x \lor y) \land z.
$$

In \( N_5 \), let \( x = a \), \( y = c \), and \( z = b \). Then:
- \( x \leq z \) because \( a \leq b \),
- \( x \lor (y \land z) = a \lor (c \land b) = a \lor 0 = a \),
- \( (x \lor y) \land z = (a \lor c) \land b = 1 \land b = b \).

Since \( a \neq b \), the modular law fails, and \( N_5 \) is non-modular.

---

### Minimality of \( N_5 \)
\( N_5 \) is the **smallest non-modular lattice** because:
1. Any lattice with fewer than 5 elements is modular.
2. \( N_5 \) is the smallest lattice that violates the modular law.

---

### Importance of \( N_5 \)
- \( N_5 \) plays a central role in lattice theory because it characterizes non-modularity: a lattice is modular if and only if it does not contain a sublattice isomorphic to \( N_5 \).
- It is one of the two critical lattices in the **Dedekind-Birkhoff theorem**, which states that a lattice is modular if and only if it does not contain \( N_5 \) or the **diamond lattice \( M_3 \)** as a sublattice.

---

### Summary
The smallest non-modular lattice is the **pentagon lattice \( N_5 \)**. It has 5 elements and is the minimal lattice that violates the modular law. Its structure and properties are fundamental in the study of modular and non-modular lattices.